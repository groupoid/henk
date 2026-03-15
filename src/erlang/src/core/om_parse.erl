-module(om_parse).
-export([expr/2, print/1]).

expr(L, S) -> 
    {_, _, R} = expr(L, S, [], {0,0}),
    case R of
        [Term|_] -> Term;
        _ -> erlang:error({parse_error, R})
    end.

expr([], _, A, {V,D}) -> rewind(A, {V,D}, []);
expr([close|T], S, A, {_,D}) -> {V1,D1,A1} = rewind(A, {D,D}, []), expr(T, S, A1, {V1,D1});
expr([F,open,{var,{N,I}},colon|T], S, Acc, {V,D}) when F==lambda; F==pi -> 
    expr(T, S, [{'$', {func(F), {N,I}}}|Acc], {V,D+1});
expr([F,{var,{N,I}},colon|T], S, Acc, {V,D}) when F==lambda; F==pi -> 
    expr(T, S, [{'$', {func(F), {N,I}}}|Acc], {V,D});
expr([{remote,L}|T], S, [{C,Y}|Acc], {V,D}) when C/='$', C/=':' -> expr(T, S, [{app,{{C,Y},{remote,L}}}|Acc], {V,D});
expr([{remote,L}|T], S, Acc, {V,D}) -> expr(T, S, [{remote,L}|Acc], {V,D});
expr([{N,X}|T], S, [{C,Y}|Acc], {V,D}) when N/='$', N/=':', C/='$', C/=':' -> expr(T, S, [{app,{{C,Y},{N,X}}}|Acc], {V,D});
expr([{N,X}|T], S, Acc, {V,D}) when N/='$', N/=':' -> expr(T, S, [{N,X}|Acc], {V,D});
expr([open|T], S, Acc, {V,D}) -> expr(T, S, [open|Acc], {V,D+1});
expr([box|T], S, Acc, {V,D}) -> expr(T, S, [{star,2}|Acc], {V,D});
expr([arrow|T], S, Acc, {V,D}) -> expr(T, S, [arrow|Acc], {V,D});
expr([X|T], _, _, _) -> 
    erlang:error({token_error, X}).

rewind([], {V,D}, R) -> {V,D,R};
rewind([{':',_}|_]=A, {V,D}, R) -> {V,D,A++R};
rewind([{'$',M}|A], {V,D}, [{C,X}|R]) -> rewind([{':',{M,{C,X}}}|A], {V,D}, R);
rewind([arrow, {':',{M,I}}|A], {V,D}, [{C,X}|R]) -> rewind([{M,{I,{C,X}}}|A], {V,D}, R);
rewind([arrow, {B,Y}|A], {V,D}, [{C,X}|R]) -> rewind([{func(arrow),{{B,Y},{C,X}}}|A], {V,D}, R);
rewind([{C,X}, {'$',M}|A], {V,D}, R) when V==D -> rewind([{':',{M,{C,X}}}|A], {V,D}, R);
rewind([{C,X}, open, {':',{M,I}}|A], {V,D}, R) -> {V,D-1, [{C,X}, {':',{M,I}}|R]++A};
rewind([{C,X}, open, {'$',M}|A], {V,D}, R) -> {V,D-1, [{C,X}, {'$',M}|R]++A};
rewind([{C,X}, open, open|A], {V,D}, R) -> {V,D-1, [{C,X}, open|R]++A};
rewind([{C,X}, open, {B,Y}|A], {V,D}, R) -> {V,D-1, [{app,{{B,Y},{C,X}}}|R]++A};
rewind([{C,X}, open|A], {V,D}, R) -> {V,D-1, [{C,X}|R]++A};
rewind([{C,X}, arrow, {':',{M,I}}|A], {V,D}, R) -> rewind([{M, {I, {C,X}}}|A], {V,D}, R);
rewind([{C,X}, arrow, {B,Y}|A], {V,D}, R) -> rewind([{func(arrow), {{B,Y},{C,X}}}|A], {V,D}, R);
rewind([{C,X}, {B,Y}|A], {V,D}, R) when C/='$', C/=':', B/='$', B/=':' -> rewind([{app, {{B,Y},{C,X}}}|A], {V,D}, R);
rewind([A], {V,D}, R) -> {V,D, [A|R]};
rewind(A, _, _) -> {error, A}.

print(any) -> "any";
print(none) -> "none";
print({remote, L}) -> ["#", L];
print({var, {N, 0}}) -> [atom_to_list(N)];
print({var, {N, I}}) -> [atom_to_list(N), "@", integer_to_list(I)];
print({star, 2}) -> "[]";
print({star, N}) -> ["*", integer_to_list(N)];
print({<<226,134,146>>, {I, O}}) -> ["(", print(I), " -> ", print(O), ")"];
print({app, {I, O}}) -> ["(", print(I), " ", print(O), ")"];
print({{<<226,136,128>>, {N, _}}, {any, O}}) -> ["(@ ", atom_to_list(N), " -> ", print(O), ")"];
print({{<<226,136,128>>, {N, _}}, {I, O}}) -> ["(@ (", atom_to_list(N), ": ", print(I), ") -> ", print(O), ")"];
print({{<<206,187>>, {N, _}}, {any, O}}) -> ["(\\ ", atom_to_list(N), " -> ", print(O), ")"];
print({{<<206,187>>, {N, _}}, {I, O}}) -> ["(\\ (", atom_to_list(N), ": ", print(I), ") -> ", print(O), ")"].

func(lambda) -> <<206,187>>; func(pi) -> <<226,136,128>>; func(arrow) -> <<226,134,146>>; func(X) -> X.
