-module(om_parse).
-export([expr/2, ret/1, print/2]).
-define(arr(F), (F == lambda orelse F == pi)).
-define(noh(F), (F /= '$'   andalso F /= ':')).
-define(nah(F,C),  (?noh(C) andalso ?noh(F))).

expr(L, S) ->
    case expr(S, L, [], {0,0}) of
        {error, R}  -> erlang:error({parse_error, R});
        {{_,_}, A}  -> ret({ok, A})
    end.

ret({_,[X]}) -> X;
ret(Y) -> Y.

expr(P,[],                 [{':',X}],{V,D}) -> {error,wrong_function};
expr(P,[],                         A,{V,D}) -> rewind(A,{V,D},[]);
expr(P,[close                 |T], A,{V,D}) -> case rewind(A,{D,D},[]) of
                                                    {error,R} -> {error,R};
                                                    {{V1,D1},A1} -> expr(P,T,A1,{V1,D1}) end;

expr(P,[F,open,{var,L},colon  |T], Acc, {V,D}) when ?arr(F)   -> expr(P,T,[{'$',{func(F),L}}|Acc],{V,D+1});
expr(P,[{remote,L}|T],  [{C,Y}|Acc],{V,D}) when ?noh(C)       -> expr(P,T,[{app,{{C,Y},{remote,L}}}|Acc],{V,D});
expr(P,[{remote,L}             |T], Acc, {V,D})                -> expr(P,T,[{remote,L}|Acc],{V,D});
expr(P,[{N,X}|T],           [{C,Y}|Acc],{V,D}) when ?nah(N,C) -> expr(P,T,[{app,{{C,Y},{N,X}}}|Acc],{V,D});
expr(P,[{N,X}                  |T], Acc, {V,D}) when ?noh(N)  -> expr(P,T,[{N,X}|Acc],{V,D});
expr(P,[open                   |T], Acc, {V,D})                -> expr(P,T,[{open}|Acc],{V,D+1});
expr(P,[box                    |T], Acc, {V,D})                -> expr(P,T,[{star,2}|Acc],{V,D});
expr(P,[arrow                  |T], Acc, {V,D})                -> expr(P,T,[{arrow}|Acc],{V,D});
expr(P,[X                      |T], Acc, {V,D})                -> {error, {bad_token, X}}.

rewind([],                      {V,D},       R)  -> {{V,D},flat(R)};
rewind([{':',_}|_]=A,           {V,D},       R)  -> {{V,D},flat([R|A])};
rewind([{'$',M}|A],             {V,D},[{C,X}|R]) -> rewind([{':',{M,{C,X}}}|A],{V,D},R);
rewind([{arrow},{':',{M,I}} |A],{V,D},[{C,X}|R]) -> rewind([{M,{I,{C,X}}}|A],{V,D},R);
rewind([{arrow},{B,Y}       |A],{V,D},[{C,X}|R]) -> rewind([{func(arrow),{{B,Y},{C,X}}}|A],{V,D},R);
rewind([{C,X},{'$',M}|A],{V,D},R) when V == D    -> rewind([{':',{M,{C,X}}}|A],{V,D},R);
rewind([{C,X},{'$',M}|_]=A,          {V,D},  R)  -> {{V,D},  flat([A|R])};
rewind([{C,X},{open},{':',{M,I}} |A],{V,D},  R)  -> {{V,D-1},flat([{C,X},{':',{M,I}}  |[R|A]])};
rewind([{C,X},{open},{'$',M}     |A],{V,D},  R)  -> {{V,D-1},flat([{C,X},{'$',M}      |[R|A]])};
rewind([{C,X},{open},{open}      |A],{V,D},  R)  -> {{V,D-1},flat([{C,X},{open}        |[R|A]])};
rewind([{C,X},{open},{B,Y}       |A],{V,D},  R)  -> {{V,D-1},flat([{app,{{B,Y},{C,X}}}|[R|A]])};
rewind([{C,X},{open}|A],{V,D},               R)  -> {{V,D-1},flat([{C,X}|[R|A]])};
rewind([{C,X},{arrow},{':',{M,I}}|A],{V,D},  R)  -> rewind([{M,{I,{C,X}}}|A],{V,D},R);
rewind([{C,X},{arrow},{B,Y} |A],{V,D},       R)  -> rewind([{func(arrow),{{B,Y},{C,X}}}|A],{V,D},R);
rewind([{C,X},{B,Y}|A], {V,D}, R) when ?nah(C,B) -> rewind([{app,{{B,Y},{C,X}}}|A],{V,D},R);
rewind([{C,X}]=A,         {V,D}, R) when ?noh(C) -> {{V,D},flat([R|A])};
rewind(A,                 {V,D}, R)               -> {error, A}.

flat(X) -> lists:flatten(X).

func(lambda) -> "λ";
func(pi)     -> "∀";
func(arrow)  -> "→";
func(Sym)    -> Sym.

print(any,D)                    -> "any";
print(none,D)                   -> "none";
print({remote,L},D)             -> ["#", L];
print({var,{N,0}},D)            -> [atom_to_list(N)];
print({var,{N,I}},D)            -> [atom_to_list(N), "@", integer_to_list(I)];
print({star,2},D)               -> "[]";
print({star,N},D)               -> ["*", integer_to_list(N)];
print({"→",{I,O}},D)            -> ["(", print(I,D+1), " → ", print(O,D), ")"];
print({app,{I,O}},D)            -> ["(", print(I,D), " ", print(O,D), ")"];
print({{"∀",{N,_}},{any,O}},D)  -> ["(∀ ", atom_to_list(N), " → ", print(O,D), ")"];
print({{"∀",{N,_}},{I,O}},D)    -> ["(∀ (", atom_to_list(N), ": ", print(I,D+1), ") → ", print(O,D), ")"];
print({{"λ",{N,_}},{any,O}},D)  -> ["(λ ", atom_to_list(N), " → ", print(O,D), ")"];
print({{"λ",{N,_}},{I,O}},D)    -> ["(λ (", atom_to_list(N), ": ", print(I,D+1), ") → ", print(O,D), ")"].
