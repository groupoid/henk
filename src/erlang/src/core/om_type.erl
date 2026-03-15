-module(om_type).
-export([type/2, type/3, norm/2, eq/3, subst/3, shift/3, bind/3]).

norm(T, S) ->
    case T of
        {app, {F, A}} -> 
            {NF, S1} = norm(F, S),
            case NF of 
                {{<<206,187>>, N}, {_, O}} -> norm(subst(O, N, A), S1); 
                _ -> {NormA, S2} = norm(A, S1), {{app, {NF, NormA}}, S2} 
            end;
        {remote, N} -> om_state:cache(norm, N, S);
        {<<226,134,146>>, {I, O}} -> 
            {NI, S1} = norm(I, S), {NO, S2} = norm(O, S1),
            {{{<<226,136,128>>, {'_', 0}}, {NI, NO}}, S2};
        {{Q, N}, {A, B}} when Q==<<226,136,128>>; Q==<<206,187>> -> 
            {NA, S1} = norm(A, S), {NB, S2} = norm(B, S1),
            {{{Q, N}, {NA, NB}}, S2};
        _ -> {T, S}
    end.

eq(A, B, S) ->
    case {A, B} of
        {{{<<226,136,128>>, {"_", 0}}, X}, {<<226,134,146>>, Y}} -> eq(X, Y, S);
        {{{Q, N1}, {I1, O1}}, {{Q, N2}, {I2, O2}}} when Q==<<226,136,128>>; Q==<<206,187>> -> eq(I1, I2, S), eq(O1, subst(shift(O2, N1, 0), N2, {var, N1}), S);
        {{app, {F1, A1}}, {app, {F2, A2}}} -> eq(F1, F2, S), eq(A1, A2, S);
        {{star, N}, {star, N}} -> S;
        {{var, V}, {var, V}} -> S;
        {{remote, R}, {remote, R}} -> S;
        _ -> erlang:error({error, "==", A, B})
    end.

type(T, S) -> {R, S1} = type(T, [], S), {R, S1}.

type({star, N}, _, S) -> {{star, N+1}, S};
type({var, V}, D, S) -> 
    case lists:keyfind(V, 1, D) of
        {V, T} -> {T, S};
        _ -> erlang:error({var, V})
    end;
type({remote, N}, _, S) -> om_state:cache(type, N, S);
type({<<226,134,146>>, {I, O}}, D, S) -> 
    {{star, N1}, S1} = type(I, D, S), {{star, N2}, S2} = type(O, D, S1),
    {{star, pts(N1, N2)}, S2};
type({{<<226,136,128>>, N}, {I, O}}, D, S) ->
    {{star, N1}, S1} = type(I, D, S), {NI, S2} = norm(I, S1),
    {{star, N2}, S3} = type(O, bind(N, NI, D), S2),
    {{star, pts(N1, N2)}, S3};
type({{<<206,187>>, N}, {I, O}}, D, S) ->
    {{star, _}, S1} = type(I, D, S), {NI, S2} = norm(I, S1),
    {TO, S3} = type(O, bind(N, NI, D), S2),
    {{{<<226,136,128>>, N}, {NI, TO}}, S3};
type({app, {F, A}}, D, S) ->
    {TF, S1} = type(F, D, S), {TypeF, S1A} = norm(TF, S1),
    {{<<226,136,128>>, N}, {In, O}} = TypeF,
    {TA, S2} = type(A, D, S1A), eq(In, TA, S2),
    norm(subst(O, N, A), S2).

pts(N, N) -> N;
pts(2, 1) -> 1;
pts(N1, N2) -> erlang:max(N1, N2).

bind({Name, _}, Type, D) ->
    D1 = [{{N, I+1}, T} || {{N, I}, T} <- D, N == Name] ++ [{{N, I}, T} || {{N, I}, T} <- D, N /= Name],
    [{{Name, 0}, Type} | D1].

subst(T, N, V) -> subst(T, N, V, 0).
subst({var, V}, V, Val, 0) -> Val;
subst({var, {Name, I}}, {Name, _}, _, L) when I > L -> {var, {Name, I-1}};
subst({{Q, N}, {I, O}}, Var, Val, L) when Q==<<226,136,128>>; Q==<<206,187>> ->
    case N of
        Var -> {{Q, N}, {subst(I, Var, Val, L), subst(O, Var, shift(Val, Var, 0), L+1)}};
        _   -> {{Q, N}, {subst(I, Var, Val, L), subst(O, Var, shift(Val, N, 0), L)}}
    end;
subst({app, {F, A}}, N, V, L) -> {app, {subst(F, N, V, L), subst(A, N, V, L)}};
subst({Binary, {I, O}}, N, V, L) when is_binary(Binary) -> {Binary, {subst(I, N, V, L), subst(O, N, V, L)}};
subst(T, _, _, _) -> T.

shift({var, {Name, I}}, {Name, _}, P) when I >= P -> {var, {Name, I+1}};
shift({{Q, N}, {I, O}}, Var, P) when Q==<<226,136,128>>; Q==<<206,187>> ->
    case N of
        Var -> {{Q, N}, {shift(I, Var, P), shift(O, Var, P+1)}};
        _   -> {{Q, N}, {shift(I, Var, P), shift(O, Var, P)}}
    end;
shift({app, {L, R}}, Var, P) -> {app, {shift(L, Var, P), shift(R, Var, P)}};
shift({Binary, {I, O}}, Var, P) when is_binary(Binary) -> {Binary, {shift(I, Var, P), shift(O, Var, P)}};
shift(T, _, _) -> T.
