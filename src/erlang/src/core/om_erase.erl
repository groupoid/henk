-module(om_erase).
-export([erase/2, erase/3]).
-import(om_type,[type_s/2,star/1,norm/1,eq/2,subst/3,func/1,hierarchy/2,var/2]).

univ({star,_})         -> true;
univ({{"∀",_},{_,O}})  -> univ(O);
univ(_)                -> false.

%% erase_s/2 — pure stateless eraser (direct port of original)
%% On remote terms: load, parse and erase directly (no state needed)
erase_s({remote,N}, D) ->
    File = om_repl:name(N),
    Ast  = om_parse:expr(om_tok:tokens(om_repl:read(File), 0), 0),
    erase_s(Ast, D);
erase_s({star,N}, _)              -> {none, {star,N+1}};
erase_s({var,{N,I}}, D)          ->
    true = var(N,D),
    T = proplists:get_value(N,D),
    case univ(T) of
        true  -> {none, T};
        false -> {{var,{N,I}}, T}
    end;
erase_s({"→",{I,O}}, D)          ->
    {none, {star, hierarchy(star(type_s(I,D)), star(type_s(O,D)))}};
erase_s({{"∀",{N,0}},{I,O}}, D)  ->
    {none, {star, hierarchy(star(type_s(I,D)), star(type_s(O,[{N,norm(I)}|D])))}};
erase_s({{"λ",{N,0}},{I,O}}, D)  ->
    _ = star(type_s(I,D)),
    NI = norm(I),
    {B1, S1} = erase_s(O, [{N,NI}|D]),
    T = {{"∀",{N,0}},{NI,S1}},
    case univ(NI) of
        true  -> {B1, T};
        false -> {{{"λ",{N,0}},{any,B1}}, T}
    end;
erase_s({app,{F,A}}, D)          ->
    {B1, _S1} = erase_s(F, D),
    {B2,  S2} = erase_s(A, D),
    try
        S1T = norm(type_s(F, D)),
        true = func(S1T),
        {{"∀",{N,0}},{_I,O}} = S1T,
        T = norm(subst(O,N,A)),
        case univ(S1T) of
            true  -> {none, T};
            false -> case univ(norm(S2)) of
                true  -> {B1, T};
                false -> {{app,{B1,B2}}, T}
            end
        end
    catch _:_ ->
        {{app,{B1,B2}}, S2}
    end.

%% erase/2 — stateless entry (for direct calls)
erase(T, D) -> erase_s(T, D).

%% erase/3 — state-passing (for om_extract and om_state:cache)
erase({remote,N}, _, S) -> om_state:cache(erased, N, S);
erase(T, D, S) ->
    {erase_s(T, D), S}.
