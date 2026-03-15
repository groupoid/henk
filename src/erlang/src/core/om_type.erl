-module(om_type).
-export([type/2, type/3, type_s/2, norm/1, norm/2, eq/2, subst/3, shift/3, star/1, func/1, var/2, hierarchy/2]).

hierarchy(_Arg, Out) -> Out.

star({star,N}) -> N;
star(S)        -> erlang:error({error, "*", S}).

func({{"∀",_},{_,_}}) -> true;
func(T)               -> erlang:error({error, "∀", T}).

var(N,D) -> case proplists:is_defined(N,D) of
    true  -> true;
    false -> erlang:error({error, "free var", N, proplists:get_keys(D)})
end.

shift({var,{N,I}},N,P) when I>=P -> {var,{N,I+1}};
shift({{"∀",{N,0}},{I,O}},N,P)   -> {{"∀",{N,0}},{shift(I,N,P),shift(O,N,P+1)}};
shift({{"λ",{N,0}},{I,O}},N,P)   -> {{"λ",{N,0}},{shift(I,N,P),shift(O,N,P+1)}};
shift({Q,{L,R}},N,P)             -> {Q,{shift(L,N,P),shift(R,N,P)}};
shift(T,_N,_P)                   -> T.

subst(Term,Name,Value)            -> subst(Term,Name,Value,0).
subst({"→",        {I,O}},N,V,L) -> {"→",        {subst(I,N,V,L),subst(O,N,V,L)}};
subst({{"∀",{N,0}},{I,O}},N,V,L) -> {{"∀",{N,0}},{subst(I,N,V,L),subst(O,N,shift(V,N,0),L+1)}};
subst({{"∀",{F,X}},{I,O}},N,V,L) -> {{"∀",{F,X}},{subst(I,N,V,L),subst(O,N,shift(V,F,0),L)}};
subst({{"λ",{N,0}},{I,O}},N,V,L) -> {{"λ",{N,0}},{subst(I,N,V,L),subst(O,N,shift(V,N,0),L+1)}};
subst({{"λ",{F,X}},{I,O}},N,V,L) -> {{"λ",{F,X}},{subst(I,N,V,L),subst(O,N,shift(V,F,0),L)}};
subst({app, {F,A}},       N,V,L) -> {app,        {subst(F,N,V,L),subst(A,N,V,L)}};
subst({var, {N,L}},       N,V,L) -> V;
subst({var, {N,I}},       N,V,L) when I>L -> {var, {N,I-1}};
subst(T,       _,_,_)            -> T.

%% Stateless norm (used by om_erase internally)
norm(none)                          -> none;
norm(any)                           -> any;
norm({"→",        {I,O}})           -> {{"∀",{'_',0}},{norm(I),norm(O)}};
norm({{"∀",{N,0}},{I,O}})           -> {{"∀",{N,0}},  {norm(I),norm(O)}};
norm({{"λ",{N,0}},{I,O}})           -> {{"λ",{N,0}},  {norm(I),norm(O)}};
norm({app,{F,A}})                   -> case norm(F) of
                                            {{"λ",{N,0}},{_,O}} -> norm(subst(O,N,A));
                                                              NF -> {app,{NF,norm(A)}} end;
norm({remote,N})                    ->
    File = om_repl:name(N),
    Ast  = om_parse:expr(om_tok:tokens(om_repl:read(File), 0), 0),
    norm(Ast);
norm(T)                             -> T.

%% State-passing norm/2
norm(T, S) ->
    case T of
        {app, {F, A}} ->
            {NF, S1} = norm(F, S),
            case NF of
                {{"λ",{N,0}}, {_, O}} -> norm(subst(O, N, A), S1);
                _                     -> {NA, S2} = norm(A, S1), {{app,{NF,NA}}, S2}
            end;
        {remote, N} -> om_state:cache(norm, N, S);
        {"→", {I, O}} ->
            {NI, S1} = norm(I, S), {NO, S2} = norm(O, S1),
            {{{"∀",{'_',0}},{NI,NO}}, S2};
        {{"∀",{N,0}}, {I, O}} ->
            {NI, S1} = norm(I, S), {NO, S2} = norm(O, S1),
            {{{"∀",{N,0}},{NI,NO}}, S2};
        {{"λ",{N,0}}, {I, O}} ->
            {NI, S1} = norm(I, S), {NO, S2} = norm(O, S1),
            {{{"λ",{N,0}},{NI,NO}}, S2};
        _ -> {T, S}
    end.

eq({{"∀",{"_",0}},X},{"→",Y})                    -> eq(X,Y);
eq({{"∀",{N1,0}},{I1,O1}},{{"∀",{N2,0}},{I2,O2}}) -> eq(I1,I2), eq(O1,subst(shift(O2,N1,0),N2,{var,{N1,0}},0));
eq({{"λ",{N1,0}},{I1,O1}},{{"λ",{N2,0}},{I2,O2}}) -> eq(I1,I2), eq(O1,subst(shift(O2,N1,0),N2,{var,{N1,0}},0));
eq({app,{F1,A1}},{app,{F2,A2}})                   -> eq(F1,F2), eq(A1,A2);
eq({star,N},{star,N})                             -> true;
eq({var,{N,I}},{var,{N,I}})                       -> true;
eq({remote,N},{remote,N})                         -> true;
eq(A,B)                                           -> erlang:error({error, "==", A, B}).

%% State-passing type
type(T, S) -> type(T, [], S).

type({star,N},_,S)              -> {{star,N+1}, S};
type({var,{N,_}},D,S)          -> true = var(N,D), {proplists:get_value(N,D), S};
type({remote,N},_,S)           -> om_state:cache(type, N, S);
type({"→",{I,O}},D,S)          ->
    TI = type_s(I,D), TO = type_s(O,D),
    {{star,hierarchy(star(TI),star(TO))}, S};
type({{"∀",{N,0}},{I,O}},D,S)  ->
    TI = type_s(I,D), NI = norm(I),
    TO = type_s(O,[{N,NI}|D]),
    {{star,hierarchy(star(TI),star(TO))}, S};
type({{"λ",{N,0}},{I,O}},D,S)  ->
    _ = star(type_s(I,D)),
    NI = norm(I),
    {TO, S1} = type(O,[{N,NI}|D],S),
    {{{"∀",{N,0}},{NI,TO}}, S1};
type({app,{F,A}},D,S)          ->
    {TF, S1} = type(F,D,S), TFN = norm(TF),
    {{"∀",{N,0}},{I,O}} = TFN,
    TA = type_s(A,D), true = eq(I,TA),
    norm(subst(O,N,A), S1).

%% Stateless type (matches original om_type:type/2 — remote terms fetch directly)
type_s({star,N},_)             -> {star,N+1};
type_s({var,{N,_}},D)         -> true = var(N,D), proplists:get_value(N,D);
type_s({remote,N},D)          ->
    File = om_repl:name(N),
    Ast  = om_parse:expr(om_tok:tokens(om_repl:read(File), 0), 0),
    type_s(Ast, D);
type_s({"→",{I,O}},D)         -> {star,hierarchy(star(type_s(I,D)),star(type_s(O,D)))};
type_s({{"∀",{N,0}},{I,O}},D) -> {star,hierarchy(star(type_s(I,D)),star(type_s(O,[{N,norm(I)}|D])))};
type_s({{"λ",{N,0}},{I,O}},D) -> _ = star(type_s(I,D)), NI = norm(I), {{"∀",{N,0}},{NI,type_s(O,[{N,NI}|D])}};
type_s({app,{F,A}},D)         ->
    TF = type_s(F,D), TFN = norm(TF),
    {{"∀",{N,0}},{I,O}} = TFN,
    TA = type_s(A,D), true = eq(I,TA),
    norm(subst(O,N,A)).
