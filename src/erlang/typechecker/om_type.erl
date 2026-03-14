-module(om_type).
-description('Type Checker').
-export([type/2, star/1, var/2, func/1, shift/3, subst/3, norm/1, eq/2, dep/3, hierarchy/2]).

dep(_Arg,Out,impredicative) -> Out;
dep(Arg,Out,predicative)   -> erlang:max(Arg,Out).

hierarchy(Arg,Out)         -> dep(Arg,Out,application:get_env(om,hierarchy,impredicative)).

star({star,N})          -> N;
star(S)                 -> erlang:error({error, "*", S}).

func({{<<"∀"/utf8>>,_},{_,_}})   -> true;
func(T)                 -> erlang:error({error, <<"∀"/utf8>>, T }).

var(N,B)                -> var(N,B,proplists:is_defined(N,B)).
var(_,_,true)           -> true;
var(N,B,false)          -> erlang:error({error, "free var", N, proplists:get_keys(B) }).

shift({var,{N,I}},N,P) when I>=P -> {var,{N,I+1}};
shift({{<<"∀"/utf8>>,{N,0}},{I,O}},N,P)   -> {{<<"∀"/utf8>>,{N,0}},{shift(I,N,P),shift(O,N,P+1)}};
shift({{<<"λ"/utf8>>,{N,0}},{I,O}},N,P)   -> {{<<"λ"/utf8>>,{N,0}},{shift(I,N,P),shift(O,N,P+1)}};
shift({Q,{L,R}},N,P)             -> {Q,{shift(L,N,P),shift(R,N,P)}};
shift(T,_,_)                     -> T.


subst(Term,Name,Value)           -> subst(Term,Name,Value,0).
subst({<<"→"/utf8>>,        {I,O}},N,V,L) -> {<<"→"/utf8>>,        {subst(I,N,V,L),subst(O,N,V,L)}};
subst({{<<"∀"/utf8>>,{N,0}},{I,O}},N,V,L) -> {{<<"∀"/utf8>>,{N,0}},{subst(I,N,V,L),subst(O,N,shift(V,N,0),L+1)}};
subst({{<<"∀"/utf8>>,{F,X}},{I,O}},N,V,L) -> {{<<"∀"/utf8>>,{F,X}},{subst(I,N,V,L),subst(O,N,shift(V,F,0),L)}};
subst({{<<"λ"/utf8>>,{N,0}},{I,O}},N,V,L) -> {{<<"λ"/utf8>>,{N,0}},{subst(I,N,V,L),subst(O,N,shift(V,N,0),L+1)}};
subst({{<<"λ"/utf8>>,{F,X}},{I,O}},N,V,L) -> {{<<"λ"/utf8>>,{F,X}},{subst(I,N,V,L),subst(O,N,shift(V,F,0),L)}};
subst({app, {F,A}},       N,V,L) -> {app,        {subst(F,N,V,L),subst(A,N,V,L)}};
subst({var, {N,L}},       N,V,L) -> V;                       % index match
subst({var, {N,I}},       N,_,L) when I>L -> {var, {N,I-1}}; % unshift
subst(T,       _,_,_)            -> T.

norm(none)                          -> none;
norm(any)                           -> any;
norm({<<"→"/utf8>>,        {I,O}})           -> {{<<"∀"/utf8>>,{'_',0}},{norm(I),norm(O)}};
norm({{<<"∀"/utf8>>,{N,0}},{I,O}})           -> {{<<"∀"/utf8>>,{N,0}},  {norm(I),norm(O)}};
norm({{<<"λ"/utf8>>,{N,0}},{I,O}})           -> {{<<"λ"/utf8>>,{N,0}},  {norm(I),norm(O)}};
norm({app,{F,A}})                   -> case norm(F) of
                                            {{<<"λ"/utf8>>,{N,0}},{_,O}} -> norm(subst(O,N,A));
                                                             NF -> {app,{NF,norm(A)}} end;
norm({remote,N})                    -> om:cache(norm,N,[]);
norm(T)                             -> T.

eq({{<<"∀"/utf8>>,{"_",0}},X},{<<"→"/utf8>>,Y})                     -> eq(X,Y);
eq({{<<"∀"/utf8>>,{N1,0}},{I1,O1}},{{<<"∀"/utf8>>,{N2,0}},{I2,O2}}) -> eq(I1,I2), eq(O1,subst(shift(O2,N1,0),N2,{var,{N1,0}},0));
eq({{<<"λ"/utf8>>,{N1,0}},{I1,O1}},{{<<"λ"/utf8>>,{N2,0}},{I2,O2}}) -> eq(I1,I2), eq(O1,subst(shift(O2,N1,0),N2,{var,{N1,0}},0));
eq({app,{F1,A1}},{app,{F2,A2}})                   -> eq(F1,F2), eq(A1,A2);
eq({star,N},{star,N})                             -> true;
eq({var,{N,I}},{var,{N,I}})                       -> true;
eq({remote,N},{remote,N})                         -> true;
eq(A,B)                                           -> erlang:error({error, "==", A, B}).

type({star,N},_)              -> {star,N+1};
type({var,{N,I}},D)           -> true = var(N,D), om:keyget(N,D,I);
type({remote,N},D)            -> om:cache(type,N,D);
type({<<"→"/utf8>>,{I,O}},D)           -> {star,hierarchy(star(type(I,D)),star(type(O,D)))};
type({{<<"∀"/utf8>>,{N,0}},{I,O}},D)   -> {star,hierarchy(star(type(I,D)),star(type(O,[{N,norm(I)}|D])))};
type({{<<"λ"/utf8>>,{N,0}},{I,O}},D)   -> star(type(I,D)),
                                 NI = norm(I),
                                 {{<<"∀"/utf8>>,{N,0}},{NI,type(O,[{N,NI}|D])}};
type({app,{F,A}},D)           -> T = type(F,D),
                                 true = func(T),
                                 {{<<"∀"/utf8>>,{N,0}},{I,O}} = T,
                                 Q = type(A,D),
                                 true = eq(I,Q),
                                 norm(subst(O,N,A)).

% 1. Substitution depends only on shift
% 2. Normalization depends only on substitution
% 3. The typechecker is all about the Typing, Equality and Substitution.
% 4. The definitional equality is needed only for
%    application typechecking (argument against domain of function),
%    i.e. for beta-reduction.
