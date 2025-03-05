-module(om_erase).
-description('Eraser').
-import(om_type,[type/2,star/1,norm/1,eq/2,subst/3,func/1,hierarchy/2,var/2]).
-compile(export_all).
-define(is_fun(F), F == <<"∀"/utf8>>; F== <<"λ"/utf8>>).

univ({star,_})        -> true;
univ({{<<"∀"/utf8>>,_},{_,O}}) -> univ(O);
univ(_)               -> false.

erase({box,_},_)             -> {none,{star,3}};
erase({star,N},_)            -> {none,{star,N+1}};
erase({var,{N,I}},D)         -> true = var(N,D),
                                T = om:keyget(N,D,I),
                                case univ(T) of
                                     true  -> {none,T};
                                     false -> {{var,{N,I}},T} end;
erase({<<"→"/utf8>>,{I,O}},D)         -> {none,{star,hierarchy(star(type(I,D)),star(type(O,D)))}};
erase({{<<"∀"/utf8>>,{N,0}},{I,O}},D) -> {none,{star,hierarchy(star(type(I,D)),star(type(O,[{N,norm(I)}|D])))}};
erase({{<<"λ"/utf8>>,{N,0}},{I,O}},D) -> star(type(I,D)),
                                NI = norm(I),
                                {B1,S1} = erase(O,[{N,NI}|D]),
                                T = {{<<"∀"/utf8>>,{N,0}},{NI,S1}},
                                case univ(NI) of
                                     true  -> {B1,T};
                                     false -> {{{<<"λ"/utf8>>,{N,0}},{any,B1}},T} end;
erase({app,{F,A}},D)         -> {B1,S1} = erase(F,D),
                                {B2,S2} = erase(A,D),
                                true = func(S1),
                                {{<<"∀"/utf8>>,{N,0}},{I,O}} = S1,
                                true = eq(I,S2),
                                T=norm(subst(O,N,A)),
                                case univ(S1) of
                                     true  -> {none,T};
                                     false -> case univ(S2) of
                                                   true  -> {B1,T};
                                                   false -> {{app,{B1,B2}},T} end end;
erase({remote,N},D)          -> om:cache(erased,N,D).

