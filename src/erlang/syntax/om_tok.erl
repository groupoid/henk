-module(om_tok).
-description('Tokenizer').
-compile(export_all).
-define(is_num(C),   C>=$0,  C=<$9 ).
-define(is_space(C), C==$\r; C==$\s; C==$\t).
-define(is_termi(C), C==$!;  C==$$;  C==$%;  C==$:; C==$;;  C==$~;  C==$^;  C==$?).
-define(is_alpha(C), C>=$a,  C=<$z;  C>=$A,  C=<$Z; C==$&;  C==$|;  C>=$0,  C=<$9;  C==$@;  C==$#;
                     C==$_;  C==$/;  C==$-;  C==$+; C==$[;  C==$];  C==$<;  C==$>;  C==$=;  C==$.).

tokens(P,<<>>,                    _, {_,C}, Acc)  -> om:rev(stack(P,C,Acc));
tokens(P,<<"--"/utf8, R/binary>>, L, {_,C}, Acc)  -> tokens(P,R,L,{c,[]},     stack(P,C,Acc));
tokens(P,<<$\n,       R/binary>>, L, {_,C}, Acc)  -> tokens(P,R,L+1,{1,[]},   stack(P,C,Acc));
tokens(P,<<_,         R/binary>>, L, {c,_}, Acc)  -> tokens(P,R,L,{c,[]},     Acc);
tokens(P,<<"->"/utf8, R/binary>>, L, {_,C}, Acc)  -> tokens(P,R,L,{1,[]},     [arrow  | stack(P,C,  Acc)]);
tokens(P,<<$(,        R/binary>>, L, {_,C}, Acc)  -> tokens(P,R,L,{t,[]},     [open   | stack(P,C,  Acc)]);
tokens(P,<<$),        R/binary>>, L, {_,C}, Acc)  -> tokens(P,R,L,{t,[]},     [close  | stack(P,C,  Acc)]);
tokens(P,<<$*,        R/binary>>, L, {a,C}, Acc)  -> tokens(P,R,L,{a,[$*|C]}, Acc);
tokens(P,<<$*,        R/binary>>, L, {_,C}, Acc)  -> tokens(P,R,L,{n,{star,C}},        stack(P,C,Acc));
tokens(P,<<X,         R/binary>>, L, {n,{S,C}}, Acc) when ?is_num(X)  -> tokens(P,R,L,{n,{S,[X|C]}}, Acc);
tokens(P,<<_,         R/binary>>, L, {n,{S,C}}, Acc)  -> tokens(P,R,L,{1,[]}, stack(P,{S,[C]},Acc));
tokens(P,<<$:,        R/binary>>, L, {_,C}, Acc)  -> tokens(P,R,L,{1,[]},     [colon  | stack(P,C,  Acc)]);
tokens(P,<<"□"/utf8,  R/binary>>, L, {_,C}, Acc)  -> tokens(P,R,L,{1,[]},     [box    | stack(P,C,  Acc)]);
tokens(P,<<"→"/utf8,  R/binary>>, L, {_,C}, Acc)  -> tokens(P,R,L,{1,[]},     [arrow  | stack(P,C,  Acc)]);
tokens(P,<<$\\,$/,    R/binary>>, L, {_,C}, Acc)  -> tokens(P,R,L,{1,[]},     [pi     | stack(P,C,  Acc)]);
tokens(P,<<"∀"/utf8,  R/binary>>, L, {_,C}, Acc)  -> tokens(P,R,L,{1,[]},     [pi     | stack(P,C,  Acc)]);
tokens(P,<<"forall"/utf8,R/binary>>,L,{_,C},Acc)  -> tokens(P,R,L,{1,[]},     [pi     | stack(P,C,  Acc)]);
tokens(P,<<"Π"/utf8,  R/binary>>, L, {_,C}, Acc)  -> tokens(P,R,L,{1,[]},     [pi     | stack(P,C,  Acc)]);
tokens(P,<<$\\,       R/binary>>, L, {_,C}, Acc)  -> tokens(P,R,L,{1,[]},     [lambda | stack(P,C,  Acc)]);
tokens(P,<<"λ"/utf8,  R/binary>>, L, {_,C}, Acc)  -> tokens(P,R,L,{1,[]},     [lambda | stack(P,C,  Acc)]);
tokens(P,<<X,         R/binary>>, L, {a,C}, Acc) when ?is_alpha(X) -> tokens(P,R,L,{a,[X|C]},            Acc);
tokens(P,<<X,         R/binary>>, L, {_,C}, Acc) when ?is_alpha(X) -> tokens(P,R,L,{a,[X]},  stack(P,[C],Acc));
tokens(P,<<X,         R/binary>>, L, {t,C}, Acc) when ?is_termi(X) -> tokens(P,R,L,{t,[X|C]},            Acc);
tokens(P,<<X,         R/binary>>, L, {_,C}, Acc) when ?is_termi(X) -> tokens(P,R,L,{t,[X]},  stack(P,C, [Acc]));
tokens(P,<<X,         R/binary>>, L, {_,C}, Acc) when ?is_space(X) -> tokens(P,R,L,{s,[C]},              Acc).

stack(_,{_,C},Ac) -> index(C,Ac);
stack(P,C,Ac) -> case om:rev(om:flat(C)) of [] -> Ac;
                                         "(" -> [open|Ac];
                                         ")" -> [close|Ac];
                                      [$#|A] -> inet(P,A,Ac);
                     [X|A] when ?is_alpha(X) -> vars([X|A],Ac);
                     [X|A] when ?is_termi(X) -> name([X|A],Ac);
                                          X  -> atom(X,Ac) end.

inet(P,X,Acc) -> [{remote,{P,X}}|Acc].
atom(X,Acc)   -> [list_to_atom(X)|Acc].
name(X,Acc)   -> [{var,{X,-1}}|Acc].
fix(X)        -> case lists:flatten(lists:reverse(X)) of [] -> "1"; A -> A end.
index(X,Acc)  -> [{star,list_to_integer(fix(X))}|Acc].
ivar([N,I])   -> [N,I];
ivar([N])     -> [N,"0"].
vars(X,Acc)   -> [Name,Index]= ivar(om:tokens(X,"@")),
                 [{var,{list_to_atom(Name),list_to_integer(Index)}}|Acc].
