-module(om_tok).
-export([tokens/2]).
-define(is_space(C), C==$\r; C==$\s; C==$\t).
-define(is_num(C),   C>=$0,  C=<$9 ).
-define(is_alpha(C), C>=$a,  C=<$z;  C>=$A,  C=<$Z;
                     C==$&;  C==$|;  C>=$0,  C=<$9;
                     C==$@;  C==$#;  C==$_;  C==$/;
                     C==$-;  C==$+;  C==$[;  C==$];
                     C==$<;  C==$>;  C==$=;  C==$.).
-define(is_termi(C), C==$!;  C==$$;  C==$%;  C==$:;
                     C==$;;  C==$~;  C==$^;  C==$?).

tokens(Bin, S) -> lists:reverse(tokens(S, Bin, 0, {1,[]}, [])).

tokens(P,<<>>,                    _, {_,C}, Acc)  -> stack(P,C,Acc);
tokens(P,<<"--"/utf8, R/binary>>, L, {_,C}, Acc)  -> tokens(P,R,L,{c,[]},     stack(P,C,Acc));
tokens(P,<<$\n,       R/binary>>, L, {_,C}, Acc)  -> tokens(P,R,L+1,{1,[]},   stack(P,C,Acc));
tokens(P,<<X,         R/binary>>, L, {c,C}, Acc)  -> tokens(P,R,L,{c,[]},     Acc);
tokens(P,<<"->"/utf8, R/binary>>, L, {_,C}, Acc)  -> tokens(P,R,L,{1,[]},     [arrow  | stack(P,C,  Acc)]);
tokens(P,<<$(,        R/binary>>, L, {_,C}, Acc)  -> tokens(P,R,L,{t,[]},     [open   | stack(P,C,  Acc)]);
tokens(P,<<$),        R/binary>>, L, {_,C}, Acc)  -> tokens(P,R,L,{t,[]},     [close  | stack(P,C,  Acc)]);
tokens(P,<<$*,        R/binary>>, L, {a,C}, Acc)  -> tokens(P,R,L,{a,[$*|C]}, Acc);
tokens(P,<<$*,        R/binary>>, L, {X,C}, Acc)  -> tokens(P,R,L,{n,{star,C}},        stack(P,C,Acc));
tokens(P,<<X,         R/binary>>, L, {n,{S,C}}, Acc) when ?is_num(X)  -> tokens(P,R,L,{n,{S,[X|C]}}, Acc);
tokens(P,<<X,         R/binary>>, L, {n,{S,C}}, Acc)  -> tokens(P,R,L,{1,[]}, stack(P,{S,[C]},Acc));
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
tokens(P,<<X,         R/binary>>, L, {_,C}, Acc) when ?is_alpha(X) -> tokens(P,R,L,{a,[X]},  stack(P,C,Acc));
tokens(P,<<X,         R/binary>>, L, {t,C}, Acc) when ?is_termi(X) -> tokens(P,R,L,{t,[X|C]},            Acc);
tokens(P,<<X,         R/binary>>, L, {_,C}, Acc) when ?is_termi(X) -> tokens(P,R,L,{t,[X]},  stack(P,C, Acc));
tokens(P,<<X,         R/binary>>, L, {_,C}, Acc) when ?is_space(X) -> tokens(P,R,L,{s,C},               Acc).

stack(P,{_,C},Ac) -> istar(C,Ac);
stack(P,C,Ac) -> case lists:reverse(lists:flatten(C)) of
    []     -> Ac;
    "("    -> [open|Ac];
    ")"    -> [close|Ac];
    [$#|A] -> [{remote,A}|Ac];
    [X|A] when ?is_alpha(X) -> vars([X|A],Ac);
    [X|A] when ?is_termi(X) -> [{var,{list_to_atom([X|A]),-1}}|Ac];
    X      -> [{var,{list_to_atom(X),0}}|Ac]
end.

fix(X)      -> case lists:flatten(lists:reverse(X)) of [] -> "1"; A -> A end.
istar(X,Acc) -> [{star,list_to_integer(fix(X))}|Acc].
ivar([N,I]) -> [N,I];
ivar([N])   -> [N,"0"].
vars(X,Acc) -> [Name,Index] = ivar(string:tokens(X,"@")),
               [{var,{list_to_atom(Name),list_to_integer(Index)}}|Acc].
