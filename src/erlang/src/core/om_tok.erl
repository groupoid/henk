-module(om_tok).
-export([tokens/2]).
-define(is_alpha(C), (C>=$a andalso C=<$z) orelse (C>=$A andalso C=<$Z) orelse (C>=$0 andalso C=<$9) orelse C==$_ orelse C==$/ orelse C==$# orelse C==$- orelse C==$+ orelse C==$. orelse C==$@ orelse C==$$ orelse C==$| orelse C==$& orelse C==$[ orelse C==$] orelse C==$< orelse C==$> orelse C==$= orelse C==$!).

tokens(Bin, S) -> tokens(Bin, S, 1, [], []).

tokens(<<>>, _, _, Acc, []) -> lists:reverse(Acc);
tokens(<<>>, _, _, Acc, Cur) -> lists:reverse(stack(lists:reverse(Cur), Acc));
tokens(<<"--", R/binary>>, S, L, Acc, Cur) -> comment(R, S, L, stack(lists:reverse(Cur), Acc));
tokens(<<$\n, R/binary>>, S, L, Acc, Cur) -> tokens(R, S, L+1, stack(lists:reverse(Cur), Acc), []);
tokens(<<$-, $>, R/binary>>, S, L, Acc, Cur) -> tokens(R, S, L, [arrow|stack(lists:reverse(Cur), Acc)], []);
tokens(<<$\\, R/binary>>, S, L, Acc, Cur) when Cur==[] -> tokens(R, S, L, [lambda|Acc], []);
tokens(<<$*, R/binary>>, S, L, Acc, Cur) -> 
    case Cur of 
        [$*|_] -> tokens(R, S, L, Acc, [$*|Cur]);
        []     -> tokens(R, S, L, Acc, [$*]);
        _      -> tokens(R, S, L, stack(lists:reverse(Cur), Acc), [$*])
    end;
tokens(<<X, R/binary>>, S, L, Acc, Cur) when X==$(; X==$); X==$: ->
    Sym = case X of $( -> open; $) -> close; $: -> colon end,
    tokens(R, S, L, [Sym|stack(lists:reverse(Cur), Acc)], []);
tokens(<<X/utf8, R/binary>>, S, L, Acc, Cur) when X==16#2200; X==16#3a0; X==16#3a0; X==16#2200 -> tokens(R, S, L, [pi|stack(lists:reverse(Cur), Acc)], []); % ∀, Π
tokens(<<X/utf8, R/binary>>, S, L, Acc, Cur) when X==16#3bb; X==16#2202 -> tokens(R, S, L, [lambda|stack(lists:reverse(Cur), Acc)], []); % λ, ∂
tokens(<<X/utf8, R/binary>>, S, L, Acc, Cur) when X==16#2192 -> tokens(R, S, L, [arrow|stack(lists:reverse(Cur), Acc)], []); % →
tokens(<<X, R/binary>>, S, L, Acc, Cur) when ?is_alpha(X) -> tokens(R, S, L, Acc, [X|Cur]);
tokens(<<_, R/binary>>, S, L, Acc, Cur) -> tokens(R, S, L, stack(lists:reverse(Cur), Acc), []).

comment(<<$\n, R/binary>>, S, L, Acc) -> tokens(R, S, L+1, Acc, []);
comment(<<_, R/binary>>, S, L, Acc) -> comment(R, S, L, Acc);
comment(<<>>, _, _, Acc) -> lists:reverse(Acc).

stack([], Acc) -> Acc;
stack([$*|T], Acc) -> [{star, length(T)+1}|Acc];
stack([$#|T], Acc) -> [{remote, T}|Acc];
stack(Cur, Acc) -> 
    case lists:member($@, Cur) of
        true -> [N, I] = string:tokens(Cur, "@"), [{var, {list_to_atom(N), list_to_integer(I)}}|Acc];
        _    -> try [{star, list_to_integer(Cur)}|Acc] catch _:_ -> [{var, {list_to_atom(Cur), 0}}|Acc] end
    end.
