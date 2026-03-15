-module(om_erase).
-export([erase/2, erase/3, bind/3]).

erase(T, S) -> erase(T, [], S).

erase(T, D, S) ->
    case T of
        {star, N} -> {{none, {star, N+1}}, S};
        {var, V} -> 
            case lists:keyfind(V, 1, D) of
                {V, Type} -> case univ(Type) of true -> {{none, Type}, S}; _ -> {{{var, V}, Type}, S} end;
                _ -> erlang:error({var, V})
            end;
        {<<226,134,146>>, {_I, _O}} -> {{none, element(1, om_type:type(T, D, S))}, S};
        {{Q, N}, {I, O}} when Q==<<226,136,128>>; Q==<<206,187>> ->
            {RI, S1} = om_type:type(I, D, S), {NI, S2} = om_type:norm(I, S1),
            {B1, S3} = erase(O, bind(N, NI, D), S2),
            case Q of
                <<226,136,128>> -> 
                    Star = case element(1, RI) of {star, Idx} -> {star, Idx}; star -> {star, 1}; _ -> {star, 1} end,
                    {{none, Star}, S3};
                <<206,187>> ->
                   T1 = {{<<226,136,128>>, N}, {NI, element(2, B1)}},
                   case univ(NI) of true -> {{element(1, B1), T1}, S3}; _ -> {{{{<<206,187>>, N}, {any, element(1, B1)}}, T1}, S3} end
            end;
        {app, {F, A}} ->
            {B1, S1} = erase(F, D, S), {B2, S2} = erase(A, D, S1),
            {TypeF, S1A} = om_type:norm(element(2, B1), S1),
            {{<<226,136,128>>, N}, {_I, O}} = TypeF,
            T1 = element(1, om_type:norm(om_type:subst(O, N, A), S1A)),
            case univ(element(2, B1)) of 
                true -> {{none, T1}, S1A}; 
                _ -> case univ(element(2, B2)) of true -> {{element(1, B1), T1}, S1A}; _ -> {{{app, {element(1, B1), element(1, B2)}}, T1}, S1A} end
            end;
        {remote, N} -> om_state:cache(erased, N, S)
    end.

bind({Name, _}, Type, D) ->
    D1 = [{{N, I+1}, T} || {{N, I}, T} <- D, N == Name] ++ [{{N, I}, T} || {{N, I}, T} <- D, N /= Name],
    [{{Name, 0}, Type} | D1].

univ({star, _}) -> true;
univ({{<<226,136,128>>, _}, {_, O}}) -> univ(O);
univ(_) -> false.
