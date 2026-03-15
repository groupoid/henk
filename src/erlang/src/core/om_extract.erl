-module(om_extract).
-export([scan/2, extr/3, extract_path/3]).

scan(S, V) -> 
    Root = om_repl:libdir(),
    Paths = [filename:join(Root, X) || X <- ["priv/morte", "library/morte", "morte"]],
    lists:foldl(fun(P, S0) ->
        case filelib:is_dir(P) of true -> extract_path(S0, P, V); false -> S0 end
    end, S, Paths).

extr(S, X, V) ->
    Root = om_repl:libdir(),
    Paths = [X, filename:join(Root, X), filename:join([Root, "priv", X]), filename:join([Root, "library", X])],
    case [P || P <- Paths, filelib:is_file(P) orelse filelib:is_dir(P)] of
        [Target|_] -> extract_path(S, Target, V);
        [] -> {error, enoent}
    end.

extract_path(S, P, V) ->
    case filelib:is_dir(P) of
        true ->
            Rel = rel(P),
            Mod = om_repl:atom(case Rel of "" -> filename:basename(P); _ -> string:join(string:tokens(Rel, "/"), ".") end),
            {ok, Files} = file:list_dir(P),
            Header = [{attribute,1,module,Mod}, {attribute,1,compile,export_all}],
            {Fs, S1} = lists:foldl(fun(F, {Acc, S0}) ->
                Path = filename:join(P, F),
                case filelib:is_dir(Path) of
                    true -> {Acc, S0};
                    false ->
                        S0F = om_state:set(file, Path, S0),
                        try
                            Expr = om_parse:expr(om_tok:tokens(om_repl:read(Path), 0), 0),
                            {E, SA} = om_erase:erase(Expr, [], S0F),
                            {Ext, SB} = om_type:norm(element(1, E), SA),
                            case ext(F, Ext, 1) of 
                                [] -> {Acc, SB}; 
                                Ex -> 
                                    if V -> io:format("\e[90m===> ~ts\e[0m~n", [Rel++"/"++F]); true -> ok end,
                                    {[Ex|Acc], SB}
                            end
                        catch _:{parse_error, _} -> {Acc, S0}; _ -> {Acc, S0} end
                end
            end, {[], S}, Files),
            case Fs of
                [] -> ok;
                _ -> save(Mod, Header ++ lists:reverse(Fs) ++ [{eof, 1}])
            end,
            lists:foldl(fun(D, S_RECURSE) -> 
                Child = filename:join(P, D),
                case filelib:is_dir(Child) of true -> extract_path(S_RECURSE, Child, V); false -> S_RECURSE end
            end, S1, Files);
        false ->
            case filelib:is_file(P) of
                true ->
                    Rel = rel(filename:dirname(P)),
                    Mod = om_repl:atom(case Rel of "" -> filename:basename(P); _ -> string:join(string:tokens(Rel, "/"), ".") end),
                    try
                        SF = om_state:set(file, P, S),
                        Expr = om_parse:expr(om_tok:tokens(om_repl:read(P), 0), 0),
                        {E, S1} = om_erase:erase(Expr, [], SF),
                        {Ext, S2} = om_type:norm(element(1, E), S1),
                        F = filename:basename(P),
                        case ext(F, Ext, 1) of 
                            [] -> S2; 
                            Ex -> 
                                save(Mod, [{attribute,1,module,Mod}, {attribute,1,compile,export_all}, Ex, {eof, 1}]),
                                S2
                        end
                    catch _ -> S end;
                false -> S
            end
    end.

rel(X) ->
    Lib = om_repl:libdir(),
    Rest = case string:prefix(X, Lib) of
        nomatch -> X;
        P_ -> string:trim(P_, leading, "/")
    end,
    lists:foldl(fun(Prefix, Acc) ->
        case string:prefix(Acc, Prefix) of
            nomatch -> Acc;
            P1 -> string:trim(P1, leading, "/")
        end
    end, Rest, ["priv/morte", "library/morte", "morte"]).

save(M, F) ->
    case compile:forms(lists:flatten(F), [debug_info]) of
        {ok, M, B} ->
            filelib:ensure_dir("ebin/"), T = "ebin/" ++ atom_to_list(M) ++ ".beam",
            file:write_file(T, B), 
            io:format("\e[32mSaving compiled '~s.beam' module.\e[0m~n", [M]),
            code:load_binary(M, T, B);
        _Err -> ok
    end.

ext(F, T, C) ->
    Name = list_to_atom(filename:rootname(F)),
    case ext_body(T, C) of
        [] -> [];
        Body -> {function, C, Name, 0, [{clause, C, [], [], [Body]}]}
    end.

ext_body(T, C) ->
    case T of
        none       -> [];
        {"→", _}   -> [];
        {{"∀", _}, _} -> [];
        {{"λ", {N, _}}, {_, O}} ->
            {'fun', C, {clauses, [{clause, C, [{var, C, N}], [], [ext_body(O, C)]}]}};
        {app, {A, B}} -> {call, C, ext_body(A, C), [ext_body(B, C)]};
        {var, {N, _}} -> {var, C, N};
        {remote, R} -> 
            case string:tokens(R, "/@") of
                [M1, F1] -> {call, C, {remote, C, {atom, C, list_to_atom(M1)}, {atom, C, list_to_atom(F1)}}, []};
                _ -> {string, C, R}
            end;
        {star, _} -> {atom, C, star};
        _ -> []
    end.
