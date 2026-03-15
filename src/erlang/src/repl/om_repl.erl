-module(om_repl).
-export([start/0, mode/0, mode/1, libdir/0, name/1, name/2, read/1, atom/1, scan/1, parse/1]).

start() -> 
    application:start(om),
    om_state:init().

mode() -> application:get_env(om, mode, "morte").
mode(M) -> application:set_env(om, mode, M).

libdir() -> filename:absname(application:get_env(om, root, ".")).

name(N) -> name(mode(), N).
name(M, N) -> 
    Root = libdir(),
    Paths = [filename:join([Root, X, M, N]) || X <- ["", "priv", "library"]],
    case [P || P <- Paths, filelib:is_regular(P)] of
        [T|_] -> T;
        [] -> 
            case [filename:join(P, "@") || P <- Paths, filelib:is_dir(P), filelib:is_regular(filename:join(P, "@"))] of
                [T1|_] -> T1;
                [] -> 
                    io:format("\e[31mNAME_FAIL: Mode ~p, Name ~p\e[0m~n", [M, N]),
                    {error, enoent}
            end
    end.

read(F) -> 
    case file:read_file(F) of
        {ok, B} -> B;
        Err -> erlang:error({read_error, F, Err})
    end.

atom(X) when is_list(X) -> list_to_atom(X).

scan(V) -> 
    S = om_state:init(),
    om_extract:scan(S, V).

parse(B) -> om_parse:expr(om_tok:tokens(B, 0), 0).
