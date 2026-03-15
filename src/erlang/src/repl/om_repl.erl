-module(om_repl).
-export([init/0, mode/2, type/2, norm/2, erase/2, parse/1]).
-export([ver/0, start/0, mode/1, mode/0, type/1, norm/1, erase/1, scan/1, test/1, extr/1]).
-export([read/1, atom/1, name/1, name/2, libdir/0, modes/0, allmodes/0]).

init() -> om_state:init().
mode(M, S) -> om_state:set(mode, M, S).
type(T, S) -> om_type:type(parse(T), S).
norm(T, S) -> om_type:norm(parse(T), S).
erase(T, S) -> om_erase:erase(parse(T), S).

parse(T) when is_list(T) -> om_parse:expr(om_tok:tokens(list_to_binary(T), 0), 0);
parse(T) when is_binary(T) -> om_parse:expr(om_tok:tokens(T, 0), 0);
parse(T) -> T.

% Shell API (Impure)
start() -> put(state, init()), mode("morte").
mode(M) -> S = get(state), S1 = mode(M, S), put(state, S1), M.
mode() -> om_state:get(mode, get(state)).

type(T) -> {R, S} = type(T, get(state)), put(state, S), R.
norm(T) -> {R, S} = norm(T, get(state)), put(state, S), R.
erase(T) -> {R, S} = erase(T, get(state)), put(state, S), R.

scan(V) -> om_extract:scan(get(state), V).
extr(X) -> om_extract:extr(get(state), X, true).
test(_) -> scan(true).

% Helpers
ver() -> ok.
read(F) -> {ok, B} = file:read_file(F), B.
atom(X) -> list_to_atom(X).
libdir() -> filename:absname(application:get_env(om, root, ".")).
modes() -> ["morte"].
allmodes() -> modes().
name(N) -> name(mode(), N).
name(M, N) -> 
    Root = libdir(),
    Paths = [filename:join([Root, X, M, N]) || X <- ["", "priv", "library"]],
    case [P || P <- Paths, filelib:is_file(P)] of
        [P|_] -> P;
        [] -> filename:join([Root, M, N]) % Fallback
    end.
