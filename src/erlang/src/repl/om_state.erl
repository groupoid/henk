-module(om_state).
-export([init/0, get/2, set/3, put/3, cache/3]).

-record(state, {
    term       = #{} :: map(),
    norm       = #{} :: map(),
    type       = #{} :: map(),
    erased     = #{} :: map(),
    filesystem = #{} :: map(),
    file       = ""  :: string(),
    mode       = "morte" :: string(),
    debug      = false   :: boolean(),
    hierarchy  = impredicative :: atom(),
    log_level  = info    :: atom(),
    log_modules = any     :: any()
}).

init() -> #state{}.

get(Key, S) when is_record(S, state) ->
    case Key of
        mode       -> S#state.mode;
        debug      -> S#state.debug;
        hierarchy  -> S#state.hierarchy;
        file       -> S#state.file;
        term       -> S#state.term;
        norm       -> S#state.norm;
        type       -> S#state.type;
        erased     -> S#state.erased;
        filesystem -> S#state.filesystem
    end.

set(Key, Val, S) ->
    case Key of
        mode       -> S#state{mode = Val};
        debug      -> S#state{debug = Val};
        hierarchy  -> S#state{hierarchy = Val};
        file       -> S#state{file = Val};
        term       -> S#state{term = Val};
        norm       -> S#state{norm = Val};
        type       -> S#state{type = Val};
        erased     -> S#state{erased = Val};
        filesystem -> S#state{filesystem = Val}
    end.

put(Tab, {Key, Val}, S) ->
    Map = maps:put(Key, Val, get(Tab, S)),
    set(Tab, Map, S).

cache(Tab, N, S) ->
    Map = get(Tab, S),
    case maps:find(N, Map) of
        {ok, V} -> {V, S};
        error ->
            case om_repl:name(N) of
                {error, enoent} ->
                    erlang:error({not_found, N});
                File ->
                    S0 = set(file, File, S),
                    Ast = om_repl:parse(om_repl:read(File)),
                    {V, S1} = case Tab of
                        norm   -> om_type:norm(Ast, S0);
                        type   -> om_type:type(Ast, S0);
                        erased -> om_erase:erase(Ast, [], S0)
                    end,
                    {V, put(Tab, {N, V}, S1)}
            end
    end.
