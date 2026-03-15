-module(om_prv_base).

-export([init/1, do/1, format_error/1]).

-define(PROVIDER, base).
-define(NAMESPACE, om).
-define(DEPS, [{default, app_discovery}]).

-spec init(rebar_state:t()) -> {ok, rebar_state:t()}.
init(State) ->
    Provider = providers:create([
            {name, ?PROVIDER},
            {module, ?MODULE},
            {namespace, ?NAMESPACE},
            {bare, true},
            {deps, ?DEPS},
            {example, "rebar3 om base --root=../../"},
            {opts, [
                {root, $r, "root", string, "Root directory of the project"},
                {verbose, $v, "verbose", boolean, "Show each source Morte file"}
            ]},
            {short_desc, "Compile (typecheck) Henk standard library"},
            {desc, "Compile (typecheck) Henk standard library"}
    ]),
    {ok, rebar_state:add_provider(State, Provider)}.

-spec do(rebar_state:t()) -> {ok, rebar_state:t()} | {error, string()}.
do(State) ->
    {Args, _} = rebar_state:command_parsed_args(State),
    case proplists:get_value(root, Args) of
        undefined -> ok;
        Root -> application:set_env(om, root, Root)
    end,
    Verbose = proplists:get_value(verbose, Args, false),
    rebar_api:info("Typechecking Henk base library...", []),
    code:add_pathsa(["ebin"]),
    code:purge(om_extract),
    code:load_file(om_extract),
    io:format("om_extract which: ~p~n", [code:which(om_extract)]),
    io:format("om_extract compile: ~p~n", [om_extract:module_info(compile)]),
    application:load(henk),
    case application:get_key(henk, applications) of
        {ok, Deps} -> [ application:ensure_all_started(D) || D <- Deps ];
        _ -> ok
    end,
    S0 = om_repl:init(),
    S1 = om_repl:mode("morte", S0),
    rebar_api:info("Extracting Henk base library...", []),
    om_extract:scan(S1, Verbose),
    {ok, State}.

-spec format_error(any()) ->  binary().
format_error(Reason) ->
    io_lib:format("~p", [Reason]).
