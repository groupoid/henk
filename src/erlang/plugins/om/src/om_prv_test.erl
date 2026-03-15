-module(om_prv_test).

-export([init/1, do/1, format_error/1]).

-define(PROVIDER, test).
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
            {example, "rebar3 om test --root=../../"},
            {opts, [
                {root, $r, "root", string, "Root directory of the project"}
            ]},
            {short_desc, "Run Henk integration tests"},
            {desc, "Run Henk integration tests"}
    ]),
    {ok, rebar_state:add_provider(State, Provider)}.

-spec do(rebar_state:t()) -> {ok, rebar_state:t()} | {error, string()}.
do(State) ->
    {Args, _} = rebar_state:command_parsed_args(State),
    case proplists:get_value(root, Args) of
        undefined -> ok;
        Root -> application:set_env(om, root, Root)
    end,
    rebar_api:info("Running Henk integration tests...", []),
    code:add_pathsa(["ebin"]),
    application:load(henk),
    S0 = om_repl:init(),
    om_repl:scan(true), % Historical: om_repl:test used scan
    rebar_api:info("Tests finished.", []),
    {ok, State}.

-spec format_error(any()) ->  binary().
format_error(Reason) ->
    io_lib:format("~p", [Reason]).
