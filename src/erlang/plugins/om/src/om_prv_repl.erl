-module(om_prv_repl).

-export([init/1, do/1, format_error/1]).

-define(PROVIDER, repl).
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
            {example, "rebar3 om repl --root=../../"},
            {opts, [
                {root, $r, "root", string, "Root directory of the project"}
            ]},
            {short_desc, "Henk interactive REPL (Erlang shell)"},
            {desc, "Henk interactive REPL (Erlang shell)"}
    ]),
    {ok, rebar_state:add_provider(State, Provider)}.

-spec do(rebar_state:t()) -> {ok, rebar_state:t()} | {error, string()}.
do(State) ->
    {Args, _} = rebar_state:command_parsed_args(State),
    case proplists:get_value(root, Args) of
        undefined -> ok;
        Root -> application:set_env(om, root, Root)
    end,
    rebar_api:info("Initializing Henk REPL environment...", []),
    code:add_pathsa(["ebin"]),
    application:load(henk),
    om_repl:start(),
    om_repl:scan(true),
    rebar_prv_shell:do(State).

-spec format_error(any()) ->  binary().
format_error(Reason) ->
    io_lib:format("~p", [Reason]).
