-module(om).

-export([init/1]).

-spec init(rebar_state:t()) -> {ok, rebar_state:t()}.
init(State) ->
    {ok, State1} = om_prv_base:init(State),
    {ok, State2} = om_prv_test:init(State1),
    {ok, State3} = om_prv_repl:init(State2),
    {ok, State3}.
