-module(henk).
-behaviour(supervisor).
-behaviour(application).
-export([init/1, start/2, stop/1, start/0]).

start()      -> start(normal,[]).
start(_,_)   -> io:setopts(standard_io, [{encoding, unicode}]), supervisor:start_link({local,henk},henk,[]).
stop(_)      -> ok.
init([])     -> om_repl:start(), {ok, {{one_for_one, 5, 10}, []}}.
