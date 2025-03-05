-module(om_io).
-export([info/3, warning/3, error/3]).

info(Module, String, Args)     -> io:format(format_message(Module, String), Args).
warning(Module, String, Args)  -> io:format(format_message(Module, String), Args).
error(Module, String, Args)    -> io:format(format_message(Module, String), Args).
format_message(Module, String) -> lists:concat([Module, ":", String, "\n\r"]).
