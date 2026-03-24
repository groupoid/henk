%% henk_io.erl — Leaf console FFI for Henk.
%% Only exposes primitive get_line/0 and put_line/1.
%% The IO/IOI interpreter loops are written in Henk (.henk files).

-module(henk_io).
-export([get_line/0, put_line/1]).

get_line() ->
    Line = io:get_line(""),
    unicode:characters_to_binary(string:trim(Line, trailing, "\n")).

put_line(Str) when is_binary(Str) -> io:format("~ts~n", [Str]);
put_line(Str) when is_list(Str)   -> io:format("~ts~n", [Str]);
put_line(Str)                     -> io:format("~tp~n", [Str]).
