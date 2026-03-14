-module(om_cache).
-compile(export_all).

ets(Tab, Key, [])    -> ets:delete(Tab,Key);
ets(Tab, Key, Value) -> ets:insert(Tab,{Key,Value}), Value.
ets(Tab, Key) ->
    Res = ets:lookup(Tab,Key),
    Val = case Res of [] -> []; [Value] -> Value; Values -> Values end,
    case Val of [] -> [];
                {_,X} -> X end.

% catch circular remote terms

cache(X,Y,Z) ->
    case application:get_env(om,Y,false) of
         false -> application:set_env(om,Y,true),
                  R = cache_(X,Y,Z),
                  application:set_env(om,Y,false),
                  R;
          true -> io:format("Circular: ~p",[Y]),
                  application:set_env(om,Y,false),
                  erlang:error(circ,list_to_binary(Y)) end.

cache_(type,N,D)   -> case ets(type,N)   of [] -> ets(type,N,om_type:type(om_parse:ret(om:parse([],N)),D)); T -> T end;
cache_(norm,N,_)   -> case ets(norm,N)   of [] -> ets(norm,N,om_type:norm(om_parse:ret(om:parse([],N)))); T -> T end;
cache_(erased,N,D) -> case ets(erased,N) of [] -> ets(erased,N,om_erase:erase(om_parse:ret(om:parse([],N)),D)); T -> T end.
