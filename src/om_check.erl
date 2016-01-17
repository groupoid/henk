-module(om_check).
-compile(export_all).

error({input,X})        -> om:print("Invalid input type: ~p~n",[X]);
error({output,X})       -> om:print("Invalid output type: ~p~n",[X]);
error({untyped,X})      -> om:print("No type for: ~p~n",[X]);
error({mismatch,{X,Y}}) -> om:print("Invalid Application~nExpected type: ~p~nArgument type: ~p~n",[X,Y]);
error({unbound,_})      -> "Unbound variable.~n";
error({app,_})          -> "Only functions may be applied to values.~n";
error(__)               -> "Unknown type error".

freeIn({var,{X,N}}=_V,{{Fun,Y},{In,Out}}) when Fun=="λ";Fun=="∀";X==Y -> freeIn(_V,In) orelse freeIn({var,{X,N+1}},Out);
freeIn({var,{X,N}}=_V,{{Fun,Y},{In,Out}}) when Fun=="λ";Fun=="∀"      -> freeIn(_V,In) orelse freeIn(_V,Out);
freeIn({var,{_,_}}=_V,{app,{In,Out}})                                 -> freeIn(_V,In) orelse freeIn(_V,Out);
freeIn({var,{X,N}}=_V,{var,{Y,O}})   -> X == Y;
freeIn(_,_)                          -> false.
