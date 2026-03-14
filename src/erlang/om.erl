-module(om).
-description('Henk: Pure Type System').
-compile(export_all).

% env

ver(_)       -> ver().
ver()        -> {version,[keyget(I,element(2,application:get_all_key(henk)))||I<-[description,vsn]]}.

rec()        -> ch:rec().
corec()      -> ch:corec().
restart()    -> [ ets:delete(T) || T <- henk:tables() ], henk:boot().
libdir()     -> application:get_env(om,lib,"priv").
mode(S)      -> application:set_env(om,mode,S).
mode()       -> application:get_env(om,mode,"Morte").
debug(S)     -> application:set_env(om,debug,atom(S)).
debug()      -> application:get_env(om,debug,false).

% constants
allmodes()   -> ["Morte"].
modes()      -> allmodes().

% providing functions

help(_)      -> help().
help()       -> om_help:help().
pwd(_)       -> case file:get_cwd() of {ok, Cwd} -> Cwd; _ -> "." end.
print(X)     -> io:format("~ts~n",[bin(X)]).
bin(X)       -> unicode:characters_to_binary(om:flat(om_parse:print(X,0))).
extract(X)   -> om_extract:extr(X).
extract()    -> om_extract:extr("Morte").
norm(T)      -> om_type:norm(T).
eq(X,Y)      -> om_type:eq(X,Y).
type(S)      -> type(S,[]).
type(T,C)    -> om_type:type(T,C).
erase(X)     -> erase(X,[]).
erase(T,C)   -> om_erase:erase(T,C).
modes(_)     -> modes().
allmodes(_)  -> allmodes().
lib(Mode)   -> lists:concat([libdir(),"/",Mode]).
name(_,[])   -> lib(mode());
name(_,F)    -> string:join([lib(mode()),F],"/").
name(M,[],F) -> name(M,F);
name(_,P,F)  -> string:join([lib(mode()),P,F],"/").
tokens(B)    -> om_tok:tokens([],B,0,{1,[]},[]).
str(F)       -> tokens(unicode:characters_to_binary(F)).
read(F)      -> tokens(file(F)).
comp(F)      -> rev(tokens(F,"/")).
cname(F)     -> hd(comp(F)).
tname(F)     -> tname(F,[]).
pname(F)     -> string:join(tl(tl(string:tokens(F,"/"))),"/").
tname(F,S)   -> X = string:join(rev(tl(comp(F))),"/"), case om:mode() of X -> []; _ -> X ++ S end.
show(F)      -> Term = snd(parse(tname(F),cname(F))), mad:info("~n~ts~n~n", [bin(Term)]), Term.
a(F)         -> snd(parse(str(F))).
fst({X,_})   -> X.
snd({error,X}) -> {error,X};
snd({_,[X]}) -> X;
snd({_,X})   -> X.
parse(X)     -> om_parse:expr([],X,[],{0,0}).
parse(T,C)   -> om_parse:expr(T,read(name(mode(),T,C)),[],{0,0}).

% system functions

convert(A,S, nt) -> convert(A,S);
convert(A,_, _)  -> A.

convert([],Acc) -> rev(Acc);
convert([$>|T],Acc) -> convert(T,[61502|Acc]);
convert([$<|T],Acc) -> convert(T,[61500|Acc]);
convert([$:|T],Acc) -> convert(T,[61498|Acc]);
convert([$||T],Acc) -> convert(T,[61564|Acc]);
convert([H|T],Acc)  -> convert(T,[H|Acc]).

% test suite

typed(X)     -> try _ = om:type(X),  {X,[]} catch _:_ -> {X,typed}  end.
erased(X)    -> try A = om:erase(X), {A,[]} catch _:_ -> {X,erased} end.
parsed(F)    -> case parse([],pname(F)) of {_,[X]} -> {X,[]}; _ -> {F,parsed} end.
pipe(L)      -> io:format("[~tp]~n",[L]), % workaround for trevis timeout break
                lists:foldl(fun(X,{A,D}) ->
                {N,E}=?MODULE:X(A), {N,[E|D]} end,{L,[]},[parsed,typed,erased]).
pass(0)      -> "PASSED";
pass(X)      -> "FAILED " ++ integer_to_list(X).
all(_)       -> all().
all()        -> X = lists:flatten([ begin om:restart(), om:mode(M), om:scan() end || M <- allmodes() ]),
                om:restart(), om:mode("Morte"),
                X.
syscard(P)   -> [ {F} || F <- filelib:wildcard(name(mode(),P,"**/*")), filelib:is_dir(F) /= true ].
wildcard(P)  -> Q = om:name(mode(),P), lists:flatten([ {A}
                     || {A,_} <- ets:tab2list(filesystem), lists:sublist(A,length(Q)) == Q ]).
scan()       -> scan([]).
scan(P)      -> Res = [ { flat(element(2,pipe(F))), lists:concat([tname(F),"/",cname(F)])}
                     || {F} <- lists:umerge(wildcard(P),syscard(P)),
                        lists:member(lists:nth(2,tokens(F,"/")),modes()) ],
                Passed = lists:foldl(fun({X,_},B) -> case X of [] -> B; _ -> B + 1 end end, 0, Res),
                {mode(),pass(Passed),Res}.
test(_)      -> All = om:all(),
                io:format("~tp~n",[om_parse:test()]),
                io:format("~tp~n",[All]),
                case lists:all(fun({_Mode,Status,_Tests}) -> Status == om:pass(0) end, All) of
                     true  -> 0;
                     false -> put(ret,1),1 end .

% relying functions

rev(X)       -> lists:reverse(X).
flat(X)      -> lists:flatten(X).
tokens(X,Y)  -> string:tokens(X,Y).
debug(S,A)   -> case om:debug() of true -> io:format(S,A); false -> ok end.
atom(X)      -> list_to_atom(cat([X])).
cat(X)       -> lists:concat(X).
keyget(K,D)  -> proplists:get_value(K,D).
keyget(K,D,I)  -> lists:nth(I+1,proplists:get_all_values(K,D)).

file(F) -> case file:read_file(convert(F,[],element(2,os:type()))) of
                {ok,Bin} -> Bin;
                {error,_} -> erlang:error({"File not found",F}) end.

cache(X,Y,Z) -> om_cache:cache(X,Y,Z).

-define(LOGGER, om_io).

log_modules() -> [om].
log_level() -> info.

-define(LOG_MODULES, (application:get_env(om,log_modules,om))).
-define(LOG_LEVEL,   (application:get_env(om,log_level,om))).

log_level(none) -> 3;
log_level(error) -> 2;
log_level(warning) -> 1;
log_level(_) -> 0.

log(Module, String, Args, Fun) ->
    case log_level(Fun) < log_level(?LOG_LEVEL:log_level()) of
        true -> skip;
        false -> case ?LOG_MODULES:log_modules() of
            any -> ?LOGGER:Fun(Module, String, Args);
            Allowed -> case lists:member(Module, Allowed) of
                true -> ?LOGGER:Fun(Module, String, Args);
                false -> skip end end end.

info(Module, String, Args) -> log(Module,  String, Args, info).
info(        String, Args) -> log(?MODULE, String, Args, info).
info(        String      ) -> log(?MODULE, String, [],   info).

warning(Module, String, Args) -> log(Module,  String, Args, warning).
warning(        String, Args) -> log(?MODULE, String, Args, warning).
warning(        String      ) -> log(?MODULE, String, [],   warning).

error(Module, String, Args) -> log(Module,  String, Args, error).
error(        String, Args) -> log(?MODULE, String, Args, error).
error(        String)       -> log(?MODULE, String, [],   error).
