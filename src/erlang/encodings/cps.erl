-module(cps).
-description('Composition Continuator Encoding Schema').
-compile(export_all).

% Composition Continuator is

% (F ,X: Type) ... \ (C: Type -> Type) -> C F X

ap(Fun,Args) -> lists:foldl(fun(X,Acc) -> Acc(X) end,Fun,Args).

ap1(Fun,Arg) -> Fun(Arg).

%   data bool: * :=
%        (true: bool)
%        (false: bool)

'if'   () ->  fun (P) -> fun (A) -> fun (B) -> (P(A))(B) end end end.

% > ch:unnat(ch:ap('Bool':'if'(),['Bool':'True'(),
%   fun(_) -> ('List':length())((('ch':'cons'())(1))('List':'Nil'())) end,
%   fun(_) -> 'Nat':'Zero'() end])).
% CONS
% 1
% > ch:unnat(ch:ap('Bool':'if'(),['Bool':'False'(),
%   fun(_) -> ('List':length())((('ch':'cons'())(1))('List':'Nil'())) end,
%   fun(_) -> 'Nat':'Zero'() end])).
% 0

bool   () ->      [ begin io:format("TRUE~n"), "true" end, begin io:format("FALSE~n"), "false" end].
true   () ->       fun (T) -> fun (_) -> io:format("true called~n"), T end end.
false  () ->       fun (_) -> fun (F) -> io:format("false called~n"), F end end.

            bool(F) -> ?MODULE:F().
            unbool(X) -> ap(X,bool()).

% record prod: * :=
%        (pr1: *)
%        (pr2: *)

prod  () ->       [fun (A) -> fun (B)->  {prod,A,B} end end].
prodid () ->                  fun (X) -> fun (_Mk) -> X end end.
mk     () ->       fun (A) -> fun (B) -> fun (Mk) -> ap(Mk,[ap(A,[Mk]),ap(B,[Mk])]) end end end.
pr1    () ->       [fun (A) -> fun (_) -> A end end].
pr2    () ->       [fun (_) -> fun (B) -> B end end].

            prod({A,B}) -> ap(mk(),[ap(prodid(),[A]),ap(prodid(),[B])]).
            unprod(X) -> ap(X,prod()).

% > ch:ap(ch:prod({io,2}),ch:pr1()).
% io
% 2> ch:ap(ch:prod({io,2}),ch:prod()).
% {prod,io,2}

%   data proto: * :=
%        (ok: * → proto)
%        (error: * → proto)
%        (io: * → * → proto)

ret    () ->           [fun (X) -> {ok,X} end, fun (X) -> {error,X} end, fun(X) -> fun (Y) -> {io,X,Y} end end].
retid  () ->            fun (R) -> fun (_Ok) -> fun (_Error) -> fun (_Io) -> R end end end end.
ok     () ->            fun (V) -> fun (Ok) -> fun (Error) -> fun (Io) -> ap(Ok,   [ap(V,[Ok,Error,Io])]) end end end end.
error  () ->            fun (V) -> fun (Ok) -> fun (Error) -> fun (Io) -> ap(Error,[ap(V,[Ok,Error,Io])]) end end end end.
io     () -> fun (X) -> fun (Y) -> fun (Ok) -> fun (Error) -> fun (Io) -> ap(Io,   [ap(X,[Ok,Error,Io]),ap(Y,[Ok,Error,Io])]) end end end end end.

             ret({N,A}) -> ap(?MODULE:N(),[ap(retid(),[A])]);
             ret({io,A,B}) -> ap(io(),[ap(retid(),[A]),ap(retid(),[B])]).
             unret(A) -> ap(A,ret()).

%  data nat: * :=
%       (zero: () → nat)
%       (succ: nat → nat)

nat_   () -> [fun (Succ) -> 1 + Succ end, 0 ].
nat    () -> [fun (Succ) -> {succ,Succ} end, zero].
id     () -> begin fun (X) -> X end end.
zero   () -> fun (_Succ) -> fun (Zero) -> Zero end end.
succ   () -> fun (Nat) -> fun (Succ) -> fun (Zero) -> Succ((Nat(Succ))(Zero)) end end end.
pred   () -> fun(N) -> fun (F) -> fun (X) -> ((N(fun (G) -> fun (H) -> H(G(F)) end end))
             (fun (_) -> X end))(fun (U) -> U end) end end end.

             % mapping to erlang integer

             nat   (0) -> 'Nat':'Zero'();
             nat   (I) -> ('Nat':'Succ2'())(nat(I-1)). % fun (Succ) -> fun(Zero) -> Succ(((nat(I-1))(Succ))(Zero)) end end.
             unnat (N) -> ap(N,nat_()).
             plus(A,B) -> nat(erlang:'+'(unnat(A),unnat(B))).

%  data list: (A:*) → * :=
%       (nil: () → list A)
%       (cons: A → list A → list A)

list_  () -> [fun (H) -> fun (T) -> [H|T] end end, [] ].
list   () -> [fun (H) -> fun (T) -> {cons,H,T} end end, nil].
nil    () -> fun (_Cons) -> fun (Nil) -> Nil end end.
cons   () -> fun (Head) -> fun (Tail) -> fun (Cons) ->
             fun (Nil) -> ((Cons(Head))((Tail(Cons))(Nil))) end end end end.

% mapping to erlang list

list   ([])          -> 'List':'Nil'();
list   ([Head|Tail]) ->  (('List':'Cons'())(Head))(list(Tail)).
unlist (L)           -> ap(L,list_()).

getLine() ->           fun(IO) -> fun(_) -> L = ch:list(io:get_line("> ")), ch:ap(IO,[L]) end end.
putLine() -> fun(S) -> fun(IO) -> io:format(": "), io:put_chars(ch:unlist(S)), ch:ap(IO,[S]) end end.
pure()    ->           fun(IO) -> IO end.

ma() -> ap('Morte':recursive(),[getLine(),putLine(),pure(),ch:nil()]).

% marshaling sample

% > ch:ap(ch:ap(ch:succ(),[ch:ap(ch:succ(),[ch:zero()])]),ch:nat()).
% {succ,{succ,zero}}

% > ch:ap(ch:ap(ch:cons(),[2,ch:ap(ch:cons(),[1,ch:nil()])]),ch:list()).
% {cons,2,{cons,1,nil}}

% benchmarks in 1M

main  ()  -> io:format("Zero: ~p~n",               [unnat(zero())]),
             io:format("Cons/Nil: ~p~n",                [unlist(ap(cons(),[2,ap(cons(),[1,nil()])]))]),
             spawn(fun () -> io:format("Pack/Unpack 1 000 000 Inductive Nat Improved: ~p~n",   [timer:tc(fun () -> unnat1(nat1(1000000)) end)]) end),
             spawn(fun () -> io:format("Pack/Unpack 1 000 000 Inductive Nat Church: ~p~n",   [timer:tc(fun () -> unnat(nat(1000000)) end)]) end),
             spawn(fun () -> io:format("Pack/Unpack 1 000 000 Inductive List: ~p~n",   [{element(1,timer:tc(fun () -> unlist(list(lists:seq(1,1000000))) end)),'_'}]) end ),
             io:format("Test Big List: ~p~n",      [unlist(list([2,3,5,8,11,19]))]),
             io:format("Two: ~p~n",                [unnat(ap(succ(),[ap(succ(),[zero()])]))]).

unnat1(N) -> ap(N,nat1()).
nat1() -> [           fun (F) -> fun (X) -> F(X) + 1 end end, 0 ].
zero1() ->            fun (_) -> fun (X) -> X end end.
succ1() -> fun (Z) -> fun (F) -> fun (X) -> (F(fun(C) -> (C(F))(X) end))(Z) end end end.
one1()  ->            fun (F) -> fun (X) -> (F(fun(C) -> (C(F))(X) end))(zero1()) end end.
two1()  ->            fun (F) -> fun (X) -> (F(fun(C) -> (C(F))(X) end))(one1()) end end.
three1()->            fun (F) -> fun (X) -> (F(fun(C) -> (C(F))(X) end))(two1()) end end.
pred1() -> begin fun (N) -> (N(fun (_) -> fun(Pred) -> Pred end end))(N) end end.

nat1(0) -> zero1();
nat1(I) -> (succ1())(nat1(I-1)).
