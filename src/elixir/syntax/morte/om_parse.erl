-module(om_parse).
-description('Parser').
-compile(export_all).
-define(arr(F), (F == lambda orelse F == pi)).
-define(noh(F), (F /= '$'   andalso F /= ':')).
-define(nah(F,C),  (?noh(C) andalso ?noh(F))).
-define(reason1, "syntax violation").
-define(reason2, "syntax violation").
-define(reason3, "wrong function definition").

expr(_,[],                 [{':',X}],{_,_}) ->      {error,{?reason3,X}};
expr(_,[],                         A,{V,D}) ->      rewind(A,{V,D},[]);
expr(P,[close                 |T], A,{_,D}) -> case rewind(A,{D,D},[]) of
                                                    {error,R} -> {error,R};
                                                    {{V1,D1},A1} -> expr(P,T,A1,{V1,D1}) end;

expr(P,[F,open,{var,L},colon  |T], Acc, {V,D}) when ?arr(F)   -> expr(P,T,[{'$',{func(F),L}}|Acc],{V,D+1});
expr(P,[{remote,{_,L}}|T],  [{C,Y}|Acc],{V,D}) when ?noh(C)   -> expr(P,T,[{app,{{C,Y},{remote,L}}}|Acc],{V,D});
expr(P,[{remote,{_,L}}        |T], Acc, {V,D})                -> expr(P,T,[{remote,L}|Acc],{V,D});
expr(P,[{N,X}|T],           [{C,Y}|Acc],{V,D}) when ?nah(N,C) -> expr(P,T,[{app,{{C,Y},{N,X}}}|Acc],{V,D});
expr(P,[{N,X}                 |T], Acc, {V,D}) when ?noh(N)   -> expr(P,T,[{N,X}|Acc],{V,D});
expr(P,[open                  |T], Acc, {V,D})                -> expr(P,T,[{open}|Acc],{V,D+1});
expr(P,[box                   |T], Acc, {V,D})                -> expr(P,T,[{star,2}|Acc],{V,D});
expr(P,[arrow                 |T], Acc, {V,D})                -> expr(P,T,[{arrow}|Acc],{V,D});
expr(_,[X                     |T], _cc, {_,_})                -> {error,{?reason1,hd(lists:flatten([X|T]))}}.

rewind([],                      {V,D},       R)  -> {{V,D},om:flat(R)};
rewind([{':',_}|_]=A,           {V,D},       R)  -> {{V,D},om:flat([R|A])};
rewind([{'$',M}|A],             {V,D},[{C,X}|R]) -> rewind([{':',{M,{C,X}}}|A],{V,D},R);
rewind([{arrow},{':',{M,I}} |A],{V,D},[{C,X}|R]) -> rewind([{M,{I,{C,X}}}|A],{V,D},R);
rewind([{arrow},{B,Y}       |A],{V,D},[{C,X}|R]) -> rewind([{func(arrow),{{B,Y},{C,X}}}|A],{V,D},R);
rewind([{C,X},{'$',M}|A],{V,D},R) when V == D    -> rewind([{':',{M,{C,X}}}|A],{V,D},R);
rewind([{_,_},{'$',_}|_]=A,          {V,D},  R)  -> {{V,D},  om:flat([A|R])};
rewind([{C,X},{open},{':',{M,I}} |A],{V,D},  R)  -> {{V,D-1},om:flat([{C,X},{':',{M,I}}  |[R|A]])};
rewind([{C,X},{open},{'$',M}     |A],{V,D},  R)  -> {{V,D-1},om:flat([{C,X},{'$',M}      |[R|A]])};
rewind([{C,X},{open},{open}      |A],{V,D},  R)  -> {{V,D-1},om:flat([{C,X},{open}       |[R|A]])};
rewind([{C,X},{open},{B,Y}       |A],{V,D},  R)  -> {{V,D-1},om:flat([{app,{{B,Y},{C,X}}}|[R|A]])};
rewind([{C,X},{open}|A],{V,D},               R)  -> {{V,D-1},om:flat([{C,X}|[R|A]])};
rewind([{C,X},{arrow},{':',{M,I}}|A],{V,D},  R)  -> rewind([{M,{I,{C,X}}}|A],{V,D},R);
rewind([{C,X},{arrow},{B,Y} |A],{V,D},       R)  -> rewind([{func(arrow),{{B,Y},{C,X}}}|A],{V,D},R);
rewind([{C,X},{B,Y}|A], {V,D}, R) when ?nah(C,B) -> rewind([{app,{{B,Y},{C,X}}}|A],{V,D},R);
rewind([{_,_}]=A,         {V,D}, R) when ?noh(A) -> {{V,D},om:flat([R|A])};
rewind(A,                 {_,_}, R)              -> {error,{?reason2,hd(lists:flatten([R|A]))}}.

% Syntax and Algorithm

%     I := #identifier
%     O := ∅ | ( O ) |
%          □ | ∀ ( I : O ) → O |
%          * | λ ( I : O ) → O |
%          I | O → O | O O

% During forward pass we stack applications, then
% on reaching close paren ")" we perform backward pass and stack arrows,
% until neaarest unstacked open paren "(" appeared (then we just return
% control to the forward pass).

test() -> F = [ "(x : ( \\ (o:*) -> o ) -> p ) -> o",        % colon
                "\\ (x : ( err (o:*) -> o ) -> p ) -> o",    % ->
                "\\ (x:*)",                                  % :
                "\\ (x : ( (o:*) -> o ) -> p ) -> o",        % ->
                "\\ (x : ( \\ (o:*) -> o ) -> p ) err -> o", % colon
                "\\ (x : \\ (x: x -> l) -> o ) l -> z",      % colon
                "\\ (x : ( (o:*) -> o ) -> p ) -> o"         % colon
              ],

          T = [ "\\ (x : (\\ (o:*) -> o) l -> p ) -> o",
                "\\ (x : ( \\ (o: \\ (x : (\\ (o:*) -> o) l -> p ) -> o) -> o ) -> p ) -> o",
                "* -> a \\ (x : a (\\ (o:*) -> o) l -> p ) -> o",
                 "\\(x : (\\ (o:*) -> o) -> p ) -> o"
               ],

          TT = lists:foldl(fun(X,Acc) ->  {X,{M,_}=A} = {X,om:a(X)},
                                     case M of error -> erlang:error(["test",X,"failed",A]);
                                                 _ -> ok end,
                                     [{X,A}|Acc] end, [], T),

          FF =lists:foldl(fun(X,Acc) -> {X,{error,{M,A}}} = {X,om:a(X)},
                                    [{M,X,A}|Acc] end, [], F),

          FF ++ TT.

pad(D)                         -> lists:duplicate(D,"  ").

print(any,_)                   -> ["any"];
print(none,_)                  -> ["none"];
print({remote,L},_)            -> ["#", om:cat([L]) ];
print({var,{N,0}},_)           -> [ om:cat([N]) ];
print({var,{N,I}},_)           -> [ om:cat([N]), "@", integer_to_list(I) ];
print({star,2},_)              -> [ "[]" ];
print({star,N},_)              -> [ "*",om:cat([N]) ];
print({<<"→"/utf8>>,{I,O}},D)           -> [ "(", print(I,D+1),"\n",pad(D),"→ ",print(O,D), ")\n" ];
print({app,{I,O}},D)           -> [ "(", print(I,D)," ",print(O,D),")" ];
print({{<<"∀"/utf8>>,{N,_}},{any,O}},D) -> [ "( ∀ ", om:cat([N]),"\n",pad(D),"→ ",print(O,D),")" ];
print({{<<"∀"/utf8>>,{N,_}},{I,O}},D)   -> [ "( ∀ (",om:cat([N]),": ",print(I,D+1),")\n",pad(D),"→ ",print(O,D),")" ];
print({{<<"λ"/utf8>>,{N,_}},{any,O}},D) -> [ "( λ ", om:cat([N]),"\n",pad(D),"→ ",print(O,D),")" ];
print({{<<"λ"/utf8>>,{N,_}},{I,O}},D)   -> [ "( λ (",om:cat([N]),": ",print(I,D+1),")\n",pad(D),"→ ",print(O,D),")" ].

func(lambda) -> <<"λ"/utf8>>;
func(pi)     -> <<"∀"/utf8>>;
func(arrow)  -> <<"→"/utf8>>;
func(star)   -> <<"*"/utf8>>;
func(Sym)    -> Sym.

ret({_,[X]}) -> X;
ret(Y) -> Y.
