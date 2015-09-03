%%%%%%%%%%%%%%%%%%%%%%
%% Meta interpreter %%
%%%%%%%%%%%%%%%%%%%%%%

% Error voor fase 2: deze staat hier al gedefinieerd, aangezien er
% anders 2 uitvoeringspaden actief zouden worden (die van (unwind, []).
% en (unwind).) waardoor er in de output eerst nog een true zou worden geprint.
eval(unwind) :- !,
  writeln('ERROR: uncaught "unwind"'),
  fail.
% Idem voor fase 3
eval(raise(P)) :- !,
  writef('ERROR: uncaught "raise(%w)"', [P]),
  fail.

% De argumenten zijn hier van de vorm eval(G, Const, M, H, P):
% - G is de uit te voeren evaluatie
% - Const is een lijst van (eventueel) later uit te voeren evaluaties
% - M is een bit dat aangeeft of we al dan niet binnen een mark zitten
% - H is een bit dat aangeeft of we al dan niet binnen een handle zitten
% - P is de outputparameter
eval(G) :-
  eval(G, [], 0, 0, P).

eval((G1,G2), Const, M, H, P) :- !,
  eval(G1, [G2|Const], M, H, P).

% Begin fase 0 %%%%%%%%%%%%%%%%%%%%%%%%
eval(X = Y, Const, M, H, P) :- !,
  X = Y,
  continue(Const, M, H, P).

eval(X is Y, Const, M, H, P) :- !,
  X is Y,
  continue(Const, M, H, P).

eval((X;Y), Const, M, H, P) :- !,
  (eval(X, [], M, H, P);eval(Y, [], M, H, P)),
  continue(Const, M, H, P).

eval(X > Y, Const, M, H, P) :- !,
  X > Y,
  continue(Const, M, H, P).

eval(X =< Y, Const, M, H, P) :- !,
  X =< Y,
  continue(Const, M, H, P).

eval(X == Y, Const, M, H, P) :- !,
  X == Y,
  continue(Const, M, H, P).

eval(X \== Y, Const, M, H, P) :- !,
  X \== Y,
  continue(Const, M, H, P).

eval(writeln(X), Const, M, H, P) :- !,
  writeln(X),
  continue(Const, M, H, P).

eval(read(X), Const, M, H, P) :- !,
  read(X),
  continue(Const, M, H, P).

eval(call(X), Const, M, H, P) :- !,
  call(X),
  continue(Const, M, H, P).

eval(eval(X), Const, M, H, P) :- !,
  eval(X),
  continue(Const, M, H, P).
% Eind fase 0 %%%%%%%%%%%%%%%%%%%%%%%%%

% Begin fase 1 %%%%%%%%%%%%%%%%%%%%%%%%
eval(end, _, _, _, _) :- !.
% Eind fase 1 %%%%%%%%%%%%%%%%%%%%%%%%%

% Begin fase 2 en 3 %%%%%%%%%%%%%%%%%%%
% Als we een mark tegen komen voeren we de code uit in een nieuw
% executiepad waar het markbit op 1 wordt gezet.
eval(mark(X), Const, _, H, P) :- !,
  eval(X, [], 1, H, P),
  continue(Const, 0, H, P).

% Idem voor handle, maar ditmaal zetten we het handlebit op 1.
eval(handle(X, P), Const, M, _, P) :- !,
  eval(X, [], M, 1, P),
  continue(Const, M, 0, P).

% Als we een unwind tegen komen waarbij het markbit op 0 staat
% weten we dat deze niet binnen een mark is opgeroepen. We roepen
% hierbij dus de error op.
eval(unwind, _, 0, _, _) :- !,
  eval(unwind).
% We komen een unwind tegen met een 1 als markbit, we stoppen het pad.
eval(unwind, _, _, _, _) :- !.

% We komen hier een raise tegen zonder dat we in een handle zitten:
% we roepen de error op.
eval(raise(X), _, _, 0, _) :- !,
  eval(raise(X)).
% Hier komen we een raise tegen waarbij het handlebit wel op 1 staat:
% We kennen hier X (het resultaat) toe aan P, de outputparameter.
eval(raise(X), _, _, _, P) :- !,
  P = X.
% Eind fase 2 en 3
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

eval(true, Const, M, H, P) :- !,
  continue(Const, M, H, P).

eval(G, Const, M, H, P) :-
  clause(G,NG),
  eval(NG, Const, M, H, P).

continue([], _, _, _).
continue([G|Const], M, H, P) :-
  eval(G, Const, M, H, P).

%%%%%%%%%%%%%%
%% Testcode %%
%%%%%%%%%%%%%%

% Fibonaccicode
fib(0,1).
fib(1,1).
fib(N,F) :-
  N > 1,
  N1 is N - 1,
  fib(N1,F1),
  N2 is N1 - 1,
  fib(N2,F2),
  F is F1 + F2.
% End Fibonaccicode

% End-testcode
p :-
  writeln(start(p)),
  q,
  writeln(end(p)).

q :-
  writeln(start(q)),
  end,
  writeln(end(q)).
% End-testcode


% mark & unwind
ex1 :-
  writeln(a),
  mark(ex1_1),
  writeln(d).

ex1_1 :-
  writeln(b),
  unwind,
  writeln(c).

ex2 :-
  writeln(a),
  mark(ex2_1),
  writeln(b).

ex2_1 :-
  writeln(c),
  mark(ex2_2),
  writeln(d).

ex2_2 :-
  writeln(e),
  unwind,
  writeln(f).

ex3 :-
  writeln(a),
  mark(ex3_1),
  writeln(d).

ex3_1 :-
  writeln(b),
  writeln(c).

ex4 :-
  writeln(a),
  mark(ex4_1),
  writeln(f).

ex4_1 :-
  writeln(b),
  mark(ex4_2),
  writeln(e).

ex4_2 :-
  writeln(c),
  writeln(d).

ex5 :-
  writeln(a),
  mark(ex5_1),
  writeln(b),
  mark(ex5_2),
  writeln(c).

ex5_1 :-
  writeln(d),
  mark(ex5_2),
  writeln(e).

ex5_2 :-
  writeln(f),
  unwind,
  writeln(g).

nex2 :-
  writeln(a),
  mark(nex2_1),
  writeln(b).

nex2_1 :-
  writeln(c),
  nex2_2,
  writeln(d).

nex2_2 :-
  writeln(e),
  unwind,
  writeln(f).

/* Faal */
ex6 :-
  writeln(a),
  unwind,
  writeln(b).

% End mark & unwind

% Product
product(L,P) :-
  handle(product_(L,P),P).

product_([],1).

product_([X|Xs],P) :-
  X \== 0,
  product_(Xs,P1),
  P is X * P1.

product_([X|Xs],P) :-
  X == 0,
  raise(0).
% End Product

% Felix' searchtree
searchTree(Tree, Value) :-
  mark(searchTree_(Tree, Value)).

searchTree_([Value|_], Value) :-
  unwind.

searchTree_([Tree|Rest], Value) :-
  searchTree_(Tree, Value);
  searchTree_(Rest, Value).
% End Felix' searchtree

%
getPath(Tree, Value, Path) :-
  handle(getPath_(Tree, Value, 0, []), Path).

getPath_([Value|_], Value, Index, Path) :-
  raise([Index|Path]).

getPath_([Tree|Rest], Value, Index, Path) :-
  getPath_(Tree, Value, 0, [Index|Path]);
  (Index_ is Index + 1,
    getPath_(Rest, Value, Index_, Path)).
