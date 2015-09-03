%%% Project Programmeertalen: Assignment 1, deel 1
%%% Schrijven van een Sudoku die het aantal oproepen
%%% bijhoudt door het gebruik van cells
%
% Author: Tom Naessens
%
% Uitvoering:
% * Start swiprolog
% * Laad dit bestand in via ['Assigment1.3.a.pl'].
% * Voer het testvoorbeeld uit via solveExample.
%
% Mogelijkheid tot het uitvoeren van andere sudokus via:
% Sudoku = [[_,_,_,_,1,3,5,_,_],
%           [_,_,_,6,_,7,_,_,_],
%           [_,_,_,_,_,_,2,_,1],
%           [_,9,_,_,_,_,_,6,5],
%           [5,_,_,_,_,_,_,_,7],
%           [2,8,_,_,_,_,_,9,_],
%           [6,_,7,_,_,_,_,_,_],
%           [_,_,_,7,_,9,_,_,_],
%           [_,_,4,8,2,_,_,_,_]],
% solve(Sudoku).
%
% Extra:
% Het is ook mogelijk om sudokus te genereren via
% generateSudoku.
% Of via:
% Sudoku = [[_,_,_,_,_,_,_,_,_],
%           [_,_,_,_,_,_,_,_,_],
%           [_,_,_,_,_,_,_,_,_],
%           [_,_,_,_,_,_,_,_,_],
%           [_,_,_,_,_,_,_,_,_],
%           [_,_,_,_,_,_,_,_,_],
%           [_,_,_,_,_,_,_,_,_],
%           [_,_,_,_,_,_,_,_,_],
%           [_,_,_,_,_,_,_,_,_]],
% solve(Sudoku).


%% Imports
%
% CLPFD: Constraint Logic Programming library
:- use_module(library(clpfd)).


%% Cellen
%
% Maakt gebruik van globale variabelen in Prolog
% Sauce: http://www.swi-prolog.org/pldoc/doc_for?object=section(2,'6.3',swi('/doc/Manual/gvar.html'))

%% Hulpfunctie: create/0
%
% Creëert alle tellers
%
% Maakt gebruik van create/1
create :-
  create(solveC),
  create(all_blocks_distinctC),
  create(split_in_threeC),
  create(prettyPrintC),
  create(prettyPrintRowsC),
  create(prettyPrintRowC),
  create(totalC).

%% Hulpfunctie: create/1
%
% Creëert 1 specifieke teller
create(Var) :-
  nb_setval(Var, 0).

%% Hulpfunctie: add/1
%
% Incrementeert een gegeven teller met 1
add(Var) :-
  nb_getval(totalC, T),
  TNew is T + 1,
  nb_setval(totalC, TNew),
  nb_getval(Var, C),
  CNew is C + 1,
  nb_setval(Var, CNew).

%% Hulpfunctie: get/2
%
% Haalt de waarde van een gegeven cellnaam op
get(Var, Res) :-
  nb_getval(Var, Res).

%% Hoofdfunctie: solve/1
%
% Neemt een sudoku van het volgende formaat:
% Sudoku ::= [Rij]
% Rij    ::= [Getal]
%
% Legt constraints op aan deze sudoku en laat
% Prolog een kloppende oplossing zoeken.
solve(Sudoku) :-

  % Creëert alle gebruikte variabelen
  create,

  % Increment de teller met 1
  add(solveC),

  % Voeg alle rijen samen via flatten/2, dit resultaat komt in AllDiff:
  flatten(Sudoku, AllDiff),
  % Via de ins/1 kunnen we eisen dat alle variabelen in de range [1..9] zitten:
  AllDiff ins 1..9,

  % Via maplist/2 mappen we de functie all_distinct op elke rij: geen enkele rij mag dus 2x dezelfde waarde bevatten:
  maplist(all_distinct, Sudoku),

  % Door de rijen te transponeren krijgen we de kolommen:
  transpose(Sudoku, Columns),
  % Idem zoals bij de rijen willen we dat geen enkele kolom 2x dezelfde waarde bevat:
  maplist(all_distinct, Columns),

  % Nu eisen we nog dat de blokken verschillende waarden hebben volgens de blocks hulpfunctie:
  all_blocks_distinct(Sudoku),

  % We moeten ook nog eisen dat elke cel wel degelijk is ingevuld:
  maplist(label, Sudoku),

  % Pretty print the sudoku:
  prettyPrint(Sudoku).


%% Hulpfunctie: all_blocks_distinct/1
%
% Neemt als input een Sudoku en splitst resursief de rijen in paren
% van 3 in 3. Deze worden bloksgewijs geconcateneerd en daarna eisen
% we dat de inhoud van de blokken distinct is.
%
% Maakt gebruik van split_in_three/4
all_blocks_distinct([]) :-
  add(all_blocks_distinctC).
all_blocks_distinct([R1, R2, R3|Rx]) :-
  add(all_blocks_distinctC),
  split_in_three(R1, A1, A2, A3),
  split_in_three(R2, B1, B2, B3),
  split_in_three(R3, C1, C2, C3),
  flatten([A1, B1, C1], L1),
  all_distinct(L1),
  flatten([A2, B2, C2], L2),
  all_distinct(L2),
  flatten([A3, B3, C3], L3),
  all_distinct(L3),
  all_blocks_distinct(Rx).

%% Hulpfunctie: split_in_three/4
%
% Neemt als input een lijst en geeft 3 lijsten terug.
% Deze 3 lijsten zijn de originele lijst in 3 stukken
% van lengte 3 gesplitst.
split_in_three(L, A, B, C) :-
    add(split_in_threeC),
    length(A, 3),
    append(A, AOverschot, L),
    length(B, 3),
    append(B, C, AOverschot).

%% Hulpfunctie: prettyPrint/1
%
% Neemt als input een Sudoku en print deze mooi uit
%
% Maakt gebruik van prettyPrintRows/2
prettyPrint(Sudoku) :-
  add(prettyPrintC),
  print('╔═══════╤═══════╤═══════╗'), nl,
  prettyPrintRows(Sudoku, 3),
  print('╚═══════╧═══════╧═══════╝'), nl,
  printCounters.

%% Hulpfunctie: prettyPrint/1
%
% Neemt als input een Sudoku en print deze mooi uit.
%
% Maakt gebruik van de prettyPrintRow/1 hulpfunctie.
prettyPrintRows([], _) :-
  !,
  add(prettyPrintRowsC).
prettyPrintRows(Rx, 0) :-
  !,
  add(prettyPrintRowsC),
  print('╟───────┼───────┼───────╢'), nl,
  prettyPrintRows(Rx, 3).
prettyPrintRows([R1|Rx], C) :-
  !,
  add(prettyPrintRowsC),
  Cn is C-1,
  print('║ '),
  prettyPrintRow(R1, 3),
  nl,
  prettyPrintRows(Rx, Cn).

%% Hulpfunctie: prettyPrintRow/1
%
% Neemt als input een Sudokurij en print deze mooi uit.
prettyPrintRow([], _) :-
  !,
  add(prettyPrintRowC),
  print('║').
prettyPrintRow(Cx, 0) :-
  !,
  add(prettyPrintRowC),
  print('│ '),
  prettyPrintRow(Cx, 3).
prettyPrintRow([C1|Cx], C) :-
  !,
  add(prettyPrintRowC),
  Cn is C-1,
  write(C1),
  write(' '),
  prettyPrintRow(Cx, Cn).

%% Hulpfunctie: printCounters/0
%
% Print alle tellers uit
printCounters :-
  nb_getval(solveC, SolveRes),
  write('#solve calls: '), write(SolveRes), nl,
  nb_getval(all_blocks_distinctC, All_blocks_distinctRes),
  write('#all_blocks_distinct calls: '), write(All_blocks_distinctRes), nl,
  nb_getval(split_in_threeC, Split_in_threeRes),
  write('#split_in_three calls: '), write(Split_in_threeRes), nl,
  nb_getval(prettyPrintC, PrettyPrintRes),
  write('#prettyPrint calls: '), write(PrettyPrintRes), nl,
  nb_getval(prettyPrintRowsC, PrettyPrintRowsRes),
  write('#prettyPrintRows calls: '), write(PrettyPrintRowsRes), nl,
  nb_getval(prettyPrintRowC, PrettyPrintRowRes),
  write('#prettyPrintRow calls: '), write(PrettyPrintRowRes), nl,
  nb_getval(totalC, TotalRes),
  write('Total # calls: '), write(TotalRes).

%% Testfunctie:
%
% Lost de voorbeeldsudoku op
solveExample :-
  Sudoku = [[_,_,_,_,1,3,5,_,_],
            [_,_,_,6,_,7,_,_,_],
            [_,_,_,_,_,_,2,_,1],
            [_,9,_,_,_,_,_,6,5],
            [5,_,_,_,_,_,_,_,7],
            [2,8,_,_,_,_,_,9,_],
            [6,_,7,_,_,_,_,_,_],
            [_,_,_,7,_,9,_,_,_],
            [_,_,4,8,2,_,_,_,_]],
  solve(Sudoku).

%% Generatiefunctie:
%
% Genereert een volledige sudoku
generateSudoku :-
  Sudoku = [[_,_,_,_,_,_,_,_,_],
            [_,_,_,_,_,_,_,_,_],
            [_,_,_,_,_,_,_,_,_],
            [_,_,_,_,_,_,_,_,_],
            [_,_,_,_,_,_,_,_,_],
            [_,_,_,_,_,_,_,_,_],
            [_,_,_,_,_,_,_,_,_],
            [_,_,_,_,_,_,_,_,_],
            [_,_,_,_,_,_,_,_,_]],
  solve(Sudoku).
