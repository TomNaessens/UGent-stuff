%%% Project Programmeertalen: Assignment 1, deel 1
%%% Schrijven van een declaratieve Sudokusolver
%
% Author: Tom Naessens
%
% Uitvoering:
% * Start swiprolog
% * Laad dit bestand in via ['Assigment1.1.pl'].
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

%% Hoofdfunctie: solve/1
%
% Neemt een sudoku van het volgende formaat:
% Sudoku ::= [Rij]
% Rij    ::= [Getal]
% Getal  ::= _|1..9
%
% Legt constraints op aan deze sudoku en laat
% Prolog een kloppende oplossing zoeken.
solve(Sudoku) :-

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
all_blocks_distinct([]).
all_blocks_distinct([R1, R2, R3|Rx]) :-
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
  print('╔═══════╤═══════╤═══════╗'), nl,
  prettyPrintRows(Sudoku, 3),
  print('╚═══════╧═══════╧═══════╝'), nl.

%% Hulpfunctie: prettyPrint/1
%
% Neemt als input een Sudoku en print deze mooi uit.
%
% Maakt gebruik van de prettyPrintRow/1 hulpfunctie.
prettyPrintRows([], _) :-
  !.
prettyPrintRows(Rx, 0) :-
  !,
  print('╟───────┼───────┼───────╢'), nl,
  prettyPrintRows(Rx, 3).
prettyPrintRows([R1|Rx], C) :-
  !,
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
  print('║').
prettyPrintRow(Cx, 0) :-
  !,
  print('│ '),
  prettyPrintRow(Cx, 3).
prettyPrintRow([C1|Cx], C) :-
  !,
  Cn is C-1,
  write(C1),
  write(' '),
  prettyPrintRow(Cx, Cn).

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
