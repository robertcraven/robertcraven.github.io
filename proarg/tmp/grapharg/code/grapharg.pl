
% FILE:         grapharg.pl
% AUTHOR:       Robert Craven [robert.craven@imperial.ac.uk]
% LANGUAGE:     Prolog
% DATE:         5/7/2012

% variable naming conventions for the Prolog are:
%
%  A...         assumptions
%  J...         justifications
%  O...         opponent justification clusters
%  P...         proponent sentences
%  S...         sentences
%  SJ...        sentences-justifications pairs
%  T...         tuples

% possible strategies are:
%  turn choice:
%     p - proponent priority [DEFAULT]
%     o - opponent priority
%     s - smallest number of arguments/justification pairs first
%  opponent sj-pair choice:
%     n - newest
%     o - oldest
%     s - smallest set of pending (unmarked) sentences [DEFAULT]
%     l - largest set of pending (unmarked) sentences
%   lmb - lowest maximum branching coefficient
%  sentence choice (Proponent and Opponent):
%     n - newest
%     o - oldest
%     e - eager (choose an assumption if possible)
%     p - patient (choose a non-assumption if possible)  [DEFAULT (prop and opp)]
%    be - sentence with smallest 'branching' coefficient (eager)
%    bp - sentence with smallest 'branching' coefficient (patient)
%  proponent rule choice
%     s - smallest rule body first
%    l1 - look-ahead, 1-step  [DEFAULT]

% TODO:
%
% - improved heuristics (dynamic, too)
% - improved structure for opponent derivations

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% PRELIMINARIES

:- use_module(library(samsort),  [samsort/3]).
:- use_module(library(lists),    [delete/3,remove_dups/2,select/3]).
:- use_module(library(ordsets),  [list_to_ord_set/2,ord_add_element/3,ord_union/3]).
:- use_module(library(ugraphs),  [add_edges/3,reduce/2]).        % for acyclicity check

:- [printing].
:- [help].
:- [extras].

:- dynamic
 assumption/1,
 branching/2,   % used in some of the heuristics
 contrary/2,
 filestem/1,
 non_assumption/1,
 option/2,
 proving/1,
 rule/3,
 rule_counter/1,
 toBeProved/1,
 user_predicate/2.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% OPTIONS and HELP

% OPTIONS: generic

option(derivation_type, ab).
option(fileID, '_sol_').
option(num_sols, 0).    % all solutions
option(opponent_sjpair_choice, s).
option(opponent_sentence_choice, p).
option(print_to_file, fail).
option(proponent_sentence_choice, p).
option(proponent_rule_choice, l1).
option(show_solution, true).
option(turn_choice, p).
option(verbose, fail).

set_opt(Option, Value) :-
 retractall(option(Option,_)),
 assert(option(Option, Value)).

options :-
 option(Opt, Val),
 format('~w = ~w~n', [Opt,Val]),
 fail.
options.

% OPTIONS: setting

set_ab :-
 set_derivation(ab).
set_gb :-
 set_derivation(gb).

set_derivation(Type) :-
 set_opt(derivation_type, Type).

set_strategies([TurnChoice,OppJust,Prop,Opp,PropRule]) :-
 set_opt(turn_choice, TurnChoice),
 set_opt(opponent_sjpair_choice, OppJust),
 set_opt(proponent_sentence_choice, Prop),
 set_opt(opponent_sentence_choice, Opp),
 set_opt(proponent_rule_choice, PropRule).

set_print :-
 set_opt(print_to_file, true).
set_noprint :-
 set_opt(print_to_file, fail).

set_verbose :-
 set_opt(verbose, true).
set_quiet :-
 set_opt(verbose, fail).

set_show :-
 set_opt(show_solution, true).
set_noshow :-
 set_opt(show_solution, fail).

% OPTIONS: checking

ab_derivation :-
 option(derivation_type, ab).
gb_derivation :-
 option(derivation_type, gb).
ib_derivation :-
 option(derivation_type, ib).

verbose :-
 option(verbose, Verbose),
 Verbose.

% OPTIONS: set some on loading (will be overridden if 'proxdd' script used)

:-
 source_file(X),
 (
  atom_concat(Path, 'code/printing.pl', X)
  -> atom_concat(Path, 'data/', FrameworkDir),
     set_opt(frameworkdir, FrameworkDir)
 ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% LOADING

loadf(FileStem) :-
 preloading,
 filename(FileStem, FileName),
 assert(filestem(FileStem)),
 open(FileName, read, Fd),
 repeat,
  read(Fd, Term),
  process_fail(Term),
 !,
 close(Fd),
 postloading.

preloading :-
 user_predicate(Func, Arity),
 abolish(Func, Arity),
 fail.
preloading :-
 retractall(assumption(_)),
 retractall(branching(_,_)),
 retractall(contrary(_,_)),
 retractall(filestem(_)),
 retractall(non_assumption(_)),
 retractall(proving(_)),
 retractall(rule(_,_,_)),
 retractall(rule_counter(_)),
 retractall(sols(_)),
 retractall(toBeProved(_)),
 retractall(user_predicate(_,_)),
 assert(rule_counter(1)).

filename(FileStem, DirAndFileName) :-
 option(frameworkdir, Dir),
 atom_concat(FileStem, '.pl', FileName),
 atom_concat(Dir, FileName, DirAndFileName).

process_fail(end_of_file) :-
 !.
process_fail(:-(Body)) :-
 !,
 call(Body),
 fail.
process_fail(:-(Head, Body)) :-
 !,
 (
  input_predicate(Head, StoreHead)
  -> (
      StoreHead = rule(_,RC,_)
      -> rule_counter(RC),
         incr_rule_counter
      ;  true
     )
  ;  functor(Head, Func, Arity),
     (
      user_predicate(Func, Arity)
      -> true
      ;  assert(user_predicate(Func, Arity)) 
     ),
     StoreHead = Head
 ),
 assert(:-(StoreHead,Body)),
 fail.
process_fail(Head) :-
 process_fail(:-(Head,true)).

input_predicate(assumption(X), assumption(X)).
input_predicate(contrary(A,S), contrary(A,S)).
input_predicate(myAsm(A), assumption(A)).
input_predicate(myRule(H,B), rule(H,_,B)).
input_predicate(rule(H,B), rule(H,_,B)).
input_predicate(toBeProved(TBP), toBeProved(TBP)).

incr_rule_counter :-
 rule_counter(RC),
 RC1 is RC + 1,
 retractall(rule_counter(_)),
 assert(rule_counter(RC1)).

postloading :-
 non_assumptions,
 check_input,
 branchings.

non_assumptions :-
 findall(S, ((
              rule(H, _, Body),
              member(S, [H|Body])
              ;
              contrary(_, S)
             ),
             \+ assumption(S)
            ),
          NonAssumptions),
 list_to_ord_set(NonAssumptions, O_NonAssumptions),
 member(S, O_NonAssumptions),
 assert(non_assumption(S)),
 fail.
non_assumptions.

% checks are:
%  - every assumption has a contrary
%  - no assumption is head of a rule
%  - every contrary is of an assumption
%  - there is at least one assumption
check_input :-
 findall(A, assumption(A), Asms),
 findall(A, (assumption(A), \+ contrary(A, _)), As),
 findall((S,C), (contrary(S,C), \+ assumption(S)), ContPairs),
 findall(A, (rule(A, _, _), assumption(A)), Hs),
 list_to_ord_set(As, O_As),
 list_to_ord_set(Hs, O_Hs),
 list_to_ord_set(ContPairs, O_ContPairs),
 (
  Asms = [],
  format('ERROR: no assumptions~n', []),
  fail
  ;
  member(A, O_As),
  format('ERROR: ~w declared an assumption without contrary~n', [A]),
  fail
  ;
  member((S,C), O_ContPairs),
  format('ERROR: ~w declared as contrary of ~w, which is not an assumption~n', [C,S]),
  fail
  ;
  member(A, O_Hs),
  format('ERROR: ~w head of a rule but declared an assumption~n', [A]),
  fail
 ).
check_input :-
 flush_output.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% DERIVATION CONTROL: entry predicates

% 3 ARGUMENTS
derive(S, [TurnChoice,OppJust,Prop,Opp,PropRule], NumSols) :-
 number(NumSols),
 !,
 set_strategies([TurnChoice,OppJust,Prop,Opp,PropRule]),
 derive_novar(S, NumSols).

derive(S, [TurnChoice,OppJust,Prop,Opp,PropRule], Result) :-
 set_strategies([TurnChoice,OppJust,Prop,Opp,PropRule]),
 derive(S, Result).

% 2 ARGUMENTS
derive([TurnChoice,OppJust,Prop,Opp,PropRule], NumSols) :-
 number(NumSols),
 !,
 (
  toBeProved([S])
  -> set_strategies([TurnChoice,OppJust,Prop,Opp,PropRule]),
     derive_novar(S, NumSols)
  ;  format('No fact toBeProved/1; supply a sentence~n', [])
 ).

derive([TurnChoice,OppJust,Prop,Opp,PropRule], Result) :-
 !,
 (
  toBeProved([S])
  -> set_strategies([TurnChoice,OppJust,Prop,Opp,PropRule]),
     derive(S, Result)
  ;  format('No fact toBeProved/1; supply a sentence~n', [])
 ).

derive(S, Result) :-
 (
  assumption(S)
  -> D0 = [S]
  ;  D0 = []
 ),
 retractall(proving(_)),
 assert(proving(S)),
 (
  verbose
  -> print_step(0, [[S],[],D0,[],[],[],[],[]])
  ;  true
 ),
 retractall(sols(_)),
 assert(sols(1)),
 derivation([[S],[],D0,[],[],[],[],[]], 1, Result),
 print_result(Result),
 incr_sols.

derive_all(S) :-
 derive(S, _),
 fail.
derive_all(_).

% 1 ARGUMENT
derive(NumSols) :-
 number(NumSols),
 !,
 (
  toBeProved([S])
  -> derive_novar(S, NumSols)
  ;  format('No fact toBeProved/1; supply a sentence~n', [])
 ).

derive(Result) :-
 toBeProved([S]),
 !,
 derive(S, Result).
derive(_Result) :-
 format('No fact toBeProved/1; supply a sentence.~n', []),
 fail.

%

derive_all(Ss, Result) :-
 findall(A, (member(A, Ss),
             assumption(A)), D0),
 retractall(proving(_)),
 \+ (member(S, Ss),
     \+ assert(proving(S))),
 (
  verbose
  -> print_step(0, [Ss,[],D0,[],[],[],[],[]])
  ;  true
 ),
 retractall(sols(_)),
 assert(sols(1)),
 derivation([Ss,[],D0,[],[],[],[],[]], 1, Result),
 print_result(Result),
 incr_sols.

%

derive_novar(S, NumSols) :- 
 (
  assumption(S)
  -> D0 = [S]
  ;  D0 = []
 ),
 retractall(proving(_)),
 assert(proving(S)),
 (
  verbose
  -> print_step(0, [[S],[],D0,[],[],[],[],[]])
  ;  true
 ),
 retractall(sols(_)),
 assert(sols(1)),
 repeat,
  derivation([[S],[],D0,[],[],[],[],[]], 1, Result),
  print_result(Result),
  (
   sols(NumSols)
   -> !
   ;  incr_sols,
      fail
  ),
 !.

incr_sols :-
 sols(N),
 retractall(sols(N)),
 N1 is N + 1,
 assert(sols(N1)).

% the following are used in 'script mode'

script_derive(S, [TurnChoice,OppJust,Prop,Opp,PropRule]) :-
 set_strategies([TurnChoice,OppJust,Prop,Opp,PropRule]),
 script_derive(S).
 
script_derive(S) :-
 (
  assumption(S)
  -> D0 = [S]
  ;  D0 = []
 ),
 retractall(proving(_)),
 assert(proving(S)),
 (
  derivation([[S],[],D0,[],[],[],[],[]], 1, _)
  -> format('solution~n', [])
  ;  true
 ).

script_derive_print(S, [TurnChoice,OppJust,Prop,Opp,PropRule]) :-
 set_strategies([TurnChoice,OppJust,Prop,Opp,PropRule]),
 script_derive_print(S).
 
script_derive_print(S) :-
 (
  assumption(S)
  -> D0 = [S]
  ;  D0 = []
 ),
 retractall(proving(_)),
 assert(proving(S)),
 (
  derivation([[S],[],D0,[],[],[],[],[]], 1, Result)
  -> print_result(Result)
  ;  format('No solution~n', [])
 ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% DERIVATION CONTROL: basic control structure

derivation([[],[]|Result], _, Result) :-
 !.
derivation(T, N, Result) :-
 derivation_step(T, T1),
 (
  verbose
  -> print_step(N, T1)
  ;  true
 ),
 N1 is N + 1,
 derivation(T1, N1, Result).

derivation_step([P,O|RestT], T1) :-
 choose_turn(P, O, Turn),
 (
  Turn = proponent
  -> proponent_step([P,O|RestT], T1)
  ;  opponent_step([P,O|RestT], T1)
 ).

proponent_step([P|RestT], T1) :-
 proponent_sentence_choice(P, S, Pminus),
 (
  assumption(S)
  -> proponent_i(S, Pminus, RestT, T1)
  ;  proponent_ii(S, Pminus, RestT, T1)
 ).

opponent_step([P,O|RestT], T1) :-
 opponent_sjpair_choice(O, SJ, Ominus),
 opponent_sentence_choice(SJ, S, SJminus),
 (
  assumption(S)
  -> opponent_i(S, SJminus, Ominus, [P|RestT], T1)
  ;  opponent_ii(S, SJminus, Ominus, [P|RestT], T1)
 ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% DERIVATION CASES

% proponent

proponent_i(A, Pminus, [O,D,C,JsP,JsO,Att,G], [Pminus,O1,D,C,JsP1,JsO,Att1,G1]) :-
 findall(Co, contrary(A, Co), Cs),
 findall([Co]-[]-[Co], (member(Co, Cs),
                        \+ member((Co,_), JsO)),
         NewCs),
 append_elements_nodup(NewCs, O, O1),
 ord_add_element(JsP, (A,*), JsP1),
 findall((Co,A), member(Co, Cs), NewAtts),
 list_to_ord_set(NewAtts, O_NewAtts),
 ord_union(Att, O_NewAtts, Att1),
 gb_acyclicity_check(G, A, Cs, G1),     % check this
 (
  verbose
  -> format('~nCase 1.(i)~n', [])
  ;  true
 ).

/*
 contrary(A, Contrary),
 (
  member((Contrary,_), JsO)
  -> O1 = O
  ;  append_element_nodup(O, [Contrary]-[]-[Contrary], O1)
 ),
 ord_add_element(JsP, (A,*), JsP1),
 ord_add_element(Att, (Contrary,A), Att1),
 gb_acyclicity_check(G, A, [Contrary], G1),
 (
  verbose
  -> format('~nCase 1.(i)~n', [])
  ;  true
 ).
*/

proponent_ii(S, Pminus, [O,D,C,JsP,JsO,Att,G], [P1,O,D1,C,JsP1,JsO,Att,G1]) :-
 (
  member((S,RuleID), JsP)
  -> rule(S, RuleID, Body)
  ;  rule_choice(S, RuleID, Body, proponent, [D,JsP])
 ),
 fDbyD(Body, D, NewP),
 append_elements_nodup(NewP, Pminus, P1),
 get_ord_assumptions(Body, BodyAs),
 ord_union(D, BodyAs, D1),
 ord_add_element(JsP, (S,RuleID), JsP1),
 gb_acyclicity_check(G, S, Body, G1),
 (
  verbose
  -> format('~nCase 1.(ii)~n', [])
  ;  true
 ).

% opponent

opponent_i(A, SJminus, Ominus, [P,D,C|RestT], T1) :-
 (
  \+ member(A, D),
  (
   fCbyC([A], C)
   -> opponent_ib(A, SJminus, Ominus, [P,D,C|RestT], T1)
   ;  opponent_ic(A, SJminus, Ominus, [P,D,C|RestT], T1)
  )
  ;
  opponent_ia(A, SJminus, Ominus, [P,D,C|RestT], T1) % we do ignore choice second, as with SXDD
 ).

% for this, if A \in C, shouldn't we fail?
% and what if A \in D?
% CHECK FOR AB/GB
opponent_ia(A, Ss-Js-Conc, Ominus, [P,D,C,JsP,JsO,Att,G], [P,O1,D,C,JsP,JsO,Att,G]) :-
 (
  ab_derivation         % also sound for gb?
  -> \+ member(A, C)
  ;  true
 ),
 ord_add_element(Js, (A,*), Js1),
 append_element_nodup(Ominus, Ss-Js1-Conc, O1),
 (
  verbose
  -> format('~nCase 2.(ia)~n', [])
  ;  true
 ).

opponent_ib(A, Ss-Js-Conc, Ominus, [P,D,C,JsP,JsO,Att,G], [P,Ominus,D,C,JsP,JsO1,Att,G]) :-
 ord_add_element(Js, (A,*), Js1),
 ord_add_element(JsO, Ss-Js1-Conc, JsO1),
 (
  verbose
  -> format('~nCase 2.(ib)~n', [])
  ;  true
 ).

opponent_ic(A, Ss-Js-Conc, Ominus, [P,D,C,JsP,JsO,Att,G], [P1,Ominus,D1,C1,JsP,JsO1,Att1,G1]) :-
 contrary(A, Contrary),
 (
  member((Contrary,_), JsP)
  -> P1 = P             % additional filtering
  ;  append_element_nodup(P, Contrary, P1)   
 ),
 (
  assumption(Contrary)
  -> ord_add_element(D, Contrary, D1)
  ;  D1 = D
 ),
 ord_add_element(C, A, C1),
 ord_add_element(Js, (A,*), Js1),
 ord_add_element(JsO, Ss-Js1-Conc, JsO1),
 ord_add_element(Att, (Contrary,A), Att1),
 gb_acyclicity_check(G, A, [Contrary], G1),
 (
  verbose
  -> format('~nCase 2.(ic)~n', [])
  ;  true
 ).

opponent_ii(S, Ss-Js-Conc, Ominus, [P,D,C,JsP,JsO,Att,G], [P,O1,D,C,JsP,JsO1,Att,G1]) :-
 (
  member((S,RuleID), Js)                % check whether S has already been (partly) justified
  -> rule(S, RuleID, Body),
     append_elements_nodup(Ss, Body, Ss1), % CHECK THIS: why not Ss1 = Ss?
     append_element_nodup(Ominus, Ss1-Js-Conc, O1),
     JsO1 = JsO,
     G1 = G                             % acyclicity check will already have been done
  ;  findall((Body,RuleID), rule(S, RuleID, Body), BodiesIDs),
     split_fCbyC(BodiesIDs, C, Sf, Snf),
     get_new_just_clusters(Snf, Ss-Js-Conc, S, JCs),
     remove_dups(JCs, NoDupsJCs),
     append_elements_nodup(Ominus, NoDupsJCs, O1),
     update_opponent_jcs(Sf, C, S, Ss-Js-Conc, NewJs),
     append_elements_nodup(JsO, NewJs, JsO1),
     flatten_bodyids(BodiesIDs, [], AllBody),
     gb_acyclicity_check(G, S, AllBody, G1)
 ),
 (
  verbose
  -> format('~nCase 2.(ii)~n', [])
  ;  true
 ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% SUBSIDIARY FUNCTIONS

% get_ord_assumptions(Ss, As)
% - As is the ordered set of assumptions in Ss
get_ord_assumptions(Ss, As) :-
 get_ord_assumptions(Ss, [], As).
% - same, with accumulator
get_ord_assumptions([], As, As).
get_ord_assumptions([A|Ss], InAs, As) :-
 assumption(A),
 !,
 ord_add_element(InAs, A, OutAs),
 get_ord_assumptions(Ss, OutAs, As).
get_ord_assumptions([_|Ss], InAs, As) :-
 get_ord_assumptions(Ss, InAs, As).

% get_new_just_clusters(BodyIDs, InSJs, S, OutSJs)
get_new_just_clusters([], _, _, []).
get_new_just_clusters([(Body,RuleID)|RestBodiesIds], Ss-Js-Conc, S, [Ss1-Js1-Conc|RestSJs]) :-
 append_elements_nodup(Ss, Body, Ss1),
 ord_add_element(Js, (S,RuleID), Js1),
 get_new_just_clusters(RestBodiesIds, Ss-Js-Conc, S, RestSJs).

% subtract(X, Y, Z)
% - Z is the list of members of Y not in X
subtract([], X, X).
subtract([H|T], InList, Result) :-
 delete(InList, H, OutList),
 subtract(T, OutList, Result).

% append_element_nodup(L, E, Res)
% - Res is the result of adding E to the end of L, if E is not in L
% - otherwise, Res is L
append_element_nodup([], Element, [Element]).
append_element_nodup([Element|Rest], Element, [Element|Rest]) :-
 !.
append_element_nodup([H|T], Element, [H|Rest]) :-
 append_element_nodup(T, Element, Rest).

% append_elements_nodup(Es, L, Res)
% - Res is the result of adding all members of Es not already in L
%   to the end of L
append_elements_nodup([], Result, Result).
append_elements_nodup([Element|Elements], InList, Result) :-
 append_element_nodup(InList, Element, OutList),
 append_elements_nodup(Elements, OutList, Result).

% split_fCbyC(Pairs, C, Sf, Snf)
% - divide a list of Pairs of form (Body,RuleID) according to
%   fCbyC filter using C
split_fCbyC([], _, [], []).
split_fCbyC([(Body,RuleID)|Rest], C, [(Body,RuleID)|RestSf], Snf) :-
 fCbyC(Body, C),
 !,
 split_fCbyC(Rest, C, RestSf, Snf).
split_fCbyC([(Body,RuleID)|Rest], C, Sf, [(Body,RuleID)|RestSnf]) :-
 split_fCbyC(Rest, C, Sf, RestSnf).

% gb_acyclicity_check(G, To, FromList, G1)
% - add the list of edges from members of FromList to To, to the
%   unweighted directed graph G, to form G1; check to
%   see if the result is acyclic
gb_acyclicity_check(G, To, FromList, G1) :-
 (
  gb_derivation
  -> findall(From-To, member(From, FromList), NewEdges),
     add_edges(G, NewEdges, G1),
     acyclic(G1)
  ;  G1 = G
 ).

% acyclic(G)
% - true when G is an acyclic ugraph
acyclic(G) :-
 reduce(G, RedG),
 \+ member([_,_|_]-_, RedG).

% update_opponent_jcs(Sf, C, S, Ss-Js-Conc, NewJs)
update_opponent_jcs([], _, _, _, []).
update_opponent_jcs([(Body,RuleID)|RestSf], C, S, Ss-Js-Conc, [Ss1-Js2-Conc|RestJCs]) :-
 split_rulebody_culprits(Body, C, InCulprits, NonCulprits),
 append_elements_nodup(NonCulprits, Ss, Ss1),
 ord_union(InCulprits, Js, Js1),
 ord_add_element(Js1, (S,RuleID), Js2),
 update_opponent_jcs(RestSf, C, S, Ss-Js-Conc, RestJCs).

% split_rulebody_culprits(RuleBody, Culprits, InCulprits, NonCulprits)
split_rulebody_culprits([], _, [], []).
split_rulebody_culprits([A|RestBody], C, [(A,*)|RestInCulprits], NonCulprits) :-
 member(A, C),
 !,
 split_rulebody_culprits(RestBody, C, RestInCulprits, NonCulprits).
split_rulebody_culprits([S|RestBody], C, InCulprits, [S|RestNonCulprits]) :-
 split_rulebody_culprits(RestBody, C, InCulprits, RestNonCulprits).

% flatten_bodyids(BodyIds, In, AllBody)
% - true when AllBody is the ordered union of all sentences from
%   bodies in BodyIds with sentences in In
flatten_bodyids([], AllBody, AllBody).
flatten_bodyids([(Body,_)|Rest], In, AllBody) :-
 ord_union(Body, In, Out),
 flatten_bodyids(Rest, Out, AllBody).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% SELECTION FUNCTIONS

choose_turn([], _, opponent) :-
 !.
choose_turn(_, [], proponent) :-
 !.
choose_turn(P, O, Player) :-
 option(turn_choice, TurnStrategy),
 turn_choice(TurnStrategy, P, O, Player).

proponent_sentence_choice(P, S, Pminus) :-
 option(proponent_sentence_choice, PropSentenceStrategy),
 sentence_choice(PropSentenceStrategy, P, S, Pminus),
 !.

opponent_sjpair_choice(O, JC, Ominus) :-
 option(opponent_sjpair_choice, OppJCStrategy),
 opponent_sjpair_choice(OppJCStrategy, O, JC, Ominus),
 !.

opponent_sentence_choice(Ss-Js-Conc, Se, Ssminus-Js-Conc) :-
 option(opponent_sentence_choice, OppSentenceStrategy),
 sentence_choice(OppSentenceStrategy, Ss, Se, Ssminus),
 !.

% PropInfo here holds information about the current state of
% proponent's derivations
rule_choice(Head, RuleID, Body, proponent, PropInfo) :-
 findall((ID,B), rule(Head, ID, B), RulePairs),
 option(proponent_rule_choice, PropRuleStrategy),
 sort_rule_pairs(PropRuleStrategy, PropInfo, RulePairs, SortedRulePairs),
 !,
 member((RuleID,Body), SortedRulePairs).

%

turn_choice(p, _, _, proponent).
turn_choice(o, _, _, opponent).
turn_choice(s, P, O, Player) :-
 length(P, PN),
 length(O, ON),
 (
  PN =< ON
  -> Player = proponent
  ;  Player = opponent
 ).

%

sentence_choice(o, [S|Ssminus], S, Ssminus).
sentence_choice(n, Ss, S, Ssminus) :-
 append(Ssminus, [S], Ss).
sentence_choice(e, Ss, S, Ssminus) :-
 get_first_assumption_or_other(Ss, S, Ssminus).
sentence_choice(p, Ss, S, Ssminus) :-
 get_first_nonassumption_or_other(Ss, S, Ssminus).
sentence_choice(be, Ss, S, Ssminus) :-
 get_smallest_branching(Ss, S, Ssminus, eager).
sentence_choice(bp, Ss, S, Ssminus) :-
 get_smallest_branching(Ss, S, Ssminus, patient).

% the rule for the 'smallest branching' is:
%  - if the sentence is a non-assumption, then its branching coefficient
%    is the number of rules having the sentence as their head
%  - if the sentence is an assumption, then the branching coefficient
%    is found by moving along the 'conrary' relation of the sentence,
%    until a non-assumption is found; the coefficient is then the
%    the number of rules having that non-assumption as their head
%  - we find the set of sentences having the smallest branching
%    coefficient by this definition; then for a 'patient' (bp)
%    selection function, we pick a non-assumption if possible;
%    for an 'eager' selection function, we pick an assumption
%    if possible

get_smallest_branching([S|Ss], Selected, Ssminus, Type) :-
 branching(S, N),
 get_branchings(Ss, N, [S], [B|Bs]),
 (
  (  (assumption(B), Type = eager)
   ; (\+ assumption(B), Type = patient))
  -> Selected = B
  ;  get_type(Bs, Type, B, Selected)
 ),
 delete([S|Ss], Selected, Ssminus).

get_branchings([], _, Best, Best).
get_branchings([S|Ss], BestN, BestSoFar, BestFinal) :-
 branching(S, N),
 (
  N < BestN
  -> NewBestN = N,
     NewBest = [S]
  ;
  N = BestN
  -> NewBestN = BestN,
     append(BestSoFar, [S], NewBest)
  ;
  % N > BestN
     NewBestN = BestN,
     NewBest = BestSoFar
 ),
 get_branchings(Ss, NewBestN, NewBest, BestFinal).

%get_branching_coefficient(S, N) :-
% get_contrary_terminus(S, NonAss),
% findall(B, rule(NonAss, _, B), Bs),
% length(Bs, N).

get_contrary_terminus(S, S) :-
 \+ assumption(S),
 !.
get_contrary_terminus(A, S) :-
 contrary(A, C),
 get_contrary_terminus(C, S).

get_type([], _, S, S).
get_type([S|Ss], eager, BestSoFar, Best) :-
 (
  assumption(S)
  -> Best = S
  ;  get_type(Ss, eager, BestSoFar, Best)
 ).
get_type([S|Ss], patient, BestSoFar, Best) :-
 (
  \+ assumption(S)
  -> Best = S
  ;  get_type(Ss, patient, BestSoFar, Best)
 ).

%

opponent_sjpair_choice(o, [JC|Ominus], JC, Ominus).
opponent_sjpair_choice(n, O, JC, Ominus) :-
 append(Ominus, [JC], O).
opponent_sjpair_choice(s, [Ss-Js-Conc|RestJCs], JC, Ominus) :-
 length(Ss, L),
 get_smallest_ss(RestJCs, L, Ss-Js-Conc, JC),
 delete([Ss-Js-Conc|RestJCs], JC, Ominus).
opponent_sjpair_choice(l, [Ss-Js-Conc|RestJCs], JC, Ominus) :-
 length(Ss, L),
 get_largest_ss(RestJCs, L, Ss-Js-Conc, JC),
 delete([Ss-Js-Conc|RestJCs], JC, Ominus).
opponent_sjpair_choice(lmb, [Ss-Js-Conc|RestJCs], JC, Ominus) :-
 maximum_branching(Ss, MB),
 get_lowest_maximum_branching(RestJCs, MB, Ss-Js-Conc, JC),
 delete([Ss-Js-Conc|RestJCs], JC, Ominus).

get_smallest_ss([], _, JC, JC).
get_smallest_ss([Ss-Js-Conc|RestJCs], BestLSoFar, BestJCSoFar, BestJC) :-
 length(Ss, L), % if L = 1, could we stop?
 (
  L < BestLSoFar
  -> NewL = L,
     NewJC = Ss-Js-Conc
  ;  NewL = BestLSoFar,
     NewJC = BestJCSoFar
 ),
 get_smallest_ss(RestJCs, NewL, NewJC, BestJC).

get_largest_ss([], _, JC, JC).
get_largest_ss([Ss-Js-Conc|RestJCs], BestLSoFar, BestJCSoFar, BestJC) :-
 length(Ss, L),
 (
  L > BestLSoFar
  -> NewL = L,
     NewJC = Ss-Js-Conc
  ;  NewL = BestLSoFar,
     NewJC = BestJCSoFar
 ),
 get_largest_ss(RestJCs, NewL, NewJC, BestJC).

get_lowest_maximum_branching([], _, JC, JC).
get_lowest_maximum_branching([Ss-Js-Conc|RestJCs], BestMBSoFar, BestJCSoFar, BestJC) :-
 maximum_branching(Ss, MB),
 (
  MB < BestMBSoFar
  -> NewMB = MB,
     NewJC = Ss-Js-Conc
  ;  NewMB = BestMBSoFar,
     NewJC = BestJCSoFar
 ),
 get_lowest_maximum_branching(RestJCs, NewMB, NewJC, BestJC).

% helpers

get_first_assumption_or_other(Ss, A, Ssminus) :-
 select(A, Ss, Ssminus),
 assumption(A),
 !.
get_first_assumption_or_other([A|Ssminus], A, Ssminus).

get_first_nonassumption_or_other(Ss, A, Ssminus) :-
 select(A, Ss, Ssminus),
 \+ assumption(A),
 !.
get_first_nonassumption_or_other([A|Ssminus], A, Ssminus).

maximum_branching([S|Ss], MB) :-
 branching(S, B),
 maximum_branching(Ss, B, MB).

maximum_branching([], MB, MB).
maximum_branching([S|Ss], InMB, MB) :-
 branching(S, B),
 (
  B > InMB
  -> OutMB = B
  ;  OutMB = InMB
 ),
 maximum_branching(Ss, OutMB, MB).

% rule sorting

sort_rule_pairs(s, _PropInfo, Pairs, SortedPairs) :-
 samsort(rule_sort_small_bodies, Pairs, SortedPairs).
sort_rule_pairs(l1, PropInfo, Pairs, SortedPairs) :-
 samsort(rule_sort_look_ahead_1(PropInfo), Pairs, SortedPairs).

rule_sort_small_bodies((_,Body1), (_,Body2)) :-
 length(Body1, L1),
 length(Body2, L2),
 L1 =< L2.

% here we minimize (Body - (D \cup JsP))
rule_sort_look_ahead_1([D,JsP], (_,Body1), (_,Body2)) :-
 count_nonD_nonJsP(Body1, D, JsP, 0, NB1),
 count_nonD_nonJsP(Body2, D, JsP, 0, NB2),
 NB1 =< NB2.

count_nonD_nonJsP([], _, _, N, N).
count_nonD_nonJsP([S|Rest], D, JsP, N, NB) :-
 \+ member(S, D),
 \+ member((S,_), JsP),
 !,
 N1 is N + 1,
 count_nonD_nonJsP(Rest, D, JsP, N1, NB).
count_nonD_nonJsP([_|Rest], D, JsP, N, NB) :-
 count_nonD_nonJsP(Rest, D, JsP, N, NB).

% BRANCHING: done on loading an ABA framework
branchings :-
 assumption(A),
 \+ branching(A, _),
 get_contrary_list(A, [A], List, Branching),
 assert_branchings(List, Branching),
 fail.
branchings :-
 non_assumption(S),
 \+ branching(S, _),
 non_assumption_branching(S, Branching),
 assert(branching(S, Branching)),
 fail.
branchings.

assert_branchings([], _).
assert_branchings([S|Rest], Branching) :-
 assert(branching(S, Branching)),
 assert_branchings(Rest, Branching).

get_contrary_list(S, List, List, Branching) :-
 branching(S, Branching),
 !.
get_contrary_list(S, List, List, Branching) :-
 non_assumption(S),
 !,
 non_assumption_branching(S, Branching).
get_contrary_list(A, InList, List, Branching) :-
 contrary(A, S),
 (
  member(S, InList)
  -> List = InList,
     Branching = 1
  ;  OutList = [S|InList],
     get_contrary_list(S, OutList, List, Branching)
 ).

/*
% previous calls:
%   get_contrary_list(A, List, Branching),
%   assert_branchings([A|List], Branching),

get_contrary_list(S, [], Branching) :-
 branching(S, Branching),
 !.
get_contrary_list(S, [], Branching) :-
 non_assumption(S),
 !,
 non_assumption_branching(S, Branching).
get_contrary_list(A, [S|Rest], Branching) :-
 contrary(A, S),
 get_contrary_list(S, Rest, Branching).
*/

% S must be a non-assumption
non_assumption_branching(S, Branching) :-
 findall(B, rule(S, _, B), Bs),
 length(Bs, Branching).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% FILTERING

fDbyD(R, D, NewP) :-
 (
  ab_derivation
  -> subtract(D, R, NewP)
  ;
  gb_derivation
  -> NewP = R
 ).

fCbyC(L, C) :-
 \+ gb_derivation,
 member(E, L),
 member(E, C),
 !.

