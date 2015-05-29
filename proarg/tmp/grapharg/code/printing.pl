
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% PRINTING: DERIVATION STEPS

print_step(N, [P,O,D,C,JsP,JsO,Att,G]) :-
 format('*** Step ~w~n', [N]),
 format('P:    [', []),
 print_step_list(P),
 format('O:    [', []),
 print_step_list(O),
 format('D:    [', []),
 print_step_list(D),
 format('C:    [', []),
 print_step_list(C),
 format('JsP:  [', []),
 print_step_list_brackets(JsP),
 format('JsO:  [', []),
 print_step_list(JsO),
 format('Att:  [', []),
 print_step_list_brackets(Att),
 format('G:    [', []),
 print_step_list_brackets(G).

print_step_list([]) :-
 format(']~n', []).
print_step_list([X]) :-
 !,
 format('~w]~n', [X]).
print_step_list([H|T]) :-
 format('~w,~n       ', [H]),
 print_step_list(T).

print_step_list_brackets([]) :-
 format(']~n', []).
print_step_list_brackets([X]) :-
 !,
 format('(~w)]~n', [X]).
print_step_list_brackets([H|T]) :-
 format('(~w),~n       ', [H]),
 print_step_list_brackets(T).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% PRINTING: RESULTS

show_result([D,C,JsP,JsO,Att,G]) :-
 format('~nDEFENCE:             ~w~n', [D]),
 format('CULPRITS:            ~w~n', [C]),
 format('PROP JUSTIFICATIONS: ~w~n', [JsP]),
 format('OPP JUSTIFICATIONS:  ~w~n', [JsO]),
 format('ATTACKS:             ~w~n', [Att]),
 format('GRAPH:               ~w~n', [G]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% PRINTING: PRINT TO FILE

graph_colour(background,                        '#FFFFFF').

graph_colour(proponent_justifications,          '#A2DDF3').
graph_colour(proponent_asm_toBeProved,          '#7C0AA2').
graph_colour(proponent_asm,                     '#117711').
graph_colour(proponent_nonAsm_toBeProved,       '#111177').
graph_colour(proponent_nonAsm,                  '#222222').

graph_colour(opponent_finished_justification,   '#CCCCCC').
graph_colour(opponent_unfinished_justification, '#FFFFFF').
graph_colour(opponent_ms_border,                '#000000').
graph_colour(opponent_ms_asm_culprit,           '#CC9922').
graph_colour(opponent_ms_asm_culprit_text,      '#FFFFFF').
graph_colour(opponent_ms_asm_defence,           '#117711').
graph_colour(opponent_ms_asm_defence_text,      '#FFFFFF').
graph_colour(opponent_ms_asm,                   '#77BB77').
graph_colour(opponent_ms_asm_text,              '#000000').
graph_colour(opponent_ms_nonAsm,                '#777777').
graph_colour(opponent_ms_nonAsm_text,           '#FFFFFF').
graph_colour(opponent_ums_asm_defence,          '#117711').
graph_colour(opponent_ums_asm_defence_border,   '#117711').
graph_colour(opponent_ums_asm_defence_text,     '#FFFFFF').
graph_colour(opponent_ums_asm_culprit,          '#CC9922').
graph_colour(opponent_ums_asm_culprit_border,   '#CC9922').
graph_colour(opponent_ums_asm_culprit_text,     '#FFFFFF').
graph_colour(opponent_ums_asm,                  '#77BB77').
graph_colour(opponent_ums_asm_border,           '#77BB77').
graph_colour(opponent_ums_asm_text,             '#000000').
graph_colour(opponent_ums_nonAsm,               '#AAAAAA').
graph_colour(opponent_ums_nonAsm_border,        '#AAAAAA').
graph_colour(opponent_ums_nonAsm_text,          '#000000').

graph_colour(attack_edge,                       '#BB2222').

%

print_result(Result) :-
 option(print_to_file, Print),
 (
  Print
  -> print_to_file(Result)
  ;  true
 ),
 option(show_solution, Show),
 (
  Show
  -> show_result(Result)
  ;  true
 ).

%

print_to_file(Result) :-
 filestem(FileStem),
 option(frameworkdir, Dir),
 option(fileID, Suff),
 atom_concat(FileStem, Suff, File),
 sols(N),
 number_codes(N, NCodes),
 atom_codes(NAtom, NCodes),
 atom_concat(File, NAtom, NumberedFile),
 atom_concat(NumberedFile, '.dot', FileName),
 atom_concat(Dir, FileName, DirAndFileName),
 open(DirAndFileName, write, Fd),
 dot_file(Result, Fd),
 close(Fd).

dot_file([D,C,JsP,JsO,Att,_], Fd) :-
 dot_preliminaries(Fd),
 proponent_cluster(JsP, Fd, PropNodeInfo),
 opponent_clusters(JsO, D, C, PropNodeInfo, Att, Fd, 1),
 format(Fd, '~n}~n', []).

dot_preliminaries(Fd) :-
 format_lines([
  'digraph G {',
  ' ',
  ' ratio="fill";',
  ' compound="true";',
  ' ranksep="1";',
  ' rankdir="LR";'], Fd),
 graph_colour(background, BGCol),
 format(Fd, ' bgcolor="~w";~n', [BGCol]),
 format(Fd, ' node [style="filled",shape="box",height="0.4",width="0.6",margin="0.1,0.1"];~n', []).

%

proponent_cluster(JsP, Fd, NodeInfo) :-
 format_lines([
  ' ',
  ' subgraph cluster0 {',
  '  label = "P";',
  '  labeljust="l";',
  '  pencolor="#444444";',
  '  style="filled";'], Fd),
 graph_colour(proponent_justifications, PropCol),
 format(Fd, '  color="~w";~n', [PropCol]),
 proponent_nodes(JsP, 0, Fd, NodeInfo),
 proponent_edges(JsP, NodeInfo, Fd),
 format(Fd, ' }~n', []).

proponent_nodes([], _, _, []).
proponent_nodes([(A,*)|Rest], N, Fd, [(A,N,0)|RestNodes]) :-
 !,
 number_atom(N, NAtom),
 format(Fd, '  s0_~w ', [NAtom]),
 (
  proving(A)
  -> graph_colour(proponent_asm_toBeProved, Colour)
  ;  graph_colour(proponent_asm, Colour)
 ),
 format(Fd, '[label="~w",fillcolor="~w",color="~w",fontcolor="white"];~n', [A,Colour,Colour]),
 N1 is N + 1,
 proponent_nodes(Rest, N1, Fd, RestNodes).
proponent_nodes([(S,_)|Rest], N, Fd, [(S,N,0)|RestNodes]) :-
 number_atom(N, NAtom),
 format(Fd, '  s0_~w ', [NAtom]),
 (
  proving(S)
  -> graph_colour(proponent_nonAsm_toBeProved, Colour)
  ;  graph_colour(proponent_nonAsm, Colour)
 ),
 format(Fd, '[label="~w",fillcolor="~w",color="~w",fontcolor="white"];~n', [S,Colour,Colour]),
 N1 is N + 1,
 proponent_nodes(Rest, N1, Fd, RestNodes).

proponent_edges([], _, _).
proponent_edges([(_,*)|Rest], NodeInfo, Fd) :-
 !,
 proponent_edges(Rest, NodeInfo, Fd).
proponent_edges([(S,RuleID)|Rest], NodeInfo, Fd) :-
 rule(S, RuleID, Body),
 body_edges(Body, S, 0, NodeInfo, Fd),
 proponent_edges(Rest, NodeInfo, Fd).

%

opponent_clusters([], _, _, _, _, _, _).
opponent_clusters([Ss-Js-_Conc|RestOpJs], D, C, PropNodeInfo, Att, Fd, ClusterN) :-
 format(Fd, '~n subgraph cluster~w {~n', [ClusterN]),
 format(Fd, '  label = "O~w";~n', [ClusterN]),
 format_lines([
  '  edge [color="#000000"];',
  '  labeljust="l";',
  '  pencolor="#444444";',
  '  style="filled";'], Fd),
 (
  Ss = []
  -> graph_colour(opponent_finished_justification, OppClusterCol)
  ;  graph_colour(opponent_unfinished_justification, OppClusterCol)
 ),
 format(Fd, '  color="~w";~n', [OppClusterCol]),
 opponent_nodes(Js-Ss, D, C, ClusterN, 0, Fd, [], OppNodeInfo),
 opponent_edges(Js, D, C, ClusterN, OppNodeInfo, Fd),
 format(Fd, ' }~n', []),
 graph_colour(attack_edge, AttackCol),
 format(Fd, '~n edge [color="~w"];~n', [AttackCol]),
 attacks(Att, PropNodeInfo, OppNodeInfo, Fd),
 ClusterN1 is ClusterN + 1,
 opponent_clusters(RestOpJs, D, C, PropNodeInfo, Att, Fd, ClusterN1).

opponent_nodes([]-[], _, _, _, _, _, NodeInfo, NodeInfo).
opponent_nodes([(A,*)|RestJs]-Ss, D, C, ClusterN, N, Fd, InNodeInfo, NodeInfo) :-
 !,
 number_atom(ClusterN, ClusterNAtom),
 number_atom(N, NAtom),
 format(Fd, '  s~w_~w ', [ClusterNAtom,NAtom]),
 (
  % MARKED SUPPORT: CULPRIT
  member(A, C)
  -> graph_colour(opponent_ms_asm_culprit, FillColour),
     graph_colour(opponent_ms_asm_culprit_text, Font)
  ;
  % MARKED SUPPORT: DEFENCE SET
  member(A, D)
  -> graph_colour(opponent_ms_asm_defence, FillColour),
     graph_colour(opponent_ms_asm_defence_text, Font)
  ;
  % MARKED SUPPORT: ASSUMPTION (NOT DEFENCE, NOT CULPRIT)
     graph_colour(opponent_ms_asm, FillColour),
     graph_colour(opponent_ms_asm_text, Font)
 ),
 graph_colour(opponent_ms_border, BorderCol),
 format(Fd, '[label="~w",fillcolor="~w",color="~w",fontcolor="~w"];~n', [A,FillColour,BorderCol,Font]),
 N1 is N + 1,
 opponent_nodes(RestJs-Ss, D, C, ClusterN, N1, Fd, [(A,N,ClusterN)|InNodeInfo], NodeInfo).
opponent_nodes([(S,_)|RestJs]-Ss, D, C, ClusterN, N, Fd, InNodeInfo, NodeInfo) :-
 !,
 number_atom(ClusterN, ClusterNAtom),
 number_atom(N, NAtom),
 format(Fd, '  s~w_~w ', [ClusterNAtom,NAtom]),
 graph_colour(opponent_ms_nonAsm, FillColour),
 graph_colour(opponent_ms_border, BorderCol),
 graph_colour(opponent_ms_nonAsm_text, Font),
 format(Fd, '[label="~w",fillcolor="~w",color="~w",fontcolor="~w"];~n', [S,FillColour,BorderCol,Font]),
 N1 is N + 1,
 opponent_nodes(RestJs-Ss, D, C, ClusterN, N1, Fd, [(S,N,ClusterN)|InNodeInfo], NodeInfo).
opponent_nodes([]-[S|RestSs], D, C, ClusterN, N, Fd, InNodeInfo, NodeInfo) :-
 (
  member((S,_,_), InNodeInfo)
  -> N1 is N,
     OutNodeInfo = InNodeInfo
  ;  number_atom(ClusterN, ClusterNAtom),
     number_atom(N, NAtom),
     format(Fd, '  s~w_~w ', [ClusterNAtom,NAtom]),
     (
      assumption(S)
      -> (
          member(S, D)
          -> 
          % UNMARKED SUPPORT: DEFENCE SET
             graph_colour(opponent_ums_asm_defence, FillColour),
             graph_colour(opponent_ums_asm_defence_border, Colour),
             graph_colour(opponent_ums_asm_defence_text, Font)
          ;
          member(S, C)
          ->
          % UNMARKED SUPPORT: CULPRIT
             graph_colour(opponent_ums_asm_culprit, FillColour),
             graph_colour(opponent_ums_asm_culprit_border, Colour),
             graph_colour(opponent_ums_asm_culprit_text, Font)
          ;
          % UNMARKED SUPPORT: NON-DEFENCE SET, NON-CULPRIT
             graph_colour(opponent_ums_asm, FillColour),
             graph_colour(opponent_ums_asm_border, Colour),
             graph_colour(opponent_ums_asm_text, Font)
         )
      ;  
         % UNMARKED SUPPORT: NON-ASSUMPTION
         graph_colour(opponent_ums_nonAsm, FillColour),
         graph_colour(opponent_ums_nonAsm_border, Colour),
         graph_colour(opponent_ums_nonAsm_text, Font)
     ),
     format(Fd, '[label="~w",fillcolor="~w",color="~w",fontcolor="~w"];~n', [S,FillColour,Colour,Font]),
     N1 is N + 1,
     OutNodeInfo = [(S,N,ClusterN)|InNodeInfo]
 ),
 opponent_nodes([]-RestSs, D, C, ClusterN, N1, Fd, OutNodeInfo, NodeInfo).

opponent_edges([], _, _, _, _, _).
opponent_edges([(_,*)|Rest], D, C, ClusterN, NodeInfo, Fd) :-
 !,
 opponent_edges(Rest, D, C, ClusterN, NodeInfo, Fd).
opponent_edges([(S,RuleID)|Rest], D, C, ClusterN, NodeInfo, Fd) :-
 rule(S, RuleID, Body),
 body_edges(Body, S, ClusterN, NodeInfo, Fd),
 opponent_edges(Rest, D, C, ClusterN, NodeInfo, Fd).

% attacks(Att, PropNodeInfo, OppNodeInfo, Fd)

attacks([], _, _, _).
attacks([(FromS,ToS)|RestAtt], PropNodeInfo, OppNodeInfo, Fd) :-
 member((FromS,FromN,FromClusterN), PropNodeInfo),
 member((ToS,ToN,ToClusterN), OppNodeInfo),
 !,
 number_atom(FromN, FromNAtom),
 number_atom(FromClusterN, FromClusterNAtom),
 number_atom(ToN, ToNAtom),
 number_atom(ToClusterN, ToClusterNAtom),
 format(Fd, ' s~w_~w -> s~w_~w;~n', [FromClusterNAtom,FromNAtom,ToClusterNAtom,ToNAtom]),
 attacks(RestAtt, PropNodeInfo, OppNodeInfo, Fd).
attacks([(FromS,ToS)|RestAtt], PropNodeInfo, OppNodeInfo, Fd) :-
 member((FromS,FromN,FromClusterN), OppNodeInfo),
 member((ToS,ToN,ToClusterN), PropNodeInfo),
 !,
 number_atom(FromN, FromNAtom),
 number_atom(FromClusterN, FromClusterNAtom),
 number_atom(ToN, ToNAtom),
 number_atom(ToClusterN, ToClusterNAtom),
 format(Fd, ' s~w_~w -> s~w_~w;~n', [FromClusterNAtom,FromNAtom,ToClusterNAtom,ToNAtom]),
 attacks(RestAtt, PropNodeInfo, OppNodeInfo, Fd).
attacks([_|RestAtt], PropNodeInfo, OppNodeInfo, Fd) :-
 attacks(RestAtt, PropNodeInfo, OppNodeInfo, Fd).

%

format_lines([], _).
format_lines([Line|Rest], Fd) :-
 format(Fd, Line, []),
 format(Fd, '~n', []),
 format_lines(Rest, Fd).

% convert a number into the corresponding atom
number_atom(N, A) :-
 number_codes(N, Codes),
 atom_codes(A, Codes).

body_edges([], _, _, _, _).
body_edges([SFrom|Rest], STo, ClusterN, NodeInfo, Fd) :-
 memberchk((SFrom,NFrom,_), NodeInfo),
 memberchk((STo,NTo,_), NodeInfo),
 number_atom(NFrom, FromAtom),
 number_atom(NTo, ToAtom),
 number_atom(ClusterN, ClusterNAtom),
 format(Fd, '  s~w_~w -> s~w_~w;~n', [ClusterNAtom,FromAtom,ClusterNAtom,ToAtom]),
 body_edges(Rest, STo, ClusterN, NodeInfo, Fd).

