
:-ensure_loaded('probleme.pl').
:-ensure_loaded('testing.pl').

get_days(Context, Days) :- member(days(Days), Context).
get_times(Context, Times) :- member(times(Times), Context).
get_rooms(Context, Rooms) :- member(rooms(Rooms), Context).
get_groups(Context, Groups) :- member(groups(Groups), Context).
get_staff(Context, Staff) :- member(staff(Staff), Context).
get_activities(Context, Activities) :- member(activities(Activities), Context).
get_constraints(Context, Constraints) :- member(constraints(Constraints), Context).

isSlot(Context, Slot) :- Slot = slot(A, G, D, T, R, P), 
						get_activities(Context, Activities), member((A, _), Activities),
						get_groups(Context, Groups), member(G, Groups),
						get_days(Context, Days), member(D, Days),
						get_times(Context, Times), member(T, Times),
						get_rooms(Context, Rooms), member(R, Rooms),
						get_staff(Context, Staff), member((P, L), Staff),
						member(A, L).

all(Context, Slots) :-
	get_activities(Context, Activities), 
	get_groups(Context, Groups), 
	forall((member(G, Groups), member((A, _), Activities)),
	member(slot(A, G, _, _, _, _), Slots)).

make_schedule([], Final, Final).
make_schedule([slot(A, G, D, T, R, P) | Rest], SoFar, Final) :-
	\+ member(slot(_, _, D, T, _, P), SoFar),
	\+ member(slot(_, _, D, T, R, _), SoFar), 
	\+ member(slot(_, G, D, T, _, _), SoFar), 
	make_schedule(Rest, [slot(A, G, D, T, R, P) | SoFar], Final).
make_schedule([slot(_, _, _, _, _, _) | Rest], SoFar, Final) :-
	make_schedule(Rest, SoFar, Final).

nn(Slots, A, N, G) :- 
	findall(slot(A, G, _, _, _, _), member(slot(A, G, _, _, _, _), Slots), L),
	length(L, N).

nr_inst(Context, Slots) :- 
	get_activities(Context, Activities), 
	get_groups(Context, Groups),
	forall((member((A, N), Activities), member(G, Groups)), 
	nn(Slots, A, N, G)).

nr_inst_one_act(Slots, A, N, G, D) :- 
	findall(slot(A, G, D, _, _, _), member(slot(A, G, D, _, _, _), Slots), L),
	length(L, LN), LN =< N.

max_inst(Context, _) :- 
	\+ member(constraints(_), Context).
max_inst(Context, _) :-
	member(constraints(Constraints), Context),
	\+ member(max_instances(_, _), Constraints).
max_inst(Context, Slots) :- 
	member(constraints(Constraints), Context),
	member(max_instances(_, _), Constraints),
	get_days(Context, Days), 
	get_groups(Context, Groups),
	forall((member(max_instances(A, N), Constraints), member(D, Days), member(G, Groups)),
	nr_inst_one_act(Slots, A, N, G, D)).

helper(Context, Slots) :- 
	setof(Slot, isSlot(Context, Slot), Slots1), Slots1 \= [],
	all(Context, Slots1),
	make_schedule(Slots1, [], Slots),
	nr_inst(Context, Slots),
	max_inst(Context, Slots).

empty_schedule(Context) :- 
	get_activities(Context, []);
	get_days(Context, []); 
	get_groups(Context, []);
	get_rooms(Context, []);
	get_staff(Context, []);
	get_times(Context, []).

% schedule(+Context, -Sol)
% pentru contextul descris, întoarce o soluție care respectă
% constrângerile fizice și de curiculă.
schedule(Context, (Context, [])) :- empty_schedule(Context), !.
schedule(Context, (Context, [])) :- 
	\+ helper(Context, _), !, fail.
schedule(Context, (Context, Slots)) :-  
	setof(S, helper(Context, S), SS), member(Slots, SS).

interval_length(Context, ILen) :- get_times(Context, Times), member((_, ILen), Times).

cost_maxH_oneG_oneD(Slots, ILen, G, D, Hours, _, 0) :- 
	findall(slot(_, G, D, _, _, _), member(slot(_, G, D, _, _, _), Slots), L),
	length(L, LN), H is LN * ILen, H =< Hours.
cost_maxH_oneG_oneD(Slots, ILen, G, D, Hours, Cost, FinalCost) :- 
	findall(slot(_, G, D, _, _, _), member(slot(_, G, D, _, _, _), Slots), L),
	length(L, LN), H is LN * ILen, H > Hours, Y is H - Hours,
	FinalCost is Y * Cost.

cost_maxH_oneP_oneD(Slots, ILen, P, D, Hours, _, 0) :- 
	findall(slot(_, _, D, _, _, P), member(slot(_, _, D, _, _, P), Slots), L),
	length(L, LN), H is LN * ILen, H =< Hours.
cost_maxH_oneP_oneD(Slots, ILen, P, D, Hours, Cost, FinalCost) :- 
	findall(slot(_, _, D, _, _, P), member(slot(_, _, D, _, _, P), Slots), L),
	length(L, LN), H is LN * ILen, H > Hours, Y is H - Hours,
	FinalCost is Y * Cost.

cost_maxH_oneR_oneD(Slots, ILen, R, D, Hours, _, 0) :- 
	findall(slot(_, _, D, _, R, _), member(slot(_, _, D, _, R, _), Slots), L),
	length(L, LN), H is LN * ILen, H =< Hours.
cost_maxH_oneR_oneD(Slots, ILen, R, D, Hours, Cost, FinalCost) :- 
	findall(slot(_, _, D, _, R, _), member(slot(_, _, D, _, R, _), Slots), L),
	length(L, LN), H is LN * ILen, H > Hours, Y is H - Hours,
	FinalCost is Y * Cost.

cost_maxH_oneE_allD(_, _, _, [], 0).
cost_maxH_oneE_allD(Context, Slots, E, [D | Rest], Cost) :-
	get_constraints(Context, Constraints),
	member(max_hours(E, Hours, Cost1), Constraints),
	interval_length(Context, ILen),
	get_groups(Context, Groups), member(E, Groups),
	cost_maxH_oneG_oneD(Slots, ILen, E, D, Hours, Cost1, X),
	cost_maxH_oneE_allD(Context, Slots, E, Rest, Y),
	Cost is X + Y.
cost_maxH_oneE_allD(Context, Slots, E, [D | Rest], Cost) :-
	get_constraints(Context, Constraints),
	member(max_hours(E, Hours, Cost1), Constraints),
	interval_length(Context, ILen),
	get_staff(Context, Staff), member((E, _), Staff),
	cost_maxH_oneP_oneD(Slots, ILen, E, D, Hours, Cost1, X),
	cost_maxH_oneE_allD(Context, Slots, E, Rest, Y),
	Cost is X + Y.
cost_maxH_oneE_allD(Context, Slots, E, [D | Rest], Cost) :-
	get_constraints(Context, Constraints),
	member(max_hours(E, Hours, Cost1), Constraints),
	interval_length(Context, ILen),
	get_rooms(Context, Rooms), member(E, Rooms),
	cost_maxH_oneR_oneD(Slots, ILen, E, D, Hours, Cost1, X),
	cost_maxH_oneE_allD(Context, Slots, E, Rest, Y),
	Cost is X + Y.

cost_maxH_allE(_, _, [], 0).
cost_maxH_allE(Context, Slots, [E | Rest], Cost) :- 
	get_days(Context, Days),
	cost_maxH_oneE_allD(Context, Slots, E, Days, X),
	cost_maxH_allE(Context, Slots, Rest, Y),
	Cost is X + Y.

cost_maxH(Context, _, 0) :- \+ member(constraints(_), Context).
cost_maxH(Context, _, 0) :- 
	member(constraints(Constraints), Context),
	\+ member(max_hours(_, _, _), Constraints).
cost_maxH(Context, Slots, Cost) :- 
	member(constraints(Constraints), Context),
	findall(E, member(max_hours(E, _, _), Constraints), L),
	cost_maxH_allE(Context, Slots, L, Cost).

cost_minH_oneG_oneD(Slots, ILen, G, D, Hours, _, 0) :- 
	findall(slot(_, G, D, _, _, _), member(slot(_, G, D, _, _, _), Slots), L),
	length(L, LN), H is LN * ILen, H >= Hours.
cost_minH_oneG_oneD(Slots, ILen, G, D, Hours, Cost, FinalCost) :- 
	findall(slot(_, G, D, _, _, _), member(slot(_, G, D, _, _, _), Slots), L),
	length(L, LN), H is LN * ILen, H < Hours, Y is Hours - H,
	FinalCost is Y * Cost.

cost_minH_oneP_oneD(Slots, ILen, P, D, Hours, _, 0) :- 
	findall(slot(_, _, D, _, _, P), member(slot(_, _, D, _, _, P), Slots), L),
	length(L, LN), H is LN * ILen, H >= Hours.
cost_minH_oneP_oneD(Slots, ILen, P, D, Hours, Cost, FinalCost) :- 
	findall(slot(_, _, D, _, _, P), member(slot(_, _, D, _, _, P), Slots), L),
	length(L, LN), H is LN * ILen, H < Hours, Y is Hours - H,
	FinalCost is Y * Cost.

cost_minH_oneR_oneD(Slots, ILen, R, D, Hours, _, 0) :- 
	findall(slot(_, _, D, _, R, _), member(slot(_, _, D, _, R, _), Slots), L),
	length(L, LN), H is LN * ILen, H >= Hours.
cost_minH_oneR_oneD(Slots, ILen, R, D, Hours, Cost, FinalCost) :- 
	findall(slot(_, _, D, _, R, _), member(slot(_, _, D, _, R, _), Slots), L),
	length(L, LN), H is LN * ILen, H < Hours, Y is Hours - H,
	FinalCost is Y * Cost.

cost_minH_oneE_allD(_, _, _, [], 0).
cost_minH_oneE_allD(Context, Slots, E, [D | Rest], Cost) :-
	get_constraints(Context, Constraints),
	member(min_hours(E, Hours, Cost1), Constraints),
	interval_length(Context, ILen),
	get_groups(Context, Groups), member(E, Groups),
	cost_minH_oneG_oneD(Slots, ILen, E, D, Hours, Cost1, X),
	cost_minH_oneE_allD(Context, Slots, E, Rest, Y),
	Cost is X + Y.
cost_minH_oneE_allD(Context, Slots, E, [D | Rest], Cost) :-
	get_constraints(Context, Constraints),
	member(min_hours(E, Hours, Cost1), Constraints),
	interval_length(Context, ILen),
	get_staff(Context, Staff), member((E, _), Staff),
	cost_minH_oneP_oneD(Slots, ILen, E, D, Hours, Cost1, X),
	cost_minH_oneE_allD(Context, Slots, E, Rest, Y),
	Cost is X + Y.
cost_minH_oneE_allD(Context, Slots, E, [D | Rest], Cost) :-
	get_constraints(Context, Constraints),
	member(min_hours(E, Hours, Cost1), Constraints),
	interval_length(Context, ILen),
	get_rooms(Context, Rooms), member(E, Rooms),
	cost_minH_oneR_oneD(Slots, ILen, E, D, Hours, Cost1, X),
	cost_minH_oneE_allD(Context, Slots, E, Rest, Y),
	Cost is X + Y.

cost_minH_allE(_, _, [], 0).
cost_minH_allE(Context, Slots, [E | Rest], Cost) :- 
	get_days(Context, Days),
	cost_minH_oneE_allD(Context, Slots, E, Days, X),
	cost_minH_allE(Context, Slots, Rest, Y),
	Cost is X + Y.

cost_minH(Context, _, 0) :- \+ member(constraints(_), Context).
cost_minH(Context, _, 0) :- 
	member(constraints(Constraints), Context),
	\+ member(min_hours(_, _, _), Constraints).
cost_minH(Context, Slots, Cost) :- 
	member(constraints(Constraints), Context),
	findall(E, member(min_hours(E, _, _), Constraints), L),
	cost_minH_allE(Context, Slots, L, Cost).

cost_interval_oneE(_, _, _, [], 0).
cost_interval_oneE(Context, Slots, E, [S | Rest], Cost) :-
	S = slot(_, _, _, (A-B, _), _, _),
	member(constraints(Constraints), Context),
	member(interval(E, Start, End, _), Constraints),
	Start =< A, B =< End, 
	cost_interval_oneE(Context, Slots, E, Rest, Cost).
cost_interval_oneE(Context, Slots, E, [S | Rest], Cost) :-
	S = slot(_, _, _, (A-_, _), _, _),
	member(constraints(Constraints), Context),
	member(interval(E, Start, _, Cost1), Constraints),
	A < Start, X is Cost1 * (Start - A),
	cost_interval_oneE(Context, Slots, E, Rest, Cost2),
	Cost is X + Cost2.
cost_interval_oneE(Context, Slots, E, [S | Rest], Cost) :-
	S = slot(_, _, _, (_-B, _), _, _),
	member(constraints(Constraints), Context),
	member(interval(E, _, End, Cost1), Constraints),
	End < B, X is Cost1 * (B - End),
	cost_interval_oneE(Context, Slots, E, Rest, Cost2),
	Cost is X + Cost2.

cost_interval_allE(_, _, [], 0).
cost_interval_allE(Context, Slots, [E | Rest], Cost) :-
	findall(S, (member(S, Slots), S = slot(_, E, _, _, _, _)), L1),
	findall(S, (member(S, Slots), S = slot(_, _, _, _, E, _)), L2), 
	findall(S, (member(S, Slots), S = slot(_, _, _, _, _, E)), L3),
	append(L1, L2, L4), append(L4, L3, L), 
	cost_interval_oneE(Context, Slots, E, L, X),
	cost_interval_allE(Context, Slots, Rest, Y),
	Cost is X + Y.

cost_interval(Context, _, 0) :- \+ member(constraints(_), Context).
cost_interval(Context, _, 0) :- 
	member(constraints(Constraints), Context),
	\+ member(interval(_, _, _, _), Constraints).
cost_interval(Context, Slots, Cost) :-
	member(constraints(Constraints), Context),
	member(interval(_, _, _, _), Constraints),
	findall(E, member(interval(E, _, _, _), Constraints), L),
	cost_interval_allE(Context, Slots, L, Cost).

cost_continuous_oneE_oneD(_, _, L, 0) :- length(L, 0); length(L, 1).
cost_continuous_oneE_oneD(E, Cost, [(_-B1), (A2-B2) | Rest], FinalCost) :-
	B1 =:= A2,
	cost_continuous_oneE_oneD(E, Cost, [(A2-B2) | Rest], FinalCost), !.
cost_continuous_oneE_oneD(E, Cost, [(_-B1), (A2-B2) | Rest], FinalCost) :-
	B1 < A2,
	cost_continuous_oneE_oneD(E, Cost, [(A2-B2) | Rest], X),
	FinalCost is Cost + X.

cost_continuous_oneE_allD(_, _, _, [], 0).
cost_continuous_oneE_allD(Context, Slots, E, [D | Rest], Cost) :-
	findall((A-B), member(slot(_, E, D, (A-B, _), _, _), Slots), L1),
	findall((A-B), member(slot(_, _, D, (A-B, _), E, _), Slots), L2),
	findall((A-B), member(slot(_, _, D, (A-B, _), _, E), Slots), L3),
	append(L1, L2, L4), append(L4, L3, L5),
	sort(L5, L),
	get_constraints(Context, Constraints),
	member(continuous(E, C), Constraints),
	cost_continuous_oneE_oneD(E, C, L, X),
	cost_continuous_oneE_allD(Context, Slots, E, Rest, Y),
	Cost is X + Y.

cost_continuous_allE(_, _, [], 0).
cost_continuous_allE(Context, Slots, [E | Rest], Cost) :-
	get_days(Context, Days),  
	cost_continuous_oneE_allD(Context, Slots, E, Days, X),
	cost_continuous_allE(Context, Slots, Rest, Y),
	Cost is X + Y.

cost_continuous(Context, _, 0) :- \+ member(constraints(_), Context).
cost_continuous(Context, _, 0) :- 
	member(constraints(Constraints), Context),
	\+ member(continuous(_, _), Constraints).
cost_continuous(Context, Slots, Cost) :-
	member(constraints(Constraints), Context),
	member(continuous(_, _), Constraints),
	findall(E, member(continuous(E, _), Constraints), L),
	cost_continuous_allE(Context, Slots, L, Cost).

% cost(+Sol, -Cost)
% pentru soluția dată, întoarce costul implicat de constrângerile de
% preferință care au fost încălcate.
cost((Context, Slots), Cost) :- 
	cost_maxH(Context, Slots, Cost1),
	cost_minH(Context, Slots, Cost2),
	cost_continuous(Context, Slots, Cost4),
	cost_interval(Context, Slots, Cost3),
	Cost is Cost1 + Cost2 + Cost3 + Cost4.

helperBest([Sol], 0, Sol) :- cost(Sol, 0).
helperBest([Sol | _], 0, Sol) :- cost(Sol, 0).
helperBest([Sol | Rest], MinCost, Sol) :- 
	cost(Sol, MinCost),
	helperBest(Rest, Cost1, _),
	MinCost =< Cost1.
helperBest([_| Rest], MinCost, S) :- 
	helperBest(Rest, MinCost, S).

canHaveMore(Context, Sols) :- schedule(Context, S), \+ member(S, Sols).

%h(Context, Sols, 0, S) :-
%	schedule(Context, S), \+ member(S, Sols),
%	cost(S, 0). 
h(Context, Sols, MinCost, Sol) :-
	schedule(Context, S), \+ member(S, Sols),
	cost(S, C), h(Context, [S | Sols], MinCost, Sol),
	C > MinCost. 
h(Context, Sols, MinCost, Sol) :-
	schedule(Context, Sol), \+ member(Sol, Sols),
	cost(Sol, MinCost), h(Context, [Sol | Sols], C, Sol),
	C > MinCost. 
h(Context, Sols, MinCost, Sol) :-
	schedule(Context, Sol), \+ member(Sol, Sols),
	\+ canHaveMore(Context, [Sol | Sols]), cost(Sol, MinCost). 


% schedule_best(+Context, -Sol, -Cost)
% pentru contextul descris, întoarce soluția validă cu cel mai bun (cel
% mai mic) cost (sau una dintre ele, dacă există mai multe cu același
% cost)
%schedule_best(Context, Sol, 0) :- schedule(Context, Sol), cost(Sol, 0), !.
schedule_best(Context, Sol, Cost) :- 
	h(Context, [], Cost, Sol).














