:- module(loop_dependency_schedule,
          [ schedule_dependencies/4
          ]).

:- use_module(safety, [classify_goal_safety/2, experimental_mode/1]).

schedule_dependencies(BodyIn, _DepGraph, BodyOut, Report) :-
    schedule_sequence(BodyIn, [], [], 0, _LoopCounterOut, BodyOut, counts(0, 0, 0), Counts),
    counts_report(Counts, Report).

schedule_sequence([], _LoopCtx, _ActiveHoists, LoopCounter, LoopCounter, [], Counts, Counts).
schedule_sequence([TermIn|RestIn], LoopCtx, ActiveHoists, LoopCounterIn, LoopCounterOut, TermsOut, CountsIn, CountsOut) :-
    schedule_term(TermIn, LoopCtx, ActiveHoists, LoopCounterIn, LoopCounterMid,
                  TermOut, ActiveHoistsMid, CountsIn, CountsMid),
    schedule_sequence(RestIn, LoopCtx, ActiveHoistsMid, LoopCounterMid, LoopCounterOut,
                      RestOut, CountsMid, CountsOut),
    ( TermOut == '$elide' ->
        TermsOut = RestOut
    ; TermsOut = [TermOut|RestOut]
    ).

schedule_term(hoisted(Goal), LoopCtx, ActiveHoists, LoopCounter, LoopCounter,
              hoisted(Scope, Goal), ActiveHoistsOut, CountsIn, CountsOut) :-
    !,
    determine_scope(Goal, LoopCtx, Scope),
    maybe_add_active_hoist(Scope, Goal, ActiveHoists, ActiveHoistsOut),
    increment_scope_count(Scope, CountsIn, CountsOut).
schedule_term(hoisted(ScopeIn, Goal), LoopCtx, ActiveHoists, LoopCounter, LoopCounter,
              hoisted(Scope, Goal), ActiveHoistsOut, CountsIn, CountsOut) :-
    !,
    normalise_scope(ScopeIn, Goal, LoopCtx, Scope),
    maybe_add_active_hoist(Scope, Goal, ActiveHoists, ActiveHoistsOut),
    increment_scope_count(Scope, CountsIn, CountsOut).
schedule_term(Term, LoopCtx, ActiveHoists, LoopCounter, LoopCounter,
              '$elide', ActiveHoists, Counts, Counts) :-
    should_elide_term(Term, LoopCtx, ActiveHoists),
    !.
schedule_term(for(Index, Start, End, BodyIn), LoopCtx, ActiveHoists, LoopCounterIn, LoopCounterOut,
              for(Index, Start, End, BodyOut), ActiveHoists, CountsIn, CountsOut) :-
    !,
    NextId is LoopCounterIn + 1,
    loop_label(NextId, LoopLabel),
    append(LoopCtx, [loop_ctx(Index, LoopLabel)], LoopCtxInLoop),
    normalise_body_list(BodyIn, BodyListIn),
    schedule_sequence(BodyListIn, LoopCtxInLoop, ActiveHoists, NextId, LoopCounterOut, BodyListOut, CountsIn, CountsOut),
    denormalise_body_list(BodyIn, BodyListOut, BodyOut).
schedule_term(and(GoalsIn), LoopCtx, ActiveHoists, LoopCounterIn, LoopCounterOut,
              and(GoalsOut), ActiveHoists, CountsIn, CountsOut) :-
    !,
    schedule_sequence(GoalsIn, LoopCtx, ActiveHoists, LoopCounterIn, LoopCounterOut, GoalsOut, CountsIn, CountsOut).
schedule_term(or(GoalsIn), LoopCtx, ActiveHoists, LoopCounterIn, LoopCounterOut,
              or(GoalsOut), ActiveHoists, CountsIn, CountsOut) :-
    !,
    schedule_sequence(GoalsIn, LoopCtx, ActiveHoists, LoopCounterIn, LoopCounterOut, GoalsOut, CountsIn, CountsOut).
schedule_term(Term, _LoopCtx, ActiveHoists, LoopCounter, LoopCounter,
              Term, ActiveHoists, Counts, Counts).

normalise_scope(local, _Goal, _LoopCtx, local) :- !.
normalise_scope(global, Goal, LoopCtx, Scope) :-
    determine_scope(Goal, LoopCtx, Scope),
    !.
normalise_scope(loop(Label), Goal, LoopCtx, Scope) :-
    ( determine_scope(Goal, LoopCtx, loop(Label)) ->
        Scope = loop(Label)
    ; determine_scope(Goal, LoopCtx, Scope)
    ),
    !.
normalise_scope(_, Goal, LoopCtx, Scope) :-
    determine_scope(Goal, LoopCtx, Scope).

should_elide_term(Term, LoopCtx, ActiveHoists) :-
    member(active_hoist(Scope, Goal), ActiveHoists),
    scope_applies(Scope, LoopCtx),
    Goal =@= Term.

scope_applies(global, _).
scope_applies(loop(Label), LoopCtx) :-
    member(loop_ctx(_, Label), LoopCtx).
scope_applies(local, _) :-
    fail.

determine_scope(Goal, _LoopCtx, local) :-
    \+ goal_hoist_allowed(Goal),
    !.
determine_scope(Goal, LoopCtx, global) :-
    term_variables(Goal, GoalVars),
    \+ goal_depends_on_loop_var(GoalVars, LoopCtx, _),
    !.
determine_scope(Goal, LoopCtx, loop(LoopLabel)) :-
    term_variables(Goal, GoalVars),
    goal_depends_on_loop_var(GoalVars, LoopCtx, LoopLabel),
    !.
determine_scope(_Goal, _LoopCtx, local).

goal_depends_on_loop_var(GoalVars, LoopCtx, LoopLabel) :-
    member(loop_ctx(IndexVar, LoopLabel), LoopCtx),
    memberchk(IndexVar, GoalVars),
    !.

goal_hoist_allowed(Goal) :-
    classify_goal_safety(Goal, safe),
    !.
goal_hoist_allowed(_Goal) :-
    experimental_mode(true).

maybe_add_active_hoist(local, _Goal, Active, Active) :- !.
maybe_add_active_hoist(Scope, Goal, Active, [active_hoist(Scope, Goal)|Active]).

normalise_body_list(Body, BodyList) :-
    ( is_list(Body) ->
        BodyList = Body
    ; Body = and(Goals) ->
        BodyList = Goals
    ; Body == true ->
        BodyList = []
    ; BodyList = [Body]
    ).

denormalise_body_list(BodyIn, BodyList, BodyOut) :-
    ( is_list(BodyIn) ->
        BodyOut = BodyList
    ; BodyIn = and(_) ->
        BodyOut = and(BodyList)
    ; BodyIn == true ->
        ( BodyList == [] -> BodyOut = true ; BodyOut = and(BodyList) )
    ; BodyList = [Single] ->
        BodyOut = Single
    ; BodyOut = and(BodyList)
    ).

loop_label(Id, Label) :-
    format(atom(Label), 'loop_~d', [Id]).

increment_scope_count(global, counts(L0, G0, Left0), counts(L0, G, Left0)) :-
    G is G0 + 1.
increment_scope_count(loop(_), counts(L0, G0, Left0), counts(L, G0, Left0)) :-
    L is L0 + 1.
increment_scope_count(local, counts(L0, G0, Left0), counts(L0, G0, Left)) :-
    Left is Left0 + 1.

counts_report(counts(LoopCount, GlobalCount, LeftCount),
              [ loop_hoisted_count(LoopCount),
                global_hoisted_count(GlobalCount),
                left_in_loop_count(LeftCount)
              ]).
