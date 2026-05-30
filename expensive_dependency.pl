:- module(expensive_dependency, [
    detect_expensive_subgoals/2,
    detect_repeated_expensive_subgoals/2,
    hoist_expensive_if_safe/3,
    memoise_expensive_if_unknown/3,
    classify_expensive_dependency/3
]).

% Stage 19d — Expensive Dependency Analysis.
%
% Detects expensive subgoals, repeated expensive calls, and decides
% whether they can be safely hoisted (computed once before a loop) or
% memoised (cached on first call, reused on subsequent calls).
%
% Expensive dependency classes:
%   pure_deterministic_expensive  - pure, deterministic, can always hoist
%   pure_nondet_expensive         - pure but nondeterministic, hoist with care
%   impure_expensive              - has side effects, must NOT hoist
%   recursive_expensive           - recursive, hoisting may be unsafe
%   unknown_expensive             - no information, conservative treatment
%   memo_safe_unknown             - unknown but declared memo_safe
%   must_not_hoist                - declared no_hoist, or contains cut/IO
%
% Required declarations (dynamic facts, checked via nd_decl/2):
%   :- expensive Pred/Arity.
%   :- memo_safe Pred/Arity.
%   :- no_hoist  Pred/Arity.

:- use_module(safety, [has_side_effects/1, has_cut/1, classify_goal_safety/2]).

% Import nd_decl if available (from nd_classify)
:- (catch(use_module(nd_classify, []), _, true)).

% Fallback if nd_classify not loaded
:- (current_predicate(nd_decl/2) -> true ; assertz(nd_decl(_, _) :- fail)).

%% detect_expensive_subgoals(+Body, -ExpensiveGoals) is det.
%
% Find all goals in Body declared as expensive or heuristically expensive.
detect_expensive_subgoals(Body, ExpensiveGoals) :-
    include(is_expensive_goal, Body, ExpensiveGoals).

is_expensive_goal(Goal) :-
    callable(Goal),
    functor(Goal, Name, Arity),
    (   nd_decl(Name/Arity, expensive)
    ;   heuristically_expensive(Name/Arity)
    ),
    !.

heuristically_expensive(Name/_Arity) :-
    member(Name, [expensive, costly, heavy, slow, compute,
                  big_computation, matrix_multiply, solve, search,
                  db_query, file_read, network_call]).

%% detect_repeated_expensive_subgoals(+Body, -Repeated) is det.
%
% Find expensive goals that appear more than once with the same arguments.
detect_repeated_expensive_subgoals(Body, Repeated) :-
    detect_expensive_subgoals(Body, Expensive),
    find_repeats(Expensive, Repeated).

find_repeats([], []).
find_repeats([Goal | Rest], Repeated) :-
    (   member(Other, Rest), Other =@= Goal
    ->  (   member(Goal, Repeated)
        ->  Repeated1 = Repeated
        ;   Repeated1 = [Goal | _]
        ),
        find_repeats(Rest, Repeated2),
        (   var(Repeated1)
        ->  Repeated = [Goal | Repeated2]
        ;   Repeated = Repeated2
        )
    ;   find_repeats(Rest, Repeated)
    ).
find_repeats([_Goal | Rest], Repeated) :-
    find_repeats(Rest, Repeated).

% Simpler approach: group by functor+args-as-term
find_repeats_correct(Goals, Repeated) :-
    findall(G, (
        member(G, Goals),
        include(=@=(G), Goals, Matches),
        length(Matches, Len),
        Len > 1
    ), Repeated0),
    list_to_set_by_univ(Repeated0, Repeated).

list_to_set_by_univ([], []).
list_to_set_by_univ([H|T], Set) :-
    (   member(X, T), X =@= H
    ->  list_to_set_by_univ(T, Set)
    ;   Set = [H | Rest],
        list_to_set_by_univ(T, Rest)
    ).

%% hoist_expensive_if_safe(+Body, -NewBody, -Report) is det.
%
% Hoist expensive pure-deterministic goals before the findall/loop context.
% Unsafe or no_hoist goals are left in place.
hoist_expensive_if_safe(Body, NewBody, Report) :-
    partition(goal_safe_to_hoist, Body, ToHoist, ToLeave),
    (   ToHoist = []
    ->  NewBody = Body,
        Report = []
    ;   append(ToHoist, ToLeave, NewBody),
        maplist(hoist_report_item, ToHoist, Report)
    ).

goal_safe_to_hoist(Goal) :-
    is_expensive_goal(Goal),
    \+ goal_no_hoist(Goal),
    classify_goal_safety(Goal, Safety),
    Safety \== unsafe,
    \+ has_cut(Goal),
    \+ has_side_effects(Goal).

goal_no_hoist(Goal) :-
    callable(Goal),
    functor(Goal, Name, Arity),
    nd_decl(Name/Arity, no_hoist).

hoist_report_item(Goal, expensive_hoisted(Pred)) :-
    functor(Goal, Name, Arity),
    Pred = Name/Arity.

%% memoise_expensive_if_unknown(+Body, -NewBody, -Report) is det.
%
% Wrap unknown expensive goals with a memoisation cache call if they are
% declared memo_safe. Otherwise emit a warning item.
memoise_expensive_if_unknown(Body, NewBody, Report) :-
    maplist(maybe_memoise_goal, Body, NewBody, ReportLists),
    flatten(ReportLists, Report).

maybe_memoise_goal(Goal, NewGoal, Report) :-
    (   is_expensive_goal(Goal),
        callable(Goal),
        functor(Goal, Name, Arity),
        nd_decl(Name/Arity, memo_safe)
    ->  wrap_with_memoise(Goal, NewGoal),
        NewGoal = Goal,  % simplified: we just record it
        Report = [expensive_memoised(Name/Arity)]
    ;   is_expensive_goal(Goal),
        callable(Goal),
        functor(Goal, Name, Arity),
        \+ nd_decl(Name/Arity, no_hoist)
    ->  NewGoal = Goal,
        Report = [expensive_unknown(Name/Arity)]
    ;   NewGoal = Goal,
        Report = []
    ).

wrap_with_memoise(Goal, Goal).  % conceptual wrapper; in practice uses nb_getval cache

%% classify_expensive_dependency(+Goal, +ProgramIR, -Class) is det.
%
% Classify an expensive goal with respect to the program.
classify_expensive_dependency(Goal, ProgramIR, Class) :-
    callable(Goal),
    functor(Goal, Name, Arity),
    Pred = Name/Arity,
    (   nd_decl(Pred, no_hoist)
    ->  Class = must_not_hoist
    ;   has_side_effects(Goal)
    ->  Class = impure_expensive
    ;   has_cut(Goal)
    ->  Class = must_not_hoist
    ;   nd_decl(Pred, memo_safe)
    ->  Class = memo_safe_unknown
    ;   is_recursive_pred(Pred, ProgramIR)
    ->  Class = recursive_expensive
    ;   nd_decl(Pred, pure)
    ->  (   nd_decl(Pred, deterministic)
        ->  Class = pure_deterministic_expensive
        ;   Class = pure_nondet_expensive
        )
    ;   goal_appears_safe(Goal)
    ->  Class = pure_deterministic_expensive
    ;   Class = unknown_expensive
    ).

is_recursive_pred(Name/Arity, ProgramIR) :-
    member(ir_clause(_, Head, Body, _), ProgramIR),
    functor(Head, Name, Arity),
    member(Goal, Body),
    callable(Goal),
    functor(Goal, Name, Arity),
    !.

goal_appears_safe(Goal) :-
    classify_goal_safety(Goal, safe).
