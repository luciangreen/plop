:- module(memoise, [memoise_program/3]).

% memoise_program(+ProgramIR, -OptimisedIR, -Report)
%
% Stage 2: detect and eliminate duplicate calls to the same predicate
% with the same input arguments within a single clause body.  The
% duplicate call is removed and the output variable(s) of the later
% call are unified with those of the earlier call.
%
% Example:
%   p(X,Y,Z) :- expensive(X,A), expensive(X,B), Y is A+1, Z is B+2.
% becomes (B unified with A, second expensive/2 call dropped):
%   p(X,Y,Z) :- expensive(X,A), Y is A+1, Z is A+2.

memoise_program(ProgramIR, OptimisedIR, Report) :-
    memoise_clauses(ProgramIR, OptimisedIR, [], ReportRaw),
    sort(ReportRaw, Report).

memoise_clauses([], [], Report, Report).
memoise_clauses([Clause|Rest], [OptClause|OptRest], Report0, Report) :-
    memoise_clause(Clause, OptClause, Changed),
    (   Changed = true
    ->  Clause = ir_clause(_, Head, _, _),
        functor(Head, F, N),
        Report1 = [memoised(F/N) | Report0]
    ;   Report1 = Report0
    ),
    memoise_clauses(Rest, OptRest, Report1, Report).

memoise_clause(ir_clause(Id, Head, Body, Meta), ir_clause(Id, Head, OptBody, Meta), Changed) :-
    term_variables(Head, HeadVars),
    deduplicate_body(Body, HeadVars, [], OptBody, false, Changed).

% deduplicate_body(+Body, +HeadVars, +Seen, -OptBody, +Changed0, -Changed)
%
% Processes the body left-to-right. For each goal that is safe to
% memoise, checks whether an equivalent prior call exists in Seen.
% If found, the fresh output variables of the current call are unified
% with those of the previous call and the current call is dropped.

deduplicate_body([], _, _, [], Changed, Changed).
deduplicate_body([Goal|Rest], HeadVars, Seen, OptBody, Changed0, Changed) :-
    term_variables(Seen, SeenGoalVars),
    append(HeadVars, SeenGoalVars, AllKnownVars),
    (   safe_memo_goal(Goal),
        find_and_merge_duplicate(Goal, Seen, AllKnownVars)
    ->  deduplicate_body(Rest, HeadVars, Seen, OptBody, true, Changed)
    ;   OptBody = [Goal | OptRest],
        deduplicate_body(Rest, HeadVars, [Goal|Seen], OptRest, Changed0, Changed)
    ).

% find_and_merge_duplicate(+Goal, +Seen, +KnownVars)
%
% Succeeds (with side-effectful unification) when a previous call in
% Seen has the same functor/arity as Goal and compatible arguments:
%   - Positions where both args are the same term (==) are accepted.
%   - Positions where the current call's arg is a fresh variable
%     (not in KnownVars) are unified with the previous call's arg.
% The ! after a successful unification prevents backtracking.

find_and_merge_duplicate(Goal, Seen, KnownVars) :-
    functor(Goal, F, N),
    Goal =.. [F | Args],
    member(PrevGoal, Seen),
    functor(PrevGoal, F, N),
    PrevGoal =.. [F | PrevArgs],
    unify_duplicate_args(Args, PrevArgs, KnownVars),
    !.

% unify_duplicate_args(+Args, +PrevArgs, +KnownVars)
%
% For each argument pair (A, B):
%   - A == B  : same term (matches input position)
%   - var(A), A not in KnownVars : A is a fresh output var; unify A = B

unify_duplicate_args([], [], _).
unify_duplicate_args([A|As], [B|Bs], KnownVars) :-
    (   A == B
    ->  unify_duplicate_args(As, Bs, KnownVars)
    ;   var(A),
        \+ member_var(A, KnownVars)
    ->  A = B,
        unify_duplicate_args(As, Bs, KnownVars)
    ;   fail
    ).

member_var(Var, [H|_]) :- Var == H, !.
member_var(Var, [_|T]) :- member_var(Var, T).

% safe_memo_goal(+Goal)
%
% A goal is safe to consider for memoisation if it is:
%   - callable,
%   - not a cut,
%   - not a meta-call (findall, call, maplist, ...),
%   - not an I/O predicate,
%   - not a disjunction / if-then(-else),
%   - not a built-in arithmetic or comparison expression.

safe_memo_goal(Goal) :-
    callable(Goal),
    \+ is_cut(Goal),
    \+ is_meta_goal(Goal),
    \+ is_io_goal(Goal),
    \+ is_disjunction(Goal),
    \+ is_builtin_test_goal(Goal).

is_cut(!).

is_disjunction((_;_)).
is_disjunction((_->_)).
is_disjunction((_->_;_)).

is_meta_goal(Goal) :-
    callable(Goal),
    functor(Goal, Name, Arity),
    member(Name/Arity, [call/1, call/2, call/3, call/4,
                        once/1, ignore/1,
                        findall/3, bagof/3, setof/3,
                        maplist/2, maplist/3, maplist/4,
                        forall/2]).

is_io_goal(Goal) :-
    callable(Goal),
    functor(Goal, Name, Arity),
    member(Name/Arity, [write/1, writeln/1, print/1,
                        format/2, format/3,
                        read/1, read_term/2, read_term/3,
                        open/3, close/1, close/2,
                        nl/0, put_char/1, get_char/1, get_code/1,
                        see/1, tell/1]).

% Built-in arithmetic, comparison, and unification goals are excluded
% because they are not user-defined predicates with separable I/O
% arguments, so the duplicate-call pattern does not apply to them.
is_builtin_test_goal(_ is _).
is_builtin_test_goal(_ > _).
is_builtin_test_goal(_ < _).
is_builtin_test_goal(_ >= _).
is_builtin_test_goal(_ =< _).
is_builtin_test_goal(_ =:= _).
is_builtin_test_goal(_ =\= _).
is_builtin_test_goal(_ = _).
is_builtin_test_goal(_ \= _).
is_builtin_test_goal(_ == _).
is_builtin_test_goal(_ \== _).
