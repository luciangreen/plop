:- module(unfold, [unfold_program/3, unfold_predicate/4]).

unfold_program(ProgramIR, OptimisedIR, Report) :-
    unfold_fixpoint(ProgramIR, ProgramIR, OptimisedIR, [], Report).

unfold_fixpoint(Original, Current, Optimised, ReportAcc, Report) :-
    unfold_once(Current, Next, StepReport),
    append(ReportAcc, StepReport, NextReportAcc),
    (   Next == Current
    ->  Optimised = Next,
        sort(NextReportAcc, Report)
    ;   unfold_fixpoint(Original, Next, Optimised, NextReportAcc, Report)
    ).

unfold_once(ProgramIR, UpdatedIR, Report) :-
    findall(
        Helper,
        ( member(Helper, ProgramIR),
          unfoldable_helper(ProgramIR, Helper)
        ),
        Helpers
    ),
    unfold_clauses(ProgramIR, Helpers, UpdatedIR, [], ReportRaw),
    sort(ReportRaw, Report).

unfold_clauses([], _, [], Report, Report).
unfold_clauses([Clause | Rest], Helpers, [Updated | UpdatedRest], Report0, Report) :-
    unfold_clause(Clause, Helpers, Updated, Changed),
    (   Changed = true
    ->  clause_predicate(Clause, Pred),
        Report1 = [unfolded(Pred) | Report0]
    ;   Report1 = Report0
    ),
    unfold_clauses(Rest, Helpers, UpdatedRest, Report1, Report).

unfold_clause(ir_clause(Id, Head, Body, Meta), Helpers, ir_clause(Id, Head, SplicedBody, Meta), Changed) :-
    unfold_body(Body, Helpers, UnfoldedBody, false, ChangedUnfold),
    splice_arithmetic(UnfoldedBody, SplicedBody),
    (   ChangedUnfold == true
    ->  Changed = true
    ;   Changed = (SplicedBody \== Body)
    ).

unfold_body([], _, [], Changed, Changed).
unfold_body([Goal | Rest], Helpers, UpdatedBody, Changed0, Changed) :-
    (   inline_goal(Goal, Helpers, InlinedGoals)
    ->  Changed1 = true,
        append(InlinedGoals, NextGoals, UpdatedBody)
    ;   Changed1 = Changed0,
        UpdatedBody = [Goal | NextGoals]
    ),
    unfold_body(Rest, Helpers, NextGoals, Changed1, Changed).

inline_goal(Goal, Helpers, InlinedGoals) :-
    clause_predicate_from_goal(Goal, Pred),
    member(ir_clause(_, HelperHead, HelperBody, _), Helpers),
    clause_predicate_from_goal(HelperHead, Pred),
    copy_term((HelperHead, HelperBody), (HeadCopy, BodyCopy)),
    Goal = HeadCopy,
    InlinedGoals = BodyCopy.

unfoldable_helper(ProgramIR, ir_clause(_, Head, Body, _)) :-
    clause_predicate_from_goal(Head, Pred),
    findall(C, (member(C, ProgramIR), clause_matches_predicate(C, Pred)), Clauses),
    Clauses = [ir_clause(_, _, _, _)],
    \+ calls_predicate(Body, Pred),
    forall(member(G, Body), safe_inline_goal(G)).

clause_matches_predicate(ir_clause(_, Head, _, _), Pred) :-
    clause_predicate_from_goal(Head, Pred).

safe_inline_goal(Goal) :-
    \+ is_cut(Goal),
    \+ is_meta_goal(Goal),
    \+ is_io_goal(Goal),
    \+ is_disjunction(Goal).

is_cut(!).

is_disjunction((_;_)).
is_disjunction((_->_)).
is_disjunction((_->_;_)).

is_meta_goal(Goal) :-
    callable(Goal),
    functor(Goal, Name, Arity),
    member(Name/Arity, [call/1, call/2, call/3, call/4, once/1, ignore/1, findall/3, bagof/3, setof/3, maplist/2, maplist/3, maplist/4, forall/2]).

is_io_goal(Goal) :-
    callable(Goal),
    functor(Goal, Name, Arity),
    member(Name/Arity, [write/1, writeln/1, print/1, format/2, format/3, read/1, read_term/2, read_term/3, open/3, close/1, close/2, nl/0, put_char/1, get_char/1, get_code/1, see/1, tell/1]).

calls_predicate([], _) :- false.
calls_predicate([Goal | _], Pred) :-
    clause_predicate_from_goal(Goal, Pred),
    !.
calls_predicate([_ | Rest], Pred) :-
    calls_predicate(Rest, Pred).

clause_predicate(ir_clause(_, Head, _, _), Pred) :-
    clause_predicate_from_goal(Head, Pred).

clause_predicate_from_goal(Goal, Name/Arity) :-
    callable(Goal),
    functor(Goal, Name, Arity).

splice_arithmetic(Body, Spliced) :-
    splice_arithmetic_once(Body, Body1),
    (   Body1 == Body
    ->  Spliced = Body1
    ;   splice_arithmetic(Body1, Spliced)
    ).

splice_arithmetic_once([], []).
splice_arithmetic_once([Goal | Rest], Result) :-
    (   Goal = (Var is Expr),
        var(Var),
        occurrences_in_goals(Var, Rest, 1),
        substitute_in_goals(Var, Expr, Rest, NewRest)
    ->  Result = NewRest
    ;   Result = [Goal | NewTail],
        splice_arithmetic_once(Rest, NewTail)
    ).

occurrences_in_goals(_, [], 0).
occurrences_in_goals(Var, [Goal | Rest], Count) :-
    occurrences_in_term(Var, Goal, N1),
    occurrences_in_goals(Var, Rest, N2),
    Count is N1 + N2.

occurrences_in_term(Var, Term, Count) :-
    (   var(Term)
    ->  (Term == Var -> Count = 1 ; Count = 0)
    ;   atomic(Term)
    ->  Count = 0
    ;   Term =.. [_ | Args],
        occurrences_in_terms(Var, Args, Count)
    ).

occurrences_in_terms(_, [], 0).
occurrences_in_terms(Var, [Term | Rest], Count) :-
    occurrences_in_term(Var, Term, N1),
    occurrences_in_terms(Var, Rest, N2),
    Count is N1 + N2.

substitute_in_goals(_, _, [], []).
substitute_in_goals(Var, Expr, [Goal | Rest], [NewGoal | NewRest]) :-
    substitute_term(Var, Expr, Goal, NewGoal),
    substitute_in_goals(Var, Expr, Rest, NewRest).

substitute_term(Var, Expr, Term, Out) :-
    (   var(Term)
    ->  (Term == Var -> Out = Expr ; Out = Term)
    ;   atomic(Term)
    ->  Out = Term
    ;   Term =.. [F | Args],
        substitute_terms(Var, Expr, Args, NewArgs),
        Out =.. [F | NewArgs]
    ).

substitute_terms(_, _, [], []).
substitute_terms(Var, Expr, [Term | Rest], [NewTerm | NewRest]) :-
    substitute_term(Var, Expr, Term, NewTerm),
    substitute_terms(Var, Expr, Rest, NewRest).

unfold_predicate(Pred, ProgramIR, OptimisedIR, Report) :-
    include(clause_matches_predicate_(Pred), ProgramIR, TargetClauses),
    exclude(clause_matches_predicate_(Pred), ProgramIR, OtherClauses),
    unfold_once(TargetClauses, UpdatedTargets, Report),
    append(UpdatedTargets, OtherClauses, OptimisedIR).

clause_matches_predicate_(Pred, Clause) :-
    clause_matches_predicate(Clause, Pred).
