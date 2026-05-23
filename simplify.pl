:- module(simplify, [simplify_program/3]).

simplify_program(ProgramIR, OptimisedIR, Report) :-
    findall(
        Name/Arity,
        (
            member(ir_clause(_, Head, _, _), ProgramIR),
            functor(Head, Name, Arity)
        ),
        Preds0
    ),
    sort(Preds0, Preds),
    simplify_predicates(Preds, ProgramIR, ProgramIR, OptimisedIR, [], ReportRaw),
    sort(ReportRaw, Report).

simplify_predicates([], _, Current, Current, Report, Report).
simplify_predicates([Pred | Rest], ProgramIR, Current0, Current, Report0, Report) :-
    (   simplify_sum_to_n_predicate(Pred, ProgramIR, Current0, Current1, Item)
    ->  Report1 = [Item | Report0]
    ;   Current1 = Current0,
        Report1 = Report0
    ),
    simplify_predicates(Rest, ProgramIR, Current1, Current, Report1, Report).

simplify_sum_to_n_predicate(Name/2, ProgramIR, Current0, Current, ReportItem) :-
    include(matches_predicate(Name/2), ProgramIR, Clauses),
    Clauses = [C1, C2],
    classify_sum_clauses(Name, C1, C2, SumRecursive),
    extract_sum_recursive_vars(Name, SumRecursive, InVar, OutVar),
    sample_verification_range(Start, End),
    verify_sum_formula_samples(Start, End),
    FormulaBody = [OutVar is InVar * (InVar + 1) // 2],
    replacement_clause(Current0, Name/2, Name, 2, InVar, OutVar, FormulaBody, Current),
    ReportItem = formula_discovered(Name/2, n_times_n_plus_1_over_2).

matches_predicate(Name/Arity, ir_clause(_, Head, _, _)) :-
    functor(Head, Name, Arity).

classify_sum_clauses(Name, C1, C2, Recursive) :-
    (   is_sum_base_clause(Name, C1),
        Recursive = C2
    ;   is_sum_base_clause(Name, C2),
        Recursive = C1
    ),
    is_sum_recursive_clause(Name, Recursive, _, _).

is_sum_base_clause(Name, ir_clause(_, Head, [], _)) :-
    Head =.. [Name, 0, 0].

is_sum_recursive_clause(Name, ir_clause(_, Head, Body, _), N, S) :-
    Head =.. [Name, N, S],
    Body = [N > 0, N1 is N - 1, RecGoal, S is S1 + N],
    RecGoal =.. [Name, N1, S1].

extract_sum_recursive_vars(Name, RecursiveClause, N, S) :-
    is_sum_recursive_clause(Name, RecursiveClause, N, S).

% 13 samples (0..12) cover the base case and multiple recursive depths with low overhead.
sample_verification_range(0, 12).

verify_sum_formula_samples(Start, End) :-
    forall(
        between(Start, End, N),
        (
            sum_recurrence(N, FromRecurrence),
            FromFormula is N * (N + 1) // 2,
            FromRecurrence =:= FromFormula
        )
    ).

sum_recurrence(0, 0).
sum_recurrence(N, S) :-
    N > 0,
    N1 is N - 1,
    sum_recurrence(N1, S1),
    S is S1 + N.

replacement_clause(ProgramIR, Pred, Name, Arity, N, S, FormulaBody, UpdatedIR) :-
    include(not_matches_predicate(Pred), ProgramIR, OtherClauses),
    formula_clause_id(ProgramIR, Name, Arity, ClauseId),
    UpdatedIR = [ir_clause(ClauseId, Head, FormulaBody, []) | OtherClauses],
    Head =.. [Name, N, S].

not_matches_predicate(Pred, Clause) :-
    \+ matches_predicate(Pred, Clause).

formula_clause_id(ProgramIR, Name, Arity, ClauseId) :-
    atomic_list_concat([c_formula_, Name, '_', Arity], BaseId),
    unique_clause_id(ProgramIR, BaseId, 0, ClauseId).

unique_clause_id(ProgramIR, BaseId, N, ClauseId) :-
    (   N = 0
    ->  Candidate = BaseId
    ;   atomic_list_concat([BaseId, '_', N], Candidate)
    ),
    (   member(ir_clause(Candidate, _, _, _), ProgramIR)
    ->  N1 is N + 1,
        unique_clause_id(ProgramIR, BaseId, N1, ClauseId)
    ;   ClauseId = Candidate
    ).
