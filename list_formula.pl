:- module(list_formula, [optimise_list_formulas/3]).

optimise_list_formulas(ProgramIR, OptimisedIR, Report) :-
    optimise_clauses(ProgramIR, OptimisedIR, [], ReportRaw),
    sort(ReportRaw, Report).

optimise_clauses([], [], Report, Report).
optimise_clauses([Clause | Rest], [UpdatedClause | UpdatedRest], Report0, Report) :-
    optimise_clause(Clause, UpdatedClause, Item),
    (   nonvar(Item)
    ->  Report1 = [Item | Report0]
    ;   Report1 = Report0
    ),
    optimise_clauses(Rest, UpdatedRest, Report1, Report).

optimise_clause(ir_clause(Id, Head, Body, Meta), ir_clause(Id, Head, OptimisedBody, Meta), ReportItem) :-
    (   rewrite_list_sum_pattern(Head, Body, OptimisedBody, FormulaTag)
    ->  predicate_from_head(Head, Pred),
        ReportItem = formula_discovered(Pred, FormulaTag)
    ;   OptimisedBody = Body
    ).

rewrite_list_sum_pattern(Head, Body, OptimisedBody, n_times_n_plus_1_over_2) :-
    append(Prefix, [build_1_to_n(N, L), sum_list(L, S) | Suffix], Body),
    \+ term_contains_var(L, Head),
    variable_occurrences_in_goals(L, Body, 2),
    OptimisedGoal = (S is N * (N + 1) // 2),
    append(Prefix, [OptimisedGoal | Suffix], OptimisedBody).
rewrite_list_sum_pattern(Head, Body, OptimisedBody, arithmetic_progression_sum) :-
    append(Prefix, [build_sequence(N, Start, Step, L), sum_list(L, S) | Suffix], Body),
    \+ term_contains_var(L, Head),
    variable_occurrences_in_goals(L, Body, 2),
    OptimisedGoal = (S is N * (2 * Start + (N - 1) * Step) // 2),
    append(Prefix, [OptimisedGoal | Suffix], OptimisedBody).

predicate_from_head(Head, Name/Arity) :-
    functor(Head, Name, Arity).

% term_contains_var(+Var, +Term)
%
% True if Term syntactically contains the variable Var (identity check).
term_contains_var(Var, Term) :-
    (   var(Term)
    ->  Var == Term
    ;   compound(Term),
        Term =.. [_ | Args],
        member(Arg, Args),
        term_contains_var(Var, Arg)
    ).

variable_occurrences_in_goals(Var, Goals, Count) :-
    occurrences_in_goals(Var, Goals, Count).

occurrences_in_goals(_, [], 0).
occurrences_in_goals(Var, [Goal | Rest], Count) :-
    occurrences_in_term(Var, Goal, C1),
    occurrences_in_goals(Var, Rest, C2),
    Count is C1 + C2.

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
    occurrences_in_term(Var, Term, C1),
    occurrences_in_terms(Var, Rest, C2),
    Count is C1 + C2.
