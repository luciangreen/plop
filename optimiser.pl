:- module(optimiser, [optimise_file/2, optimise_program/3, optimise_predicate/4]).
:- reexport(parser, [parse_file/2]).

:- use_module(parser).
:- use_module(unfold).
:- use_module(memoise).
:- use_module(simplify).
:- use_module(list_formula).
:- use_module(enumerators).
:- use_module(indexical).
:- use_module(recursive_index).
:- use_module(splice).
:- use_module(loop_conversion).
:- use_module(safety).

optimise_file(InputFile, OutputFile) :-
    parse_file(InputFile, ProgramIR),
    optimise_program(ProgramIR, OptimisedIR, _Report),
    write_program(OutputFile, OptimisedIR).

optimise_program(ProgramIR, OptimisedIR, optimisation_report(Items)) :-
    unfold_program(ProgramIR, UnfoldedIR, UnfoldItems),
    memoise_program(UnfoldedIR, MemoisedIR, MemoItems),
    simplify_program(MemoisedIR, SimplifiedIR, SimplifyItems),
    optimise_list_formulas(SimplifiedIR, ListFormulaIR, ListFormulaItems),
    optimise_indexicals(ListFormulaIR, IndexicalIR, IndexicalItems),
    optimise_recursive_index_loops(IndexicalIR, RecursiveIndexIR, RecursiveIndexItems),
    splice_program(RecursiveIndexIR, SplicedIR, SpliceItems),
    convert_deterministic_loops(SplicedIR, LoopIR, LoopItems),
    analyse_enumerators(ProgramIR, LoopIR, EnumeratorItems),
    append(UnfoldItems, MemoItems, Items0),
    append(Items0, SimplifyItems, Items1),
    append(Items1, ListFormulaItems, Items2),
    append(Items2, IndexicalItems, Items3),
    append(Items3, RecursiveIndexItems, Items4),
    append(Items4, SpliceItems, Items5),
    append(Items5, LoopItems, Items6),
    append(Items6, EnumeratorItems, Items7),
    enforce_stage17_safety(ProgramIR, LoopIR, Items7, OptimisedIR, Items).

optimise_predicate(PredicateNameArity, ProgramIR, OptimisedIR, optimisation_report(Items)) :-
    unfold_predicate(PredicateNameArity, ProgramIR, UnfoldedIR, UnfoldItems),
    memoise_program(UnfoldedIR, MemoisedIR, MemoItems),
    simplify_program(MemoisedIR, SimplifiedIR, SimplifyItems),
    optimise_list_formulas(SimplifiedIR, ListFormulaIR, ListFormulaItems),
    optimise_indexicals(ListFormulaIR, IndexicalIR, IndexicalItems),
    optimise_recursive_index_loops(IndexicalIR, RecursiveIndexIR, RecursiveIndexItems),
    splice_program(RecursiveIndexIR, SplicedIR, SpliceItems),
    convert_deterministic_loops(SplicedIR, LoopIR, LoopItems),
    analyse_enumerators(ProgramIR, LoopIR, EnumeratorItems),
    append(UnfoldItems, MemoItems, Items0),
    append(Items0, SimplifyItems, Items1),
    append(Items1, ListFormulaItems, Items2),
    append(Items2, IndexicalItems, Items3),
    append(Items3, RecursiveIndexItems, Items4),
    append(Items4, SpliceItems, Items5),
    append(Items5, LoopItems, Items6),
    append(Items6, EnumeratorItems, Items7),
    enforce_stage17_safety(ProgramIR, LoopIR, Items7, OptimisedIR, Items).

write_program(OutputPath, ProgramIR) :-
    setup_call_cleanup(
        open(OutputPath, write, Stream),
        write_ir_program(Stream, ProgramIR),
        close(Stream)
    ).

write_ir_program(_, []) :- !.
write_ir_program(Stream, [Clause | Rest]) :-
    ir_clause_term(Clause, Term),
    write_term(Stream, Term, [fullstop(true), nl(true)]),
    write_ir_program(Stream, Rest).

ir_clause_term(ir_clause(_, Head, [], _), Head).
ir_clause_term(ir_clause(_, Head, Body, _), (Head :- BodyTerm)) :-
    goals_to_body(Body, BodyTerm).

goals_to_body([], true).
goals_to_body([Goal], Goal) :-
    !.
goals_to_body([Goal | Rest], (Goal, BodyRest)) :-
    goals_to_body(Rest, BodyRest).

enforce_stage17_safety(OriginalIR, CandidateIR, CandidateItems, FinalIR, FinalItems) :-
    changed_predicates(OriginalIR, CandidateIR, ChangedPreds),
    predicates_to_skip(ChangedPreds, CandidateIR, PredsToSkip),
    (   PredsToSkip == []
    ->  CandidateItemsWithSkips = CandidateItems,
    FinalIR = CandidateIR
    ;   restore_original_predicates(OriginalIR, CandidateIR, PredsToSkip, CandidateIRWithFallback),
    FinalIR = CandidateIRWithFallback,
    skipped_items(PredsToSkip, CandidateIR, SkipItems),
    append(CandidateItems, SkipItems, CandidateItemsWithSkips)
    ),
    filter_report_items_for_skipped_preds(CandidateItemsWithSkips, PredsToSkip, FilteredItems),
    sort(FilteredItems, FinalItems).

predicates_to_skip(_, _, []) :-
    experimental_mode(true),
    !.
predicates_to_skip([], _, []).
predicates_to_skip([Pred | Rest], CandidateIR, PredsToSkip) :-
    classify_predicate_rewrite_safety(CandidateIR, Pred, Safety),
    predicates_to_skip(Rest, CandidateIR, RestPredsToSkip),
    (   Safety == safe
    ->  PredsToSkip = RestPredsToSkip
    ;   PredsToSkip = [pred_safety(Pred, Safety) | RestPredsToSkip]
    ).

classify_predicate_rewrite_safety(ProgramIR, Pred, safe) :-
    \+ clause_matches_predicate_(Pred, ProgramIR),
    !.
classify_predicate_rewrite_safety(ProgramIR, Pred, Safety) :-
    findall(
        ClauseSafety,
        (
            member(ir_clause(_, Head, Body, _), ProgramIR),
            predicate_from_head(Head, Pred),
            classify_clause_safety(Body, ProgramIR, ClauseSafety)
        ),
        ClauseSafeties
    ),
    combine_safeties(ClauseSafeties, Safety).

classify_clause_safety([], _, safe).
classify_clause_safety([Goal | Rest], ProgramIR, Safety) :-
    classify_goal_safety(Goal, GoalSafety0),
    normalise_goal_safety(Goal, GoalSafety0, ProgramIR, GoalSafety),
    classify_clause_safety(Rest, ProgramIR, RestSafety),
    worst_safety_rank(GoalSafety, RestSafety, Safety).

normalise_goal_safety(_Goal, unsafe, _ProgramIR, unsafe) :- !.
normalise_goal_safety(_Goal, safe, _ProgramIR, safe) :- !.
normalise_goal_safety(Goal, unknown, ProgramIR, safe) :-
    callable(Goal),
    functor(Goal, Name, Arity),
    clause_matches_predicate_(Name/Arity, ProgramIR),
    !.
normalise_goal_safety(_Goal, unknown, _ProgramIR, unknown).

combine_safeties([], safe).
combine_safeties([Safety], Safety) :- !.
combine_safeties([Safety | Rest], Combined) :-
    combine_safeties(Rest, RestCombined),
    worst_safety_rank(Safety, RestCombined, Combined).

worst_safety_rank(unsafe, _, unsafe) :- !.
worst_safety_rank(_, unsafe, unsafe) :- !.
worst_safety_rank(unknown, _, unknown) :- !.
worst_safety_rank(_, unknown, unknown) :- !.
worst_safety_rank(safe, safe, safe).

changed_predicates(OriginalIR, CandidateIR, ChangedPreds) :-
    findall(Pred, (
        member(ir_clause(_, Head, _, _), OriginalIR),
        predicate_from_head(Head, Pred)
    ), OriginalPreds0),
    findall(Pred, (
        member(ir_clause(_, Head, _, _), CandidateIR),
        predicate_from_head(Head, Pred)
    ), CandidatePreds0),
    append(OriginalPreds0, CandidatePreds0, AllPreds0),
    sort(AllPreds0, AllPreds),
    include(predicate_changed_between(OriginalIR, CandidateIR), AllPreds, ChangedPreds).

predicate_changed_between(OriginalIR, CandidateIR, Pred) :-
    clauses_for_predicate(OriginalIR, Pred, OriginalClauses),
    clauses_for_predicate(CandidateIR, Pred, CandidateClauses),
    OriginalClauses \== CandidateClauses.

restore_original_predicates(OriginalIR, CandidateIR, PredsToSkip, RestoredIR) :-
    findall(Pred, member(pred_safety(Pred, _), PredsToSkip), PredsToSkipOnly),
    exclude(clause_in_predicates(PredsToSkipOnly), CandidateIR, CandidateKept),
    include(clause_in_predicates(PredsToSkipOnly), OriginalIR, OriginalFallback),
    append(CandidateKept, OriginalFallback, RestoredIR).

skipped_items([], _, []).
skipped_items([pred_safety(Pred, Safety) | Rest], CandidateIR, [skipped(Pred, Safety) | RestItems]) :-
    clause_matches_predicate_(Pred, CandidateIR),
    !,
    skipped_items(Rest, CandidateIR, RestItems).
skipped_items([_ | Rest], CandidateIR, RestItems) :-
    skipped_items(Rest, CandidateIR, RestItems).

filter_report_items_for_skipped_preds([], _, []).
filter_report_items_for_skipped_preds([Item | Rest], PredsToSkip, Filtered) :-
    report_item_predicate(Item, Pred),
    member(pred_safety(Pred, _), PredsToSkip),
    Item \= skipped(_, _),
    !,
    filter_report_items_for_skipped_preds(Rest, PredsToSkip, Filtered).
filter_report_items_for_skipped_preds([Item | Rest], PredsToSkip, [Item | FilteredRest]) :-
    filter_report_items_for_skipped_preds(Rest, PredsToSkip, FilteredRest).

report_item_predicate(Item, Pred) :-
    compound(Item),
    arg(1, Item, Pred),
    Pred = _/_.

predicate_from_head(Head, Name/Arity) :-
    functor(Head, Name, Arity).

clause_matches_predicate_(Pred, ProgramIR) :-
    member(ir_clause(_, Head, _, _), ProgramIR),
    predicate_from_head(Head, Pred),
    !.

clause_in_predicates(Preds, ir_clause(_, Head, _, _)) :-
    predicate_from_head(Head, Pred),
    member(Pred, Preds).

clauses_for_predicate(ProgramIR, Pred, Clauses) :-
    include(clause_with_predicate(Pred), ProgramIR, Clauses).

clause_with_predicate(Pred, ir_clause(_, Head, _, _)) :-
    predicate_from_head(Head, Pred).
