:- module(optimiser, [optimise_file/2, optimise_program/3, optimise_predicate/4]).
:- reexport(parser, [parse_file/2]).

:- use_module(parser).
:- use_module(unfold).
:- use_module(dependency_graph).
:- use_module(common_dependency_hoist).
:- use_module(hierarchical_splice).
:- use_module(memoise).
:- use_module(simplify).
:- use_module(list_formula).
:- use_module(enumerators).
:- use_module(indexical).
:- use_module(recursive_index).
:- use_module(splice).
:- use_module(loop_conversion).
:- use_module(nd_classify).
:- use_module(loop_splice).
:- use_module(nd_to_loop).
:- use_module(loop_dependency_schedule).
:- use_module(safety).
:- use_module(grouped_subterms).

optimise_file(InputFile, OutputFile) :-
    parse_file(InputFile, ProgramIR),
    optimise_program(ProgramIR, OptimisedIR, _Report),
    write_program(OutputFile, OptimisedIR).

optimise_program(ProgramIR, OptimisedIR, optimisation_report(Items)) :-
    unfold_program(ProgramIR, UnfoldedIR, UnfoldItems),
    build_dependency_graph(UnfoldedIR, Graph, GraphItems),
    hoist_common_dependencies(UnfoldedIR, Graph, HoistedIR, HoistItems),
    hierarchical_splice_program(HoistedIR, SplicedHierarchyIR, HSpliceItems),
    schedule_program_dependencies(SplicedHierarchyIR, ScheduledIR, ScheduleItems),
    memoise_program(ScheduledIR, MemoisedIR, MemoItems),
    simplify_program(MemoisedIR, SimplifiedIR, SimplifyItems),
    optimise_list_formulas(SimplifiedIR, ListFormulaIR, ListFormulaItems),
optimise_indexicals(ListFormulaIR, IndexicalIR, IndexicalItems),

rewrite_grouped_subterms(IndexicalIR, GroupedIR, GroupedItems),

optimise_recursive_index_loops(GroupedIR, RecursiveIndexIR, RecursiveIndexItems),
    splice_program(RecursiveIndexIR, SplicedIR, _SpliceItems),
    convert_deterministic_loops(SplicedIR, LoopIR, LoopItems),
loop_splice_program(LoopIR, LoopSpliceIR, LoopSpliceItems),
nd_to_loop_program(LoopSpliceIR, NDLoopIR, NDLoopItems),
nd_classify_program(ProgramIR, _NDClassifiedIR, NDClassifyItems),
analyse_enumerators(ProgramIR, NDLoopIR, EnumeratorItems),
    append(UnfoldItems, GraphItems, Items0),
    append(Items0, HoistItems, Items1),
    append(Items1, HSpliceItems, Items2),
    append(Items2, ScheduleItems, Items3),
    append(Items3, MemoItems, Items4),
    append(Items4, SimplifyItems, Items5),
    append(Items5, ListFormulaItems, Items6),
    append(Items6, IndexicalItems, Items7),
append(Items7, GroupedItems, Items8),

append(Items8, RecursiveIndexItems, Items9),
    append(Items9, LoopItems, Items10),
    append(Items10, LoopSpliceItems, Items11),
    append(Items11, NDLoopItems, Items12),
    append(Items12, NDClassifyItems, Items13),
    append(Items13, EnumeratorItems, Items14),
    enforce_stage17_safety(ProgramIR, NDLoopIR, Items14, OptimisedIR, Items).

optimise_predicate(PredicateNameArity, ProgramIR, OptimisedIR, optimisation_report(Items)) :-
    unfold_predicate(PredicateNameArity, ProgramIR, UnfoldedIR, UnfoldItems),
    build_dependency_graph(UnfoldedIR, Graph, GraphItems),
    hoist_common_dependencies(UnfoldedIR, Graph, HoistedIR, HoistItems),
    hierarchical_splice_program(HoistedIR, SplicedHierarchyIR, HSpliceItems),
    schedule_program_dependencies(SplicedHierarchyIR, ScheduledIR, ScheduleItems),
    memoise_program(ScheduledIR, MemoisedIR, MemoItems),
    simplify_program(MemoisedIR, SimplifiedIR, SimplifyItems),
    optimise_list_formulas(SimplifiedIR, ListFormulaIR, ListFormulaItems),
optimise_indexicals(ListFormulaIR, IndexicalIR, IndexicalItems),

rewrite_grouped_subterms(IndexicalIR, GroupedIR, GroupedItems),

optimise_recursive_index_loops(GroupedIR, RecursiveIndexIR, RecursiveIndexItems),
    splice_program(RecursiveIndexIR, SplicedIR, _SpliceItems),
    convert_deterministic_loops(SplicedIR, LoopIR, LoopItems),
loop_splice_program(LoopIR, LoopSpliceIR, LoopSpliceItems),
nd_to_loop_program(LoopSpliceIR, NDLoopIR, NDLoopItems),
nd_classify_program(ProgramIR, _NDClassifiedIR, NDClassifyItems),
analyse_enumerators(ProgramIR, NDLoopIR, EnumeratorItems),
    append(UnfoldItems, GraphItems, Items0),
    append(Items0, HoistItems, Items1),
    append(Items1, HSpliceItems, Items2),
    append(Items2, ScheduleItems, Items3),
    append(Items3, MemoItems, Items4),
    append(Items4, SimplifyItems, Items5),
    append(Items5, ListFormulaItems, Items6),
    append(Items6, IndexicalItems, Items7),
append(Items7, GroupedItems, Items8),

append(Items8, RecursiveIndexItems, Items9),
    append(Items9, LoopItems, Items10),
    append(Items10, LoopSpliceItems, Items11),
    append(Items11, NDLoopItems, Items12),
    append(Items12, NDClassifyItems, Items13),
    append(Items13, EnumeratorItems, Items14),
    enforce_stage17_safety(ProgramIR, NDLoopIR, Items14, OptimisedIR, Items).

schedule_program_dependencies([], [], []).
schedule_program_dependencies([ir_clause(Id, Head, BodyIn, Meta)|RestIn],
                              [ir_clause(Id, Head, BodyOut, Meta)|RestOut],
                              Report) :-
    schedule_dependencies(BodyIn, [], BodyOut, ClauseReport),
    schedule_program_dependencies(RestIn, RestOut, RestReport),
    append(ClauseReport, RestReport, Report).

write_program(OutputPath, ProgramIR) :-
    setup_call_cleanup(
        open(OutputPath, write, Stream),
        write_ir_program(Stream, ProgramIR),
        close(Stream)
    ).

write_ir_program(_, []) :- !.
write_ir_program(Stream, [Clause | Rest]) :-
    ir_clause_term(Clause, Term),
    copy_term(Term, TermCopy),
    numbervars(TermCopy, 0, _),
    write_term(Stream, TermCopy, [fullstop(true), nl(true), numbervars(true)]),
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
