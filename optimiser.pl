:- module(optimiser, [optimise_file/2, optimise_program/3, optimise_predicate/4]).

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
    convert_deterministic_loops(SplicedIR, OptimisedIR, LoopItems),
    analyse_enumerators(ProgramIR, OptimisedIR, EnumeratorItems),
    append(UnfoldItems, MemoItems, Items0),
    append(Items0, SimplifyItems, Items1),
    append(Items1, ListFormulaItems, Items2),
    append(Items2, IndexicalItems, Items3),
    append(Items3, RecursiveIndexItems, Items4),
    append(Items4, SpliceItems, Items5),
    append(Items5, LoopItems, Items6),
    append(Items6, EnumeratorItems, Items).

optimise_predicate(PredicateNameArity, ProgramIR, OptimisedIR, optimisation_report(Items)) :-
    unfold_predicate(PredicateNameArity, ProgramIR, UnfoldedIR, UnfoldItems),
    memoise_program(UnfoldedIR, MemoisedIR, MemoItems),
    simplify_program(MemoisedIR, SimplifiedIR, SimplifyItems),
    optimise_list_formulas(SimplifiedIR, ListFormulaIR, ListFormulaItems),
    optimise_indexicals(ListFormulaIR, IndexicalIR, IndexicalItems),
    optimise_recursive_index_loops(IndexicalIR, RecursiveIndexIR, RecursiveIndexItems),
    splice_program(RecursiveIndexIR, SplicedIR, SpliceItems),
    convert_deterministic_loops(SplicedIR, OptimisedIR, LoopItems),
    analyse_enumerators(ProgramIR, OptimisedIR, EnumeratorItems),
    append(UnfoldItems, MemoItems, Items0),
    append(Items0, SimplifyItems, Items1),
    append(Items1, ListFormulaItems, Items2),
    append(Items2, IndexicalItems, Items3),
    append(Items3, RecursiveIndexItems, Items4),
    append(Items4, SpliceItems, Items5),
    append(Items5, LoopItems, Items6),
    append(Items6, EnumeratorItems, Items).

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
