:- module(optimiser, [optimise_file/2, optimise_program/3, optimise_predicate/4]).

:- use_module(parser).
:- use_module(unfold).

optimise_file(InputFile, OutputFile) :-
    parse_file(InputFile, ProgramIR),
    optimise_program(ProgramIR, OptimisedIR, _Report),
    write_program(OutputFile, OptimisedIR).

optimise_program(ProgramIR, OptimisedIR, optimisation_report(Items)) :-
    unfold_program(ProgramIR, OptimisedIR, Items).

optimise_predicate(PredicateNameArity, ProgramIR, OptimisedIR, optimisation_report(Items)) :-
    unfold_predicate(PredicateNameArity, ProgramIR, OptimisedIR, Items).

write_program(OutputPath, ProgramIR) :-
    setup_call_cleanup(
        open(OutputPath, write, Stream),
        write_ir_program(Stream, ProgramIR),
        close(Stream)
    ).

write_ir_program(_, []).
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
