:- module(hierarchical_splice, [hierarchical_splice_program/3]).

hierarchical_splice_program(ProgramIR, OptimisedIR, Report) :-
    hierarchical_splice_clauses(ProgramIR, OptimisedIR, [], Report0),
    sort(Report0, Report).

hierarchical_splice_clauses([], [], Report, Report).
hierarchical_splice_clauses([Clause | Rest], [Updated | UpdatedRest], Report0, Report) :-
    hierarchical_splice_clause(Clause, Updated, Item),
    (   Item == none
    ->  Report1 = Report0
    ;   Report1 = [Item | Report0]
    ),
    hierarchical_splice_clauses(Rest, UpdatedRest, Report1, Report).

hierarchical_splice_clause(ir_clause(Id, Head, Body, Meta), ir_clause(Id, Head, Body, NewMeta), Item) :-
    (   select(hierarchical_splice_ready, Meta, MetaRest)
    ->  NewMeta = MetaRest,
        predicate_from_head(Head, Pred),
        Item = hierarchical_spliced(Pred)
    ;   NewMeta = Meta,
        Item = none
    ).

predicate_from_head(Head, Name/Arity) :-
    callable(Head),
    functor(Head, Name, Arity).
