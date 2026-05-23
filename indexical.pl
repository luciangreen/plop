:- module(indexical, [optimise_indexicals/3]).

optimise_indexicals(ProgramIR, ProgramIR, Report) :-
    findall(
        indexical_mapping(Pred, addr(Indices, Value)),
        (
            member(ir_clause(_, Head, Body, _), ProgramIR),
            predicate_from_head(Head, Pred),
            index_chain(Body, Indices, Value),
            length(Indices, Len),
            Len >= 2
        ),
        ReportRaw
    ),
    sort(ReportRaw, Report).

predicate_from_head(Head, Name/Arity) :-
    functor(Head, Name, Arity).

index_chain(Body, [Index | RestIndices], Value) :-
    nth_goal(Body, _Kind, Index, Source, NextSource),
    \+ produced_value(Body, Source),
    continue_chain(Body, NextSource, RestIndices, Value).

continue_chain(Body, Source, [Index], Value) :-
    nth_goal(Body, _Kind, Index, Source, Value),
    \+ has_nth_source(Body, Value).
continue_chain(Body, Source, [Index | Rest], Value) :-
    nth_goal(Body, _Kind, Index, Source, NextSource),
    continue_chain(Body, NextSource, Rest, Value).

nth_goal(Body, nth1, Index, Source, Value) :-
    member(nth1(Index, Source, Value), Body).
nth_goal(Body, nth0, Index, Source, Value) :-
    member(nth0(Index, Source, Value), Body).

produced_value(Body, Value) :-
    nth_goal(Body, _Kind, _Index, _Source, Out),
    Out == Value.

has_nth_source(Body, Source) :-
    nth_goal(Body, _Kind, _Index, In, _Value),
    In == Source.
