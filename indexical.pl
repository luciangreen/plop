:- module(indexical, [optimise_indexicals/3]).

optimise_indexicals(ProgramIR, ProgramIR, Report) :-
    findall(
        indexical_mapping(Pred, addr(Source, Indices, Value)),
        (
            member(ir_clause(_, Head, Body, _), ProgramIR),
            predicate_from_head(Head, Pred),
            index_chain(Body, Source, Indices, Value)
        ),
        Raw
    ),
sort(Raw, Sorted),

remove_duplicate_addr_shapes(Sorted, Report).

remove_duplicate_addr_shapes([], []).
remove_duplicate_addr_shapes([Item|Rest], [Item|Out]) :-
    Item = indexical_mapping(Pred, addr(_Source, Address, _Value)),
    exclude(same_pred_address(Pred, Address), Rest, Rest1),
    remove_duplicate_addr_shapes(Rest1, Out).

same_pred_address(Pred, Address, indexical_mapping(Pred2, addr(_Source, Address2, _Value))) :-
    Pred == Pred2,
    Address == Address2.
    
predicate_from_head(Head, Name/Arity) :-
    functor(Head, Name, Arity).

index_chain(Body, Source, Indices, Value) :-
    nth_goal(Body, Index, Source, Next),
    \+ produced_value(Body, Source),
    length(Body, MaxDepth),
    continue_chain(Body, Next, [Source], MaxDepth, RestIndices, Value),
    Indices = [Index | RestIndices],
    length(Indices, Len),
    Len >= 2.

continue_chain(Body, Source, Seen, _MaxDepth, [Index], Value) :-
    nth_goal(Body, Index, Source, Value),
    \+ has_nth_source(Body, Value),
    \+ seen_var_or_term(Value, Seen).

continue_chain(Body, Source, Seen, MaxDepth, [Index | Rest], Value) :-
    MaxDepth > 0,
    nth_goal(Body, Index, Source, Next),
    \+ has_nth_source(Body, Source),
    \+ seen_var_or_term(Next, Seen),
    MaxDepth1 is MaxDepth - 1,
    continue_chain(Body, Next, [Source | Seen], MaxDepth1, Rest, Value).

nth_goal(Body, Index, Source, Value) :-
    member(Goal, Body),
    (
        Goal = nth1(Index, Source, Value)
    ;
        Goal = nth0(Index, Source, Value)
    ).

produced_value(Body, Value) :-
    nth_goal(Body, _Index, _Source, Out),
    Out == Value.

has_nth_source(Body, Source) :-
    nth_goal(Body, _Index, In, _Value),
    In == Source.

seen_var_or_term(X, Seen) :-
    member(Y, Seen),
    X == Y,
    !.