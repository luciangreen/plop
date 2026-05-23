:- module(enumerators, [analyse_enumerators/3]).

analyse_enumerators(BeforeIR, AfterIR, Report) :-
    collect_enumerator_pairs(BeforeIR, BeforePairs, _),
    collect_enumerator_pairs(AfterIR, AfterPairs, AfterIndexical),
    classify_pairs(BeforePairs, AfterPairs, ClassItems),
    indexical_items(AfterIndexical, IndexicalItems),
    append(ClassItems, IndexicalItems, ReportRaw),
    sort(ReportRaw, Report).

collect_enumerator_pairs(ProgramIR, Pairs, IndexicalPairs) :-
    findall(
        pred_enum(Pred, Enum),
        (
            member(ir_clause(_, Head, Body, _), ProgramIR),
            predicate_from_head(Head, Pred),
            indexical_enumerators(Body, IndexicalEnums),
            member(Goal, Body),
            enumerator_goal(Goal, Enum),
            \+ member(Enum, IndexicalEnums)
        ),
        PairRaw
    ),
    sort(PairRaw, Pairs),
    findall(
        pred_enum(Pred, Enum),
        (
            member(ir_clause(_, Head, Body, _), ProgramIR),
            predicate_from_head(Head, Pred),
            indexical_enumerator(Body, Enum)
        ),
        IndexicalRaw
    ),
    sort(IndexicalRaw, IndexicalPairs).

classify_pairs(BeforePairs, AfterPairs, Items) :-
    findall(
        enumerator(retained, Pred, Enum),
        (member(pred_enum(Pred, Enum), BeforePairs), member(pred_enum(Pred, Enum), AfterPairs)),
        Retained
    ),
    findall(
        enumerator(removed, Pred, Enum),
        (member(pred_enum(Pred, Enum), BeforePairs), \+ member(pred_enum(Pred, Enum), AfterPairs)),
        Removed
    ),
    findall(
        enumerator(created, Pred, Enum),
        (member(pred_enum(Pred, Enum), AfterPairs), \+ member(pred_enum(Pred, Enum), BeforePairs)),
        Created
    ),
    append(Retained, Removed, Items0),
    append(Items0, Created, Items).

indexical_items(IndexicalPairs, Items) :-
    findall(
        indexical_candidate(Pred, Enum),
        member(pred_enum(Pred, Enum), IndexicalPairs),
        Items
    ).

predicate_from_head(Head, Name/Arity) :-
    functor(Head, Name, Arity).

enumerator_goal(Goal, Enum) :-
    callable(Goal),
    functor(Goal, Name, Arity),
    member(Name/Arity, [between/3, member/2, nth0/3, nth1/3, findall/3]),
    Enum = Name/Arity.

indexical_enumerators(Body, Enums) :-
    findall(Enum, indexical_enumerator(Body, Enum), Raw),
    sort(Raw, Enums).

indexical_enumerator(Body, nth1/3) :-
    member(nth1(_, Source, Row), Body),
    member(nth1(_, Row, _), Body),
    Source \= Row,
    !.
indexical_enumerator(Body, nth0/3) :-
    member(nth0(_, Source, Row), Body),
    member(nth0(_, Row, _), Body),
    Source \= Row,
    !.
