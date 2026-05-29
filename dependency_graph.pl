:- module(dependency_graph, [build_dependency_graph/3]).

build_dependency_graph(ProgramIR, dependency_graph(Edges), Report) :-
    findall(
        dep(Pred, CalledPred, Count),
        predicate_dependency_count(ProgramIR, Pred, CalledPred, Count),
        Edges0
    ),
    sort(Edges0, Edges),
    findall(Pred, predicate_in_program(ProgramIR, Pred), Preds0),
    sort(Preds0, Preds),
    findall(dependency_graph_built(Pred), member(Pred, Preds), Report).

predicate_dependency_count(ProgramIR, Pred, CalledPred, Count) :-
    member(ir_clause(_, Head, Body, _), ProgramIR),
    predicate_from_head(Head, Pred),
    findall(
        C,
        (
            member(Goal, Body),
            predicate_from_goal(Goal, C)
        ),
        Called0
    ),
    sort(Called0, CalledPreds),
    member(CalledPred, CalledPreds),
    findall(
        1,
        (
            member(ir_clause(_, H2, B2, _), ProgramIR),
            predicate_from_head(H2, Pred),
            member(Goal2, B2),
            predicate_from_goal(Goal2, CalledPred)
        ),
        Hits
    ),
    length(Hits, Count),
    Count > 0.

predicate_in_program(ProgramIR, Pred) :-
    member(ir_clause(_, Head, _, _), ProgramIR),
    predicate_from_head(Head, Pred).

predicate_from_head(Head, Pred) :-
    callable(Head),
    functor(Head, Name, Arity),
    Pred = Name/Arity.

predicate_from_goal(Goal, Pred) :-
    callable(Goal),
    functor(Goal, Name, Arity),
    Pred = Name/Arity.
