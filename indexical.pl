:- module(indexical, [
    optimise_indexicals/3,
    group_address_lookups/2,
    rewrite_index_chain_to_subterm/3,
    reconstruct_output_from_addresses/4,
    common_address_prefix/2,
    local_address/3
]).

optimise_indexicals(ProgramIR, OptimisedIR, Report) :-
    optimise_indexical_clauses(ProgramIR, OptimisedIR, ReportItems),
    sort(ReportItems, Report).

optimise_indexical_clauses([], [], []).
optimise_indexical_clauses(
    [ir_clause(Id, Head, Body, Meta) | Rest],
    [ir_clause(Id, Head, FinalBody, Meta) | RestOptimised],
    Report
) :-
    rewrite_index_chain_to_subterm(Body, BodyWithSubterms, Mappings),
    rewrite_output_construction(BodyWithSubterms, Mappings, FinalBody),
    predicate_from_head(Head, Pred),
    findall(indexical_mapping(Pred, Mapping), member(Mapping, Mappings), ClauseReport),
    optimise_indexical_clauses(Rest, RestOptimised, RestReport),
    append(ClauseReport, RestReport, Report).

predicate_from_head(Head, Name/Arity) :-
    functor(Head, Name, Arity).

rewrite_index_chain_to_subterm(Body, NewBody, Mappings) :-
    nth1_edges(Body, Edges),
    chain_mappings(Edges, MappingInfos),
    mappings_from_infos(MappingInfos, Mappings),
    findall(Position, (
        member(mapping(_, _, _, _, ChainPositions), MappingInfos),
        member(Position, ChainPositions)
    ), ChainPositionsRaw),
    sort(ChainPositionsRaw, ChainPositions),
    rewrite_body_with_subterm_calls(Body, MappingInfos, ChainPositions, 1, NewBody).

mappings_from_infos([], []).
mappings_from_infos([mapping(Source, Address, Value, _, _) | Rest], [addr(Source, Address, Value) | RestMappings]) :-
    mappings_from_infos(Rest, RestMappings).

rewrite_body_with_subterm_calls([], _, _, _, []).
rewrite_body_with_subterm_calls([Goal | Rest], MappingInfos, ChainPositions, Position, NewBody) :-
    (   start_position_mappings(Position, MappingInfos, GoalMappings),
        GoalMappings \= []
    ->  subterm_goals_from_mappings(GoalMappings, SubtermGoals),
        NextPosition is Position + 1,
        rewrite_body_with_subterm_calls(Rest, MappingInfos, ChainPositions, NextPosition, RestBody),
        append(SubtermGoals, RestBody, NewBody)
    ;   memberchk(Position, ChainPositions)
    ->  NextPosition is Position + 1,
        rewrite_body_with_subterm_calls(Rest, MappingInfos, ChainPositions, NextPosition, NewBody)
    ;   NextPosition is Position + 1,
        rewrite_body_with_subterm_calls(Rest, MappingInfos, ChainPositions, NextPosition, RestBody),
        NewBody = [Goal | RestBody]
    ).

subterm_goals_from_mappings([], []).
subterm_goals_from_mappings([mapping(Source, Address, Value, _, _) | Rest], [subterm_with_address(Source, Address, Value) | RestGoals]) :-
    subterm_goals_from_mappings(Rest, RestGoals).

start_position_mappings(Position, MappingInfos, GoalMappings) :-
    start_position_mappings_(MappingInfos, Position, GoalMappings).

start_position_mappings_([], _, []).
start_position_mappings_([mapping(Source, Address, Value, StartPosition, Positions) | Rest], Position, [mapping(Source, Address, Value, StartPosition, Positions) | FilteredRest]) :-
    StartPosition =:= Position,
    !,
    start_position_mappings_(Rest, Position, FilteredRest).
start_position_mappings_([_ | Rest], Position, FilteredRest) :-
    start_position_mappings_(Rest, Position, FilteredRest).

chain_mappings(Edges, Mappings) :-
    root_edges(Edges, Edges, RootEdges),
    chain_mappings_from_roots(RootEdges, Edges, Mappings).

root_edges([], _, []).
root_edges([Edge | Rest], AllEdges, [Edge | RootRest]) :-
    edge_root(Edge, AllEdges),
    !,
    root_edges(Rest, AllEdges, RootRest).
root_edges([_ | Rest], AllEdges, RootRest) :-
    root_edges(Rest, AllEdges, RootRest).

chain_mappings_from_roots([], _, []).
chain_mappings_from_roots([RootEdge | RestRoots], Edges, Mappings) :-
    RootEdge = edge(Source, _, _, _, _),
    paths_from_edge(RootEdge, Edges, [Source], Paths),
    paths_to_mappings(Source, Paths, RootMappings),
    chain_mappings_from_roots(RestRoots, Edges, RestMappings),
    append(RootMappings, RestMappings, Mappings).

paths_to_mappings(_, [], []).
paths_to_mappings(Source, [path(Address, Value, Positions) | Rest], [mapping(Source, Address, Value, StartPosition, Positions) | RestMappings]) :-
    length(Address, Len),
    Len >= 2,
    Positions = [StartPosition | _],
    !,
    paths_to_mappings(Source, Rest, RestMappings).
paths_to_mappings(Source, [_ | Rest], RestMappings) :-
    paths_to_mappings(Source, Rest, RestMappings).

paths_from_edge(edge(_Source, Index, Dest, _Goal, Position), Edges, Visited, Paths) :-
    \+ var_member_eq(Dest, Visited),
    outgoing_edges(Dest, Edges, NextEdges),
    (   NextEdges == []
    ->  Paths = [path([Index], Dest, [Position])]
    ;   paths_from_edges(NextEdges, Edges, [Dest | Visited], ChildPaths),
        prepend_step_to_paths(Index, Position, ChildPaths, Paths)
    ).

paths_from_edges([], _, _, []).
paths_from_edges([Edge | Rest], Edges, Visited, Paths) :-
    paths_from_edge(Edge, Edges, Visited, EdgePaths),
    paths_from_edges(Rest, Edges, Visited, RestPaths),
    append(EdgePaths, RestPaths, Paths).

prepend_step_to_paths(_, _, [], []).
prepend_step_to_paths(Index, Position, [path(Address, Value, Positions) | Rest], [path([Index | Address], Value, [Position | Positions]) | PrefixedRest]) :-
    prepend_step_to_paths(Index, Position, Rest, PrefixedRest).

edge_root(edge(Source, _, _, _, _), Edges) :-
    \+ produced_source(Source, Edges).

produced_source(Source, Edges) :-
    member(edge(_, _, Dest, _, _), Edges),
    Dest == Source.

outgoing_edges(Source, Edges, Outgoing) :-
    outgoing_edges_(Edges, Source, Outgoing).

outgoing_edges_([], _, []).
outgoing_edges_([edge(Src, Index, Dest, Goal, Position) | Rest], Source, Outgoing) :-
    (   Src == Source
    ->  Outgoing = [edge(Src, Index, Dest, Goal, Position) | RestOutgoing]
    ;   Outgoing = RestOutgoing
    ),
    outgoing_edges_(Rest, Source, RestOutgoing).

nth1_edges(Body, Edges) :-
    nth1_edges_(Body, 1, Edges).

nth1_edges_([], _, []).
nth1_edges_([Goal | Rest], Position, Edges) :-
    (   Goal = nth1(Index, Source, Value)
    ->  Edges = [edge(Source, Index, Value, Goal, Position) | RestEdges]
    ;   Edges = RestEdges
    ),
    NextPosition is Position + 1,
    nth1_edges_(Rest, NextPosition, RestEdges).

rewrite_output_construction(Body, Mappings, FinalBody) :-
    (   select(OutputGoal, Body, RestBody),
        output_unify_goal(OutputGoal, OutputVar, OutputTerm),
        choose_single_source_for_output(OutputTerm, Mappings, Source),
        reconstruct_output_from_addresses(Source, OutputTerm, Mappings, OutputGoals),
        OutputGoals \= [],
        term_variables(OutputTerm, OutputVars),
        remove_individual_output_lookups(RestBody, Source, OutputVars, PrunedBody),
        (   OutputGoals = [subterm_with_address(Source, Prefix, OutputTerm)]
        ->  ReplacementGoals = [subterm_with_address(Source, Prefix, OutputVar)]
        ;   append(OutputGoals, [OutputGoal], ReplacementGoals)
        ),
        append(ReplacementGoals, PrunedBody, CandidateBody),
        CandidateBody \== Body
    ->  rewrite_output_construction(CandidateBody, Mappings, FinalBody)
    ;   FinalBody = Body
    ).

output_unify_goal(Goal, Var, Term) :-
    Goal = (Left = Right),
    var(Left),
    nonvar(Right),
    Var = Left,
    Term = Right.
output_unify_goal(Goal, Var, Term) :-
    Goal = (Left = Right),
    var(Right),
    nonvar(Left),
    Var = Right,
    Term = Left.

choose_single_source_for_output(OutputTerm, Mappings, Source) :-
    term_variables(OutputTerm, Vars),
    Vars \= [],
    vars_single_source(Vars, Mappings, Source).

vars_single_source([Var | Rest], Mappings, Source) :-
    variable_source(Var, Mappings, Source),
    vars_single_source_(Rest, Mappings, Source).

vars_single_source_([], _, _).
vars_single_source_([Var | Rest], Mappings, Source) :-
    variable_source(Var, Mappings, VarSource),
    VarSource == Source,
    vars_single_source_(Rest, Mappings, Source).

variable_source(Var, [addr(Source, _Address, Value) | _], Source) :-
    Value == Var,
    !.
variable_source(Var, [_ | Rest], Source) :-
    variable_source(Var, Rest, Source).

remove_individual_output_lookups([], _, _, []).
remove_individual_output_lookups([Goal | Rest], Source, Vars, Pruned) :-
    Goal = subterm_with_address(GoalSource, _Address, Value),
    GoalSource == Source,
    var(Value),
    var_member_eq(Value, Vars),
    !,
    remove_individual_output_lookups(Rest, Source, Vars, Pruned).
remove_individual_output_lookups([Goal | Rest], Source, Vars, [Goal | PrunedRest]) :-
    remove_individual_output_lookups(Rest, Source, Vars, PrunedRest).

group_address_lookups([], []).
group_address_lookups(Lookups, GroupedLookups) :-
    all_lookup_sources_same(Lookups, Source),
    findall(Address, member(subterm_with_address(Source, Address, _), Lookups), Addresses),
    common_address_prefix(Addresses, Prefix),
    Prefix \= [],
    findall(
        Index-Value,
        (
            member(subterm_with_address(Source, Address, Value), Lookups),
            local_address(Prefix, Address, [Index]),
            integer(Index)
        ),
        IndexedValues
    ),
    length(IndexedValues, LookupCount),
    length(Lookups, LookupCount),
    LookupCount > 1,
    sort(IndexedValues, SortedIndexedValues),
    contiguous_indices(SortedIndexedValues, 1),
    values_from_indexed_pairs(SortedIndexedValues, Values),
    !,
    GroupedLookups = [subterm_with_address(Source, Prefix, Values)].
group_address_lookups(Lookups, Lookups).

all_lookup_sources_same([subterm_with_address(Source, _, _) | Rest], Source) :-
    all_lookup_sources_same_(Rest, Source).

all_lookup_sources_same_([], _).
all_lookup_sources_same_([subterm_with_address(Source1, _, _) | Rest], Source) :-
    Source1 == Source,
    all_lookup_sources_same_(Rest, Source).

contiguous_indices([], _).
contiguous_indices([Index-_ | Rest], Index) :-
    NextIndex is Index + 1,
    contiguous_indices(Rest, NextIndex).

values_from_indexed_pairs([], []).
values_from_indexed_pairs([_-Value | Rest], [Value | Values]) :-
    values_from_indexed_pairs(Rest, Values).

reconstruct_output_from_addresses(Source, Output, Mappings, Goals) :-
    reconstruct_term_output(Source, Output, Mappings, Goals).

reconstruct_term_output(Source, OutputVar, Mappings, Goals) :-
    var(OutputVar),
    !,
    (   member(addr(Source, Address, Value), Mappings),
        Value == OutputVar
    ->  Goals = [subterm_with_address(Source, Address, OutputVar)]
    ;   Goals = []
    ).
reconstruct_term_output(Source, OutputTerm, Mappings, [subterm_with_address(Source, Prefix, OutputTerm)]) :-
    compound(OutputTerm),
    output_term_groupable(OutputTerm),
    grouped_output_mapping(Source, OutputTerm, Mappings, Prefix),
    !.
reconstruct_term_output(Source, OutputTerm, Mappings, Goals) :-
    compound(OutputTerm),
    !,
    OutputTerm =.. [_Functor | Args],
    reconstruct_term_args(Source, Args, Mappings, Goals).
reconstruct_term_output(_, _, _, []).

reconstruct_term_args(_, [], _, []).
reconstruct_term_args(Source, [Arg | Rest], Mappings, Goals) :-
    reconstruct_term_output(Source, Arg, Mappings, ArgGoals),
    reconstruct_term_args(Source, Rest, Mappings, RestGoals),
    append(ArgGoals, RestGoals, Goals).

grouped_output_mapping(Source, OutputTerm, Mappings, Prefix) :-
    term_variables(OutputTerm, Vars),
    Vars \= [],
    output_variable_leaf_addresses(OutputTerm, [], ExpectedLeafPairs),
    length(Vars, VarCount),
    length(ExpectedLeafPairs, VarCount),
    mapped_variable_addresses(Source, Vars, Mappings, GlobalPairs),
    findall(Address, member(Address-_, GlobalPairs), Addresses),
    common_address_prefix(Addresses, Prefix),
    local_pairs_from_global(Prefix, GlobalPairs, LocalPairs),
    msort(ExpectedLeafPairs, ExpectedSorted),
    msort(LocalPairs, LocalSorted),
    ExpectedSorted == LocalSorted.

local_pairs_from_global(_, [], []).
local_pairs_from_global(Prefix, [GlobalAddress-Var | Rest], [LocalAddress-Var | LocalRest]) :-
    local_address(Prefix, GlobalAddress, LocalAddress),
    local_pairs_from_global(Prefix, Rest, LocalRest).

mapped_variable_addresses(_, [], _, []).
mapped_variable_addresses(Source, [Var | Rest], Mappings, [Address-Var | RestPairs]) :-
    findall(
        CandidateAddress,
        (
            member(addr(MappingSource, CandidateAddress, MappingValue), Mappings),
            MappingSource == Source,
            MappingValue == Var
        ),
        Matches
    ),
    Matches = [Address],
    mapped_variable_addresses(Source, Rest, Mappings, RestPairs).

output_variable_leaf_addresses(Term, Path, [Path-Term]) :-
    var(Term),
    !.
output_variable_leaf_addresses(Term, Path, Pairs) :-
    is_list(Term),
    !,
    output_variable_leaf_addresses_list(Term, Path, 1, Pairs).
output_variable_leaf_addresses(Term, Path, Pairs) :-
    compound(Term),
    !,
    functor(Term, _Name, Arity),
    output_variable_leaf_addresses_args(Term, Path, 1, Arity, Pairs).
output_variable_leaf_addresses(_Term, _Path, []).

output_variable_leaf_addresses_list([], _Path, _Index, []).
output_variable_leaf_addresses_list([Element | Rest], Path, Index, Pairs) :-
    append(Path, [Index], ChildPath),
    output_variable_leaf_addresses(Element, ChildPath, ElementPairs),
    NextIndex is Index + 1,
    output_variable_leaf_addresses_list(Rest, Path, NextIndex, RestPairs),
    append(ElementPairs, RestPairs, Pairs).

output_variable_leaf_addresses_args(_Term, _Path, Index, Arity, []) :-
    Index > Arity,
    !.
output_variable_leaf_addresses_args(Term, Path, Index, Arity, Pairs) :-
    arg(Index, Term, Arg),
    append(Path, [Index], ChildPath),
    output_variable_leaf_addresses(Arg, ChildPath, ArgPairs),
    NextIndex is Index + 1,
    output_variable_leaf_addresses_args(Term, Path, NextIndex, Arity, RestPairs),
    append(ArgPairs, RestPairs, Pairs).

output_term_groupable(Term) :-
    var(Term),
    !.
output_term_groupable(Term) :-
    is_list(Term),
    !,
    output_term_groupable_list(Term).
output_term_groupable([]) :-
    !.
output_term_groupable(Term) :-
    compound(Term),
    !,
    Term =.. [_Functor | Args],
    output_term_groupable_args(Args).

output_term_groupable_list([]).
output_term_groupable_list([Head | Tail]) :-
    output_term_groupable(Head),
    output_term_groupable_list(Tail).

output_term_groupable_args([]).
output_term_groupable_args([Arg | Rest]) :-
    output_term_groupable(Arg),
    output_term_groupable_args(Rest).

common_address_prefix([], []).
common_address_prefix([Address], Address) :-
    !.
common_address_prefix([Address1, Address2 | Rest], Prefix) :-
    common_prefix_two(Address1, Address2, Prefix12),
    common_address_prefix([Prefix12 | Rest], Prefix).

common_prefix_two([], _, []).
common_prefix_two(_, [], []).
common_prefix_two([A | As], [B | Bs], [A | Prefix]) :-
    A == B,
    !,
    common_prefix_two(As, Bs, Prefix).
common_prefix_two(_, _, []).

local_address(Prefix, Address, LocalAddress) :-
    append(Prefix, LocalAddress, Address).

var_member_eq(Var, [Head | _]) :-
    Var == Head,
    !.
var_member_eq(Var, [_ | Rest]) :-
    var_member_eq(Var, Rest).
