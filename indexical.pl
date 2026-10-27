:- module(indexical, [
    optimise_indexicals/3
]).

optimise_indexicals(ProgramIR, OptimisedIR, Report) :-
    maplist(optimise_clause, ProgramIR, OptimisedIR, Reports),
    append(Reports, Report0),
    sort(Report0, Report).

optimise_clause(ir_clause(Id, Head, Body, Meta), ir_clause(Id, Head, NewBody, Meta), Report) :-
    predicate_from_head(Head, Pred),
    collect_indexical_mappings(Body, Mappings),
    (   Mappings = [_ | _]
    ->  (   output_reconstruction(Body, Mappings, NewBody, ReportMappings)
        ->  findall(indexical_mapping(Pred, Mapping), member(Mapping, ReportMappings), Report)
        ;   remove_index_chains(Body, Mappings, Remaining),
            mapping_goals(Mappings, SubtermGoals),
            append(Remaining, SubtermGoals, NewBody),
            findall(indexical_mapping(Pred, Mapping), member(Mapping, Mappings), Report)
        )
    ;   NewBody = Body,
        Report = []
    ).

predicate_from_head(Head, Name/Arity) :-
    functor(Head, Name, Arity).

collect_indexical_mappings(Body, Mappings) :-
    collect_indexical_mappings_(Body, Body, Mappings).

collect_indexical_mappings_([], _, []).
collect_indexical_mappings_([nth1(Index, Source, FirstOutput) | Rest], Body, Mappings) :-
    \+ has_nth1_output(Body, Source),
    !,
    complete_chains(Body, Source, FirstOutput, [Index], [Source], ChainMappings),
    append(ChainMappings, Tail, Mappings),
    collect_indexical_mappings_(Rest, Body, Tail).
collect_indexical_mappings_([_ | Rest], Body, Mappings) :-
    collect_indexical_mappings_(Rest, Body, Mappings).

has_nth1_output(Body, Value) :-
    member(nth1(_, _, Output), Body),
    Output == Value.

complete_chains(Body, Root, Current, Prefix, Seen, Mappings) :-
    (   identical_member(Current, Seen)
    ->  Mappings = []
    ;   complete_chains_(Body, Root, Current, Prefix, [Current | Seen], Mappings)
    ).

complete_chains_(Body, Root, Current, Prefix, Seen, Mappings) :-
    matching_nth1_goals(Body, Current, Children),
    (   Children = []
    ->  (   Prefix = [_, _ | _]
        ->  Mappings = [addr(Root, Prefix, Current)]
        ;   Mappings = []
        )
    ;   complete_child_chains(Children, Body, Root, Prefix, Seen, Mappings)
    ).

matching_nth1_goals([], _, []).
matching_nth1_goals([Goal | Rest], Source, Children) :-
    (   Goal = nth1(_, Input, _),
        Input == Source
    ->  Children = [Goal | Tail]
    ;   Children = Tail
    ),
    matching_nth1_goals(Rest, Source, Tail).

complete_child_chains([], _, _, _, _, []).
complete_child_chains([nth1(Index, _, Output) | Rest], Body, Root, Prefix, Seen, Mappings) :-
    append(Prefix, [Index], ChildPrefix),
    complete_chains(Body, Root, Output, ChildPrefix, Seen, ChildMappings),
    complete_child_chains(Rest, Body, Root, Prefix, Seen, RestMappings),
    append(ChildMappings, RestMappings, Mappings).

identical_member(Value, [Candidate | _]) :-
    Value == Candidate,
    !.
identical_member(Value, [_ | Rest]) :-
    identical_member(Value, Rest).

rewrite_index_chain_to_subterm(Body, NewBody, Mappings) :-
    collect_indexical_mappings(Body, Mappings),
    Mappings = [_ | _],
    remove_index_chains(Body, Mappings, Remaining),
    mapping_goals(Mappings, SubtermGoals),
    append(Remaining, SubtermGoals, NewBody).

remove_index_chains(Body, [], Body).
remove_index_chains(Body, Mappings, Remaining) :-
    exclude(index_goal_in_mappings(Body, Mappings), Body, Remaining).

index_goal_in_mappings(Body, Mappings, Goal) :-
    member(addr(Source, Address, _), Mappings),
    address_contains_goal(Body, Source, Address, Goal).

address_contains_goal(Body, Source, [Index | Rest], Goal) :-
    member(Candidate, Body),
    Candidate = nth1(CandidateIndex, Input, Output),
    CandidateIndex == Index,
    Input == Source,
    (   Goal == Candidate
    ;   Rest \= [],
        address_contains_goal(Body, Output, Rest, Goal)
    ).

mapping_goals([], []).
mapping_goals([addr(Source, Address, Value) | Rest],
              [subterm_with_address(Source, Address, Value) | Goals]) :-
    mapping_goals(Rest, Goals).

output_reconstruction(Body, Mappings, NewBody, ReportMappings) :-
    select(Output = Shape, Body, BodyWithoutOutput),
    is_list(Shape),
    Mappings = [addr(Source, _, _) | _],
    collect_output_mappings(Shape, [], Source, Mappings, ReportMappings),
    reconstruct_output_from_addresses(Source, Shape, ReportMappings, OutputGoals),
    OutputGoals \= [],
    remove_index_chains(BodyWithoutOutput, Mappings, Remaining),
    replace_output_shape(OutputGoals, Shape, Output, RewrittenGoals, Replaced),
    (   Replaced == true
    ->  append(Remaining, RewrittenGoals, NewBody)
    ;   append(Remaining, [Output = Shape | OutputGoals], NewBody)
    ).

replace_output_shape([], _, _, [], false).
replace_output_shape(
    [subterm_with_address(Source, Address, Shape) | Rest],
    Shape,
    Output,
    [subterm_with_address(Source, Address, Output) | Rest],
    true
) :-
    !.
replace_output_shape([Goal | Rest], Shape, Output, [Goal | Rewritten], Replaced) :-
    replace_output_shape(Rest, Shape, Output, Rewritten, Replaced).

collect_output_mappings(Shape, Path, Source, Mappings, OutputMappings) :-
    (   is_list(Shape)
    ->  collect_output_mapping_items(Shape, 1, Path, Source, Mappings, OutputMappings)
    ;   member(addr(MappedSource, Address, Value), Mappings),
        Source == MappedSource,
        Shape == Value,
        append(_, Path, Address),
        OutputMappings = [addr(Source, Address, Value)]
    ).

collect_output_mapping_items([], _, _, _, _, []).
collect_output_mapping_items([Item | Rest], Index, Path, Source, Mappings, OutputMappings) :-
    append(Path, [Index], ItemPath),
    collect_output_mappings(Item, ItemPath, Source, Mappings, ItemMappings),
    NextIndex is Index + 1,
    collect_output_mapping_items(Rest, NextIndex, Path, Source, Mappings, RestMappings),
    append(ItemMappings, RestMappings, OutputMappings).

reconstruct_output_from_addresses(Source, Shape, Mappings, Goals) :-
    reconstruct_shape(Source, Shape, [], Mappings, Goals).

reconstruct_shape(Source, Shape, _Prefix, Mappings, [subterm_with_address(Source, Address, Shape)]) :-
    is_list(Shape),
    shape_mapping_prefix(Shape, Mappings, Address),
    Address \= [],
    !.
reconstruct_shape(Source, Shape, Prefix, Mappings, [subterm_with_address(Source, Prefix, Shape)]) :-
    \+ is_list(Shape),
    member(addr(MappedSource, Address, Value), Mappings),
    Source == MappedSource,
    Address == Prefix,
    Value == Shape,
    !.
reconstruct_shape(Source, Shape, Prefix, Mappings, Goals) :-
    is_list(Shape),
    reconstruct_shape_items(Shape, 1, Source, Prefix, Mappings, Goals).

reconstruct_shape_items([], _, _, _, _, []).
reconstruct_shape_items([Item | Rest], Index, Source, Prefix, Mappings, Goals) :-
    append(Prefix, [Index], ItemPrefix),
    reconstruct_shape(Source, Item, ItemPrefix, Mappings, ItemGoals),
    NextIndex is Index + 1,
    reconstruct_shape_items(Rest, NextIndex, Source, Prefix, Mappings, RestGoals),
    append(ItemGoals, RestGoals, Goals).

shape_mapping_prefix(Shape, Mappings, Prefix) :-
    shape_leaves(Shape, [], Leaves),
    maplist(mapping_address(Mappings), Leaves, Addresses),
    common_address_prefix(Addresses, Prefix),
    maplist(local_address(Prefix), Addresses, LocalPaths),
    maplist(shape_leaf_path, Leaves, LeafPaths),
    LocalPaths == LeafPaths.

shape_leaves(Shape, Prefix, Leaves) :-
    (   is_list(Shape)
    ->  shape_leaf_items(Shape, 1, Prefix, Leaves)
    ;   Leaves = [leaf(Prefix, Shape)]
    ).

shape_leaf_items([], _, _, []).
shape_leaf_items([Item | Rest], Index, Prefix, Leaves) :-
    append(Prefix, [Index], ItemPrefix),
    shape_leaves(Item, ItemPrefix, ItemLeaves),
    NextIndex is Index + 1,
    shape_leaf_items(Rest, NextIndex, Prefix, RestLeaves),
    append(ItemLeaves, RestLeaves, Leaves).

mapping_address(Mappings, leaf(_, Value), Address) :-
    member(addr(_, Address, MappedValue), Mappings),
    Value == MappedValue.

shape_leaf_path(leaf(Path, _), Path).

common_address_prefix([Address | Rest], Prefix) :-
    common_address_prefix_(Rest, Address, Prefix).

common_address_prefix_([], Prefix, Prefix).
common_address_prefix_([Address | Rest], Prefix0, Prefix) :-
    common_prefix(Prefix0, Address, Prefix1),
    common_address_prefix_(Rest, Prefix1, Prefix).

common_prefix([A | As], [B | Bs], [A | Rest]) :-
    A == B,
    !,
    common_prefix(As, Bs, Rest).
common_prefix(_, _, []).

local_address(Prefix, Address, Local) :-
    append(Prefix, Local, Address).
