:- module(loop_splice, [
    loop_splice_program/3,
    loop_splice_predicate/4,
    detect_spliced_templates/2
]).

% Stage 19c — Loop-Splice Optimisation.
%
% Detects multiple findall calls over the same enumerator list and
% splices them into a single shared loop with multiple accumulators,
% preserving all output templates, answer order, and multiplicity.
%
% Safety rules (same as nd_to_loop):
%   - No transformation when generator contains cut, IO, or meta-calls.
%   - Order is preserved by reversing accumulators at end.
%   - Duplicate answers preserved (accumulator collects all).

:- use_module(safety, [has_side_effects/1, has_cut/1]).

%% loop_splice_program(+ProgramIR, -OptimisedIR, -Report) is det.
loop_splice_program(ProgramIR, OptimisedIR, Report) :-
    splice_clauses(ProgramIR, SplicedClauses, HelperClauses, [], ReportRaw),
    append(SplicedClauses, HelperClauses, OptimisedIR),
    sort(ReportRaw, Report).

splice_clauses([], [], [], Report, Report).
splice_clauses([Clause | Rest], [SC | SCs], HelpersOut, Report0, Report) :-
    splice_clause(Clause, SC, HelpersHere, Item),
    (   nonvar(Item) -> Report1 = [Item | Report0] ; Report1 = Report0 ),
    splice_clauses(Rest, SCs, HelpersRest, Report1, Report),
    append(HelpersHere, HelpersRest, HelpersOut).

splice_clause(ir_clause(Id, Head, Body, Meta), ResultClause, Helpers, Item) :-
    collect_findalls_over_member(Body, FindallGroups),
    (   FindallGroups = [Group | _],
        Group = group(List, Entries),
        length(Entries, N), N >= 2,
        all_entries_safe(Entries)
    ->  build_splice(Head, Id, List, Entries, SpliceCall, Reverses, Helpers),
        remove_findall_goals(Body, Entries, Stripped),
        append(Stripped, [SpliceCall | Reverses], NewBody),
        ResultClause = ir_clause(Id, Head, NewBody, Meta),
        functor(Head, Name, Arity),
        Item = nd_splice_converted(Name/Arity)
    ;   ResultClause = ir_clause(Id, Head, Body, Meta),
        Helpers = []
    ).

%% loop_splice_predicate(+Pred, +ProgramIR, -OptimisedIR, -Report) is det.
loop_splice_predicate(_Pred, ProgramIR, OptimisedIR, Report) :-
    loop_splice_program(ProgramIR, OptimisedIR, Report).

%% detect_spliced_templates(+Body, -Templates) is det.
%
% Return list of findall(Template, Generator, Out) goals that share a
% member/2 enumerator over the same list variable.
detect_spliced_templates(Body, Templates) :-
    collect_findalls_over_member(Body, Groups),
    (   Groups = [group(_, Entries) | _]
    ->  maplist(entry_to_template, Entries, Templates)
    ;   Templates = []
    ).

entry_to_template(entry(T, _G, O, _), findall(T, _, O)).

% -----------------------------------------------------------------------
% Collect findall goals sharing the same member list
% -----------------------------------------------------------------------

collect_findalls_over_member(Body, Groups) :-
    findall(entry(T, G, Out, List), (
        member(findall(T, Generator, Out), Body),
        generator_list(Generator, List)
    ), Entries),
    group_by_list(Entries, Groups).

generator_list((member(_, List), _), List) :- !.
generator_list(member(_, List), List).

group_by_list([], []).
group_by_list([entry(T, G, Out, List) | Rest], [group(List, [entry(T,G,Out,List) | Same]) | Groups]) :-
    include(same_list(List), Rest, Same),
    exclude(same_list(List), Rest, Others),
    group_by_list(Others, Groups).

same_list(List, entry(_, _, _, List2)) :- List == List2.

all_entries_safe(Entries) :-
    \+ (
        member(entry(_, Generator, _, _), Entries),
        generator_unsafe(Generator)
    ).

generator_unsafe(Goal) :-
    (   has_cut(Goal)
    ;   has_side_effects(Goal)
    ;   compound(Goal), Goal = (A, B),
        (generator_unsafe(A) ; generator_unsafe(B))
    ;   compound(Goal), Goal = (A ; B),
        (generator_unsafe(A) ; generator_unsafe(B))
    ;   callable(Goal),
        functor(Goal, Name, Arity),
        member(Name/Arity, [call/1, call/2, call/3, once/1])
    ).

% -----------------------------------------------------------------------
% Build splice loop
% -----------------------------------------------------------------------

build_splice(Head, Id, List, Entries, SpliceCall, Reverses, [BaseClause, StepClause]) :-
    functor(Head, PredName, _),
    atomic_list_concat([splice_loop, PredName, Id], '_', SpliceName),
    length(Entries, N),
    length(AccIns, N),
    length(AccOuts, N),
    numlist(1, N, Indices),
    maplist(fresh_acc_in, Indices, AccIns),
    maplist(fresh_acc_out, Indices, AccOuts),
    maplist(build_step_goals, Entries, AccIns, AccOuts, StepGoalLists),
    flatten(StepGoalLists, StepGoals),
    X = _XVar,
    RecAccIns =  AccOuts,
    RecAccOuts = FinalOuts,
    length(FinalOuts, N),
    maplist(fresh_final_out, Indices, FinalOuts),
    flatten([List, AccIns, FinalOuts], BaseArgList),
    BaseHead =.. [SpliceName | BaseArgList],
    BaseBody_pairs = AccIns,
    base_body_goals(AccIns, FinalOuts, BaseEqs),
    flatten([[X|List_t], AccIns, FinalOuts], StepArgList),
    StepHead =.. [SpliceName | StepArgList],
    flatten([List_t, RecAccIns, RecAccOuts], RecArgList),
    RecCall  =.. [SpliceName | RecArgList],
    append(StepGoals, [RecCall], StepBody),
    BaseClause = ir_clause(base(SpliceName), BaseHead, BaseEqs, []),
    StepClause = ir_clause(step(SpliceName), StepHead, StepBody, []),
    flatten([List, replicate(N, []), FinalOuts], CallArgs),
    SpliceCall =.. [SpliceName | CallArgs],
    maplist(build_reverse, Entries, FinalOuts, Reverses),
    ignore(BaseBody_pairs = BaseBody_pairs).  % suppress singleton warning

fresh_acc_in(I, Acc) :- term_to_atom(acc_in(I), A), term_to_atom(Acc, A).
fresh_acc_out(I, Acc) :- term_to_atom(acc_out(I), A), term_to_atom(Acc, A).
fresh_final_out(I, F) :- term_to_atom(final(I), A), term_to_atom(F, A).

base_body_goals([], [], []).
base_body_goals([AccIn | AccIns], [FinalOut | FinalOuts], [AccIn = FinalOut | Rest]) :-
    base_body_goals(AccIns, FinalOuts, Rest).

build_step_goals(entry(Template, (member(_, _), MapGoal), _, _), AccIn, AccOut, Goals) :-
    !,
    Goals = [MapGoal, AccOut = [Template | AccIn]].
build_step_goals(entry(Template, member(_, _), _, _), AccIn, AccOut, [AccOut = [Template | AccIn]]).
build_step_goals(entry(Template, _, _, _), AccIn, AccOut, [AccOut = [Template | AccIn]]).

build_reverse(entry(_, _, Out, _), FinalOut, reverse(FinalOut, Out)).

replicate(0, _, []) :- !.
replicate(N, X, [X | Rest]) :-
    N > 0,
    N1 is N - 1,
    replicate(N1, X, Rest).

remove_findall_goals(Body, Entries, Stripped) :-
    findall(Goal, (
        member(Goal, Body),
        \+ member(entry(_, _, _, _), Entries),
        \+ (Goal = findall(_, _, Out), member(entry(_, _, Out, _), Entries))
    ), Stripped0),
    (   Stripped0 = []
    ->  Stripped = []
    ;   Stripped = Stripped0
    ).
