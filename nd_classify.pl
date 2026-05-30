:- module(nd_classify, [
    nd_classify_program/3,
    nd_classify_predicate/4,
    nd_goal_class/3,
    nd_body_class/4,
    can_convert_1_to_1/3
]).

% Stage 19 — Nondeterminism-to-Determinism Classifier.
%
% Decides whether Prolog choicepoint code can be converted 1:1 into
% deterministic loops, maps, folds, flatmaps, spliced outputs, or
% memoised dependent loops without changing meaning.
%
% Classes produced:
%   deterministic            - already deterministic, no ND present
%   enumerator               - generates multiple solutions via backtracking
%   map_compatible           - findall/member/template pattern
%   fold_compatible          - findall/member + aggregation (sum, etc.)
%   flatmap_compatible       - nested member enumerators
%   filter_compatible        - findall/member + condition
%   splice_compatible        - repeated expensive call, shared template
%   dependent_nested_loop    - inner loop depends on outer expensive call
%   hoistable_expensive_dependency  - expensive subgoal can be hoisted
%   memo_safe_expensive_dependency  - expensive subgoal, safe to memoise
%   unknown_cost_dependency  - expensive subgoal, cost unknown
%   unsafe_nondeterminism    - contains cut, IO, or other unsafe ND
%   requires_interpreter_construct  - needs call/N, meta-call, etc.

:- use_module(safety, [has_side_effects/1, has_cut/1, classify_goal_safety/2]).

% -----------------------------------------------------------------------
% User declarations (dynamic facts)
% -----------------------------------------------------------------------

:- dynamic nd_decl/2.
% nd_decl(Name/Arity, Declaration)
% Declarations: pure, deterministic, nondet, expensive, memo_safe,
%               no_hoist, no_loop_convert, output_template, enumerator

declare_nd(Pred, Decl) :-
    retractall(nd_decl(Pred, Decl)),
    assertz(nd_decl(Pred, Decl)).

%% nd_classify_program(+ProgramIR, -ClassifiedIR, -Report) is det.
%
% Classify every predicate in ProgramIR and return a ClassifiedIR list
% that annotates each ir_clause with its nd_class, plus a Report list
% of nd_classified/3 items.
nd_classify_program(ProgramIR, ClassifiedIR, Report) :-
    all_predicates(ProgramIR, Preds),
    classify_all_predicates(Preds, ProgramIR, ClassMap, ReportItems),
    annotate_ir(ProgramIR, ClassMap, ClassifiedIR),
    Report = ReportItems.

classify_all_predicates([], _, [], []).
classify_all_predicates([Pred | Rest], ProgramIR, [Pred-Class | ClassRest], [nd_classified(Pred, Class, Reasons) | ReportRest]) :-
    nd_classify_predicate(Pred, ProgramIR, Class, Reasons),
    classify_all_predicates(Rest, ProgramIR, ClassRest, ReportRest).

annotate_ir([], _, []).
annotate_ir([ir_clause(Id, Head, Body, Meta) | Rest], ClassMap, [ir_clause(Id, Head, Body, Meta1) | AnnotRest]) :-
    functor(Head, Name, Arity),
    Pred = Name/Arity,
    (   member(Pred-Class, ClassMap)
    ->  Meta1 = [nd_class(Class) | Meta]
    ;   Meta1 = Meta
    ),
    annotate_ir(Rest, ClassMap, AnnotRest).

%% nd_classify_predicate(+Predicate, +ProgramIR, -Class, -Reasons) is det.
%
% Classify a single predicate given the full program IR.
nd_classify_predicate(Pred, ProgramIR, Class, Reasons) :-
    clauses_for_pred(Pred, ProgramIR, Clauses),
    (   Clauses == []
    ->  Class = deterministic,
        Reasons = [not_defined_in_program]
    ;   classify_clauses(Clauses, ProgramIR, Class, Reasons)
    ).

classify_clauses(Clauses, ProgramIR, Class, Reasons) :-
    (   any_clause_has_unsafe(Clauses)
    ->  Class = unsafe_nondeterminism,
        Reasons = [contains_cut_or_io]
    ;   any_clause_has_meta_call(Clauses)
    ->  Class = requires_interpreter_construct,
        Reasons = [contains_meta_call]
    ;   classify_by_body_patterns(Clauses, ProgramIR, Class, Reasons)
    ).

any_clause_has_unsafe(Clauses) :-
    member(ir_clause(_, _, Body, _), Clauses),
    member(Goal, Body),
    (has_cut(Goal) ; has_side_effects(Goal)),
    !.

any_clause_has_meta_call(Clauses) :-
    member(ir_clause(_, _, Body, _), Clauses),
    member(Goal, Body),
    is_meta_call(Goal),
    !.

is_meta_call(Goal) :-
    callable(Goal),
    functor(Goal, Name, Arity),
    meta_call_pred(Name/Arity).

meta_call_pred(call/1).
meta_call_pred(call/2).
meta_call_pred(call/3).
meta_call_pred(call/4).
meta_call_pred(call/5).
meta_call_pred(once/1).
meta_call_pred(ignore/1).
meta_call_pred(forall/2).
meta_call_pred(maplist/2).
meta_call_pred(maplist/3).
meta_call_pred(maplist/4).
meta_call_pred(bagof/3).
meta_call_pred(setof/3).

classify_by_body_patterns(Clauses, ProgramIR, Class, Reasons) :-
    (   all_clauses_deterministic(Clauses, ProgramIR)
    ->  Class = deterministic,
        Reasons = [no_choicepoints]
    ;   clauses_match_map_pattern(Clauses, ProgramIR)
    ->  Class = map_compatible,
        Reasons = [findall_member_template]
    ;   clauses_match_fold_pattern(Clauses, ProgramIR)
    ->  Class = fold_compatible,
        Reasons = [findall_member_aggregation]
    ;   clauses_match_flatmap_pattern(Clauses, ProgramIR)
    ->  Class = flatmap_compatible,
        Reasons = [nested_member_enumerators]
    ;   clauses_match_filter_pattern(Clauses, ProgramIR)
    ->  Class = filter_compatible,
        Reasons = [findall_member_condition]
    ;   clauses_match_splice_pattern(Clauses, ProgramIR)
    ->  Class = splice_compatible,
        Reasons = [repeated_expensive_shared_template]
    ;   clauses_match_dependent_nested(Clauses, ProgramIR)
    ->  Class = dependent_nested_loop,
        Reasons = [nested_loop_with_expensive_dependency]
    ;   clauses_have_enumerator_call(Clauses, ProgramIR)
    ->  Class = enumerator,
        Reasons = [generates_multiple_solutions]
    ;   Class = unsafe_nondeterminism,
        Reasons = [unrecognised_nd_pattern]
    ).

% -----------------------------------------------------------------------
% Body classification
% -----------------------------------------------------------------------

%% nd_body_class(+Body, +Context, -Class, -DependencyGraph) is det.
nd_body_class(Body, _Context, Class, DepGraph) :-
    (   member(Goal, Body), is_findall_goal(Goal)
    ->  classify_findall_body(Body, Class),
        build_simple_dep_graph(Body, DepGraph)
    ;   body_only_deterministic(Body)
    ->  Class = deterministic,
        DepGraph = []
    ;   member(Goal2, Body), member_call(Goal2)
    ->  Class = enumerator,
        build_simple_dep_graph(Body, DepGraph)
    ;   Class = unknown_cost_dependency,
        build_simple_dep_graph(Body, DepGraph)
    ).

classify_findall_body(Body, Class) :-
    member(findall(Template, Generator, _Result), Body),
    !,
    (   generator_is_map(Generator, Template)
    ->  Class = map_compatible
    ;   generator_is_fold(Generator, Body)
    ->  Class = fold_compatible
    ;   generator_is_flatmap(Generator)
    ->  Class = flatmap_compatible
    ;   generator_has_condition(Generator)
    ->  Class = filter_compatible
    ;   Class = map_compatible
    ).
classify_findall_body(_, unknown_cost_dependency).

generator_is_map((member(X, _List), Goal), Template) :-
    term_variables(Goal, GoalVars),
    term_variables(Template, TplVars),
    term_variables(X, XVars),
    vars_subset(TplVars, GoalVars),
    vars_disjoint_or_subset(XVars, GoalVars).
generator_is_map((member(_X, _List), _Goal), _Template).

generator_is_fold(_Generator, Body) :-
    member(sum_list(_, _), Body), !.
generator_is_fold(_Generator, Body) :-
    member(max_list(_, _), Body), !.
generator_is_fold(_Generator, Body) :-
    member(min_list(_, _), Body), !.

generator_is_flatmap((member(_X, _L1), member(_Y, _L2), _Goal)) :- !.
generator_is_flatmap((member(_X, _L1), member(_Y, _E), _Goal)) :-
    nonvar(_E).

generator_has_condition((member(_X, _List), Cond, _Goal)) :-
    is_condition(Cond), !.
generator_has_condition((member(_X, _List), (Cond, _))) :-
    is_condition(Cond).

is_condition(Goal) :-
    callable(Goal),
    functor(Goal, Name, _Arity),
    member(Name, ['>', '<', '>=', '=<', '=:=', '=\\=', '==', '\\==', '\\+']).

body_only_deterministic([]).
body_only_deterministic([Goal | Rest]) :-
    \+ member_call(Goal),
    \+ is_findall_goal(Goal),
    body_only_deterministic(Rest).

%% nd_goal_class(+Goal, +Context, -Class) is det.
nd_goal_class(Goal, _Context, Class) :-
    (   has_cut(Goal)
    ->  Class = unsafe_nondeterminism
    ;   has_side_effects(Goal)
    ->  Class = unsafe_nondeterminism
    ;   is_meta_call(Goal)
    ->  Class = requires_interpreter_construct
    ;   is_findall_goal(Goal)
    ->  Class = map_compatible
    ;   member_call(Goal)
    ->  Class = enumerator
    ;   known_deterministic_goal(Goal)
    ->  Class = deterministic
    ;   Class = unknown_cost_dependency
    ).

%% can_convert_1_to_1(+Predicate, +ProgramIR, -Decision) is det.
%
% Decision is one of:
%   yes(Class, TransformPlan)
%   no(Reason)
%   unknown(Reason, RequiredDeclarations)
can_convert_1_to_1(Pred, ProgramIR, Decision) :-
    nd_classify_predicate(Pred, ProgramIR, Class, Reasons),
    (   Class = unsafe_nondeterminism
    ->  Decision = no(unsafe_nd(Reasons))
    ;   Class = requires_interpreter_construct
    ->  Decision = no(meta_call_required)
    ;   Class = deterministic
    ->  Decision = yes(deterministic, no_transform_needed)
    ;   Class = map_compatible
    ->  Decision = yes(map_compatible, transform_findall_to_accumulator_loop)
    ;   Class = fold_compatible
    ->  Decision = yes(fold_compatible, transform_findall_to_fold_loop)
    ;   Class = flatmap_compatible
    ->  Decision = yes(flatmap_compatible, transform_to_nested_loops)
    ;   Class = filter_compatible
    ->  Decision = yes(filter_compatible, transform_findall_to_filter_loop)
    ;   Class = splice_compatible
    ->  Decision = yes(splice_compatible, transform_to_spliced_template_loop)
    ;   Class = dependent_nested_loop
    ->  Decision = yes(dependent_nested_loop, transform_to_nested_dependent_loops)
    ;   Class = enumerator
    ->  Decision = unknown(enumerator_may_produce_multiple_answers,
                           [':- deterministic Pred/Arity.', ':- enumerator Pred/Arity.'])
    ;   Decision = unknown(classification_incomplete, [])
    ).

% -----------------------------------------------------------------------
% Helpers
% -----------------------------------------------------------------------

all_predicates(ProgramIR, Preds) :-
    findall(Name/Arity, (
        member(ir_clause(_, Head, _, _), ProgramIR),
        functor(Head, Name, Arity)
    ), Preds0),
    sort(Preds0, Preds).

clauses_for_pred(Name/Arity, ProgramIR, Clauses) :-
    include(clause_matches(Name, Arity), ProgramIR, Clauses).

clause_matches(Name, Arity, ir_clause(_, Head, _, _)) :-
    functor(Head, Name, Arity).

all_clauses_deterministic(Clauses, ProgramIR) :-
    \+ (
        member(ir_clause(_, _, Body, _), Clauses),
        member(Goal, Body),
        (   member_call(Goal)
        ;   is_findall_goal(Goal)
        ;   is_nondet_user_call(Goal, ProgramIR)
        )
    ).

is_nondet_user_call(Goal, ProgramIR) :-
    callable(Goal),
    functor(Goal, Name, Arity),
    Pred = Name/Arity,
    clauses_for_pred(Pred, ProgramIR, Clauses),
    Clauses \== [],
    \+ all_clauses_deterministic(Clauses, ProgramIR).

clauses_match_map_pattern(Clauses, _ProgramIR) :-
    member(ir_clause(_, _, Body, _), Clauses),
    member(findall(Template, Generator, _Out), Body),
    nonvar(Template),
    generator_starts_with_member(Generator),
    !.

clauses_match_fold_pattern(Clauses, _ProgramIR) :-
    member(ir_clause(_, _, Body, _), Clauses),
    member(findall(_Template, Generator, _Vs), Body),
    generator_starts_with_member(Generator),
    (   member(sum_list(_, _), Body)
    ;   member(max_list(_, _), Body)
    ;   member(min_list(_, _), Body)
    ),
    !.

clauses_match_flatmap_pattern(Clauses, _ProgramIR) :-
    member(ir_clause(_, _, Body, _), Clauses),
    member(findall(_Template, Generator, _Out), Body),
    generator_has_nested_member(Generator),
    !.

clauses_match_filter_pattern(Clauses, _ProgramIR) :-
    member(ir_clause(_, _, Body, _), Clauses),
    member(findall(_Template, Generator, _Out), Body),
    generator_starts_with_member(Generator),
    generator_has_condition(Generator, _),
    !.

clauses_match_splice_pattern(Clauses, _ProgramIR) :-
    member(ir_clause(_, _, Body, _), Clauses),
    findall(FA, (
        member(findall(_, Gen, _), Body),
        first_generator_call(Gen, FA)
    ), FAs),
    FAs = [FA | _],
    include(==(FA), FAs, MatchingFAs),
    length(MatchingFAs, Len),
    Len > 1,
    !.

clauses_match_dependent_nested(Clauses, _ProgramIR) :-
    member(ir_clause(_, _, Body, _), Clauses),
    member(findall(_Template, Generator, _Out), Body),
    generator_has_expensive_then_member(Generator),
    !.

clauses_have_enumerator_call(Clauses, _ProgramIR) :-
    member(ir_clause(_, _, Body, _), Clauses),
    member(Goal, Body),
    member_call(Goal),
    !.

generator_starts_with_member((member(_, _), _)) :- !.
generator_starts_with_member((member(_, _))) :- !.

generator_has_nested_member((member(_, _), member(_, _), _)) :- !.
generator_has_nested_member((member(_, _), member(_, _))) :- !.
generator_has_nested_member((_Expensive, member(_, _), _)) :- !.
generator_has_nested_member((_Expensive, member(_, _))) :- !.

generator_has_condition((member(_, _), Cond, _), Cond) :-
    is_condition(Cond), !.
generator_has_condition((member(_, _), (Cond, _)), Cond) :-
    is_condition(Cond), !.

generator_has_expensive_then_member((_Expensive, member(_, _), _)) :- !.
generator_has_expensive_then_member((_Expensive, member(_, _))) :- !.

first_generator_call((Goal, _), FA) :-
    callable(Goal),
    functor(Goal, Name, Arity),
    FA = Name/Arity, !.
first_generator_call(Goal, FA) :-
    callable(Goal),
    functor(Goal, Name, Arity),
    FA = Name/Arity.

build_simple_dep_graph(Body, Graph) :-
    findall(depends(GoalIdx, DepIdx), (
        nth0(GoalIdx, Body, Goal),
        term_variables(Goal, GoalVars),
        nth0(DepIdx, Body, DepGoal),
        DepIdx < GoalIdx,
        term_variables(DepGoal, DepVars),
        shares_variable(GoalVars, DepVars)
    ), Graph).

shares_variable(Vars1, Vars2) :-
    member(V1, Vars1),
    member(V2, Vars2),
    V1 == V2,
    !.

vars_subset([], _).
vars_subset([V | Rest], Superset) :-
    member(S, Superset),
    V == S,
    !,
    vars_subset(Rest, Superset).

vars_disjoint_or_subset(Vars1, Vars2) :-
    (   vars_subset(Vars1, Vars2) -> true
    ;   \+ shares_variable(Vars1, Vars2)
    ).

member_call(member(_, _)).
member_call(between(_, _, _)).
member_call(nth0(_, _, _)).
member_call(nth1(_, _, _)).

is_findall_goal(findall(_, _, _)).
is_findall_goal(bagof(_, _, _)).
is_findall_goal(setof(_, _, _)).

known_deterministic_goal(Goal) :-
    callable(Goal),
    functor(Goal, Name, Arity),
    member(Name/Arity, [
        is/2, >/2, </2, >=/2, =</2, =:=/2, =\=/2,
        =/2, \=/2, ==/2, \==/2,
        functor/3, arg/3, =../2,
        atom/1, number/1, integer/1, float/1, compound/1,
        var/1, nonvar/1, is_list/1, atomic/1, callable/1,
        length/2, append/3, reverse/2, sort/2, msort/2,
        atom_length/2, atom_concat/3, atom_codes/2, atom_chars/2,
        number_codes/2, number_chars/2,
        succ/2, plus/3,
        true/0, fail/0, false/0,
        max_list/2, min_list/2, sum_list/2
    ]).
