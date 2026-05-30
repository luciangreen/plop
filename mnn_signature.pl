:- module(mnn_signature, [
    mnn_signature/2,
    mnn_lookup_class/2,
    mnn_transform_hint/2,
    mnn_signature_index/2
]).

% Stage 19e — MNN/O(1) Signature Recognition Layer.
%
% Builds an index of known pattern signatures so that common findall/member
% patterns can be classified in O(1) by index lookup rather than by deep
% structural analysis.
%
% Workflow:
%   1. Build signature index once over the program IR.
%   2. Lookup known patterns by signature (O(1) table lookup).
%   3. Fall back to nd_classify structural analysis only when unknown.
%
% Known signatures:
%   sig_findall_member_template         - findall(T, member(X,L), Ts)
%   sig_findall_member_accumulator      - findall(V, (member(X,L), f(X,V)), Vs)
%   sig_member_filter_template          - findall(X, (member(X,L), cond(X)), Xs)
%   sig_member_nested_member_template   - findall(Z, (member(X,L), g(X,A), member(Y,A)), Zs)
%   sig_repeated_expensive_template     - two findall/member calls, shared expensive g
%   sig_shared_expensive_multi_template - three+ findall/member calls, shared expensive g
%   sig_unknown_cost_dependency         - expensive call without known class
%   sig_meta_call_blocked               - call/N in generator
%   sig_cut_blocked                     - cut in generator
%   sig_io_blocked                      - IO goal in generator

%% mnn_signature(+Clause, -Signature) is det.
%
% Recognise the primary structural signature of a clause.
mnn_signature(ir_clause(_Id, _Head, Body, _Meta), Signature) :-
    (   body_signature(Body, Signature) -> true
    ;   Signature = sig_unknown
    ).

body_signature(Body, sig_cut_blocked) :-
    member(findall(_, Gen, _), Body),
    generator_has_cut(Gen), !.

body_signature(Body, sig_io_blocked) :-
    member(findall(_, Gen, _), Body),
    generator_has_io(Gen), !.

body_signature(Body, sig_meta_call_blocked) :-
    member(findall(_, Gen, _), Body),
    generator_has_meta_call(Gen), !.

body_signature(Body, sig_shared_expensive_multi_template) :-
    findall(List, (
        member(findall(_, (member(_, List), _), _), Body)
    ), Lists),
    Lists = [L | Rest],
    maplist(==(L), Rest),
    length(Lists, N), N >= 3, !.

body_signature(Body, sig_repeated_expensive_template) :-
    findall(List, (
        member(findall(_, (member(_, List), _), _), Body)
    ), Lists),
    Lists = [L, L2 | _],
    L == L2, !.

body_signature(Body, sig_member_nested_member_template) :-
    member(findall(_, (member(_, _), _, member(_, _)), _), Body), !.
body_signature(Body, sig_member_nested_member_template) :-
    member(findall(_, (member(_, _), _, member(_, _), _), _), Body), !.

body_signature(Body, sig_member_filter_template) :-
    member(findall(_, (member(_, _), Cond), _), Body),
    is_condition(Cond), !.
body_signature(Body, sig_member_filter_template) :-
    member(findall(_, (member(_, _), Cond, _), _), Body),
    is_condition(Cond), !.

body_signature(Body, sig_findall_member_accumulator) :-
    member(findall(V, (member(_, _), Goal), Vs), Body),
    \+ V == Goal,
    nonvar(Goal), !.

body_signature(Body, sig_findall_member_template) :-
    member(findall(_, member(_, _), _), Body), !.
body_signature(Body, sig_findall_member_template) :-
    member(findall(_, (member(_, _)), _), Body), !.
body_signature(Body, sig_findall_member_template) :-
    member(findall(_, (member(_, _), _), _), Body), !.

body_signature(Body, sig_unknown_cost_dependency) :-
    member(Goal, Body),
    callable(Goal),
    functor(Goal, Name, _Arity),
    heuristically_expensive(Name), !.

%% mnn_lookup_class(+Signature, -Class) is det.
%
% Map a known signature to an ND classification class.
mnn_lookup_class(sig_findall_member_template, map_compatible).
mnn_lookup_class(sig_findall_member_accumulator, map_compatible).
mnn_lookup_class(sig_member_filter_template, filter_compatible).
mnn_lookup_class(sig_member_nested_member_template, flatmap_compatible).
mnn_lookup_class(sig_repeated_expensive_template, splice_compatible).
mnn_lookup_class(sig_shared_expensive_multi_template, splice_compatible).
mnn_lookup_class(sig_unknown_cost_dependency, unknown_cost_dependency).
mnn_lookup_class(sig_meta_call_blocked, requires_interpreter_construct).
mnn_lookup_class(sig_cut_blocked, unsafe_nondeterminism).
mnn_lookup_class(sig_io_blocked, unsafe_nondeterminism).
mnn_lookup_class(sig_unknown, unknown_cost_dependency).

%% mnn_transform_hint(+Signature, -Hint) is det.
%
% Return a transformation hint for a given signature.
mnn_transform_hint(sig_findall_member_template, accumulator_loop_with_reverse).
mnn_transform_hint(sig_findall_member_accumulator, accumulator_loop_with_reverse).
mnn_transform_hint(sig_member_filter_template, filter_accumulator_loop).
mnn_transform_hint(sig_member_nested_member_template, nested_inner_outer_loops).
mnn_transform_hint(sig_repeated_expensive_template, shared_splice_loop_two_accumulators).
mnn_transform_hint(sig_shared_expensive_multi_template, shared_splice_loop_n_accumulators).
mnn_transform_hint(sig_unknown_cost_dependency, requires_expensive_declaration).
mnn_transform_hint(sig_meta_call_blocked, cannot_transform_meta_call).
mnn_transform_hint(sig_cut_blocked, cannot_transform_cut).
mnn_transform_hint(sig_io_blocked, cannot_transform_io).
mnn_transform_hint(sig_unknown, fallback_to_structural_classifier).

%% mnn_signature_index(+ProgramIR, -Index) is det.
%
% Build a signature index for the entire program.
% Index is a list of (Pred-Signature) pairs for fast lookup.
mnn_signature_index(ProgramIR, Index) :-
    findall(Pred-Sig, (
        member(Clause, ProgramIR),
        Clause = ir_clause(_, Head, _, _),
        functor(Head, Name, Arity),
        Pred = Name/Arity,
        mnn_signature(Clause, Sig)
    ), Pairs0),
    sort(Pairs0, Index).

% -----------------------------------------------------------------------
% Helpers
% -----------------------------------------------------------------------

generator_has_cut(Goal) :-
    (   Goal == (!) -> true
    ;   compound(Goal), Goal = (A, B),
        (generator_has_cut(A) ; generator_has_cut(B))
    ;   compound(Goal), Goal = (A ; B),
        (generator_has_cut(A) ; generator_has_cut(B))
    ).

generator_has_io(Goal) :-
    (   callable(Goal), has_side_effects_simple(Goal) -> true
    ;   compound(Goal), Goal = (A, B),
        (generator_has_io(A) ; generator_has_io(B))
    ;   compound(Goal), Goal = (A ; B),
        (generator_has_io(A) ; generator_has_io(B))
    ).

:- use_module(safety, [has_side_effects/1]).

has_side_effects_simple(Goal) :-
    has_side_effects(Goal).

generator_has_meta_call(Goal) :-
    (   callable(Goal), functor(Goal, Name, Arity),
        member(Name/Arity, [call/1, call/2, call/3, call/4, once/1, forall/2]) -> true
    ;   compound(Goal), Goal = (A, B),
        (generator_has_meta_call(A) ; generator_has_meta_call(B))
    ;   compound(Goal), Goal = (A ; B),
        (generator_has_meta_call(A) ; generator_has_meta_call(B))
    ).

is_condition(Goal) :-
    callable(Goal),
    functor(Goal, Name, _),
    member(Name, ['>', '<', '>=', '=<', '=:=', '=\\=', '==', '\\==', '\\+']).

heuristically_expensive(Name) :-
    member(Name, [expensive, costly, heavy, slow, compute,
                  big_computation, matrix_multiply, solve, search]).
