:- module(safety, [
    classify_goal_safety/2,
    classify_body_safety/2,
    has_side_effects/1,
    has_cut/1,
    experimental_mode/1,
    set_experimental_mode/1
]).

% Stage 12 — Safety Requirements.
%
% Every optimisation must be classified as:
%   safe    - the rewrite is guaranteed not to change observable behaviour.
%   unsafe  - the rewrite would move, remove, or duplicate a side-effecting or
%             control-flow-sensitive goal (I/O, assert/retract, cut, etc.).
%   unknown - safety cannot be determined statically (user-defined goals with
%             no known purity declaration).
%
% The experimental-mode flag allows unsafe/unknown rewrites to proceed; it
% defaults to false so that only safe rewrites are applied normally.

:- dynamic experimental_mode_flag/1.
experimental_mode_flag(false).

%% experimental_mode(-Value) is det.
experimental_mode(Value) :-
    experimental_mode_flag(Value).

%% set_experimental_mode(+Value) is det.
set_experimental_mode(Value) :-
    must_be(boolean, Value),
    retractall(experimental_mode_flag(_)),
    assertz(experimental_mode_flag(Value)).

%% classify_goal_safety(+Goal, -Safety) is det.
%
% Classify a single goal as safe, unsafe, or unknown.
classify_goal_safety(Goal, unsafe) :-
    ( Goal == (!) ; has_cut(Goal) ),
    !.
classify_goal_safety(Goal, unsafe) :-
    has_side_effects(Goal),
    !.
classify_goal_safety(Goal, safe) :-
    known_safe_goal(Goal),
    !.
classify_goal_safety(_Goal, unknown).

%% classify_body_safety(+Body, -Safety) is det.
%
% Classify a list of goals.  The result is the worst safety of any member:
%   unsafe > unknown > safe.
classify_body_safety([], safe).
classify_body_safety([Goal | Rest], Safety) :-
    classify_goal_safety(Goal, GoalSafety),
    classify_body_safety(Rest, RestSafety),
    worst_safety(GoalSafety, RestSafety, Safety).

worst_safety(unsafe, _, unsafe) :- !.
worst_safety(_, unsafe, unsafe) :- !.
worst_safety(unknown, _, unknown) :- !.
worst_safety(_, unknown, unknown) :- !.
worst_safety(safe, safe, safe).

%% has_side_effects(+Goal) is semidet.
%
% Succeeds when Goal is a call to a predicate known to produce side effects
% (I/O, global state mutation, or higher-order control that may trigger
% side effects).
has_side_effects(Goal) :-
    callable(Goal),
    functor(Goal, Name, Arity),
    side_effect_predicate(Name/Arity).

side_effect_predicate(write/1).
side_effect_predicate(write/2).
side_effect_predicate(writeln/1).
side_effect_predicate(writeln/2).
side_effect_predicate(print/1).
side_effect_predicate(print/2).
side_effect_predicate(write_canonical/1).
side_effect_predicate(write_term/2).
side_effect_predicate(write_term/3).
side_effect_predicate(format/1).
side_effect_predicate(format/2).
side_effect_predicate(format/3).
side_effect_predicate(read/1).
side_effect_predicate(read_term/2).
side_effect_predicate(read_term/3).
side_effect_predicate(open/3).
side_effect_predicate(open/4).
side_effect_predicate(close/1).
side_effect_predicate(close/2).
side_effect_predicate(nl/0).
side_effect_predicate(nl/1).
side_effect_predicate(put_char/1).
side_effect_predicate(put_char/2).
side_effect_predicate(get_char/1).
side_effect_predicate(get_char/2).
side_effect_predicate(get_code/1).
side_effect_predicate(get_code/2).
side_effect_predicate(peek_char/1).
side_effect_predicate(peek_code/1).
side_effect_predicate(see/1).
side_effect_predicate(tell/1).
side_effect_predicate(seen/0).
side_effect_predicate(told/0).
side_effect_predicate(assert/1).
side_effect_predicate(asserta/1).
side_effect_predicate(assertz/1).
side_effect_predicate(retract/1).
side_effect_predicate(retractall/1).
side_effect_predicate(abolish/1).
side_effect_predicate(nb_setval/2).
side_effect_predicate(nb_getval/2).
side_effect_predicate(b_setval/2).
side_effect_predicate(b_getval/2).
side_effect_predicate(set_flag/2).
side_effect_predicate(flag/3).
side_effect_predicate(findall/3).
side_effect_predicate(bagof/3).
side_effect_predicate(setof/3).
side_effect_predicate(call/1).
side_effect_predicate(call/2).
side_effect_predicate(call/3).
side_effect_predicate(call/4).
side_effect_predicate(once/1).
side_effect_predicate(ignore/1).
side_effect_predicate(forall/2).
side_effect_predicate(maplist/2).
side_effect_predicate(maplist/3).
side_effect_predicate(maplist/4).
side_effect_predicate(aggregate_all/3).

%% has_cut(+Goal) is semidet.
%
% Succeeds when Goal is or contains a cut.
% Uses == for strict equality to avoid accidentally unifying
% uninstantiated variables with the cut atom.
has_cut(Goal) :-
    Goal == (!),
    !.
has_cut(Goal) :-
    compound(Goal),
    Goal =.. [_ | Args],
    member(Arg, Args),
    has_cut(Arg),
    !.

%% known_safe_goal(+Goal) is semidet.
%
% Succeeds when Goal is a call to a predicate known to be pure and
% deterministic (or nondeterministic but without side effects).
known_safe_goal(Goal) :-
    callable(Goal),
    functor(Goal, Name, Arity),
    safe_predicate(Name/Arity).

safe_predicate(is/2).
safe_predicate((>)/2).
safe_predicate((<)/2).
safe_predicate((>=)/2).
safe_predicate((=<)/2).
safe_predicate((=:=)/2).
safe_predicate((=\=)/2).
safe_predicate((=)/2).
safe_predicate((\=)/2).
safe_predicate((==)/2).
safe_predicate((\==)/2).
safe_predicate(functor/3).
safe_predicate(arg/3).
safe_predicate((=..)/2).
safe_predicate(copy_term/2).
safe_predicate(atom/1).
safe_predicate(number/1).
safe_predicate(integer/1).
safe_predicate(float/1).
safe_predicate(compound/1).
safe_predicate(callable/1).
safe_predicate(var/1).
safe_predicate(nonvar/1).
safe_predicate(is_list/1).
safe_predicate(string/1).
safe_predicate(atomic/1).
safe_predicate(true/0).
safe_predicate(fail/0).
safe_predicate(false/0).
safe_predicate(length/2).
safe_predicate(append/3).
safe_predicate(member/2).
safe_predicate(memberchk/2).
safe_predicate(nth0/3).
safe_predicate(nth1/3).
safe_predicate(last/2).
safe_predicate(msort/2).
safe_predicate(sort/2).
safe_predicate(sort/4).
safe_predicate(reverse/2).
safe_predicate(flatten/2).
safe_predicate(between/3).
safe_predicate(succ/2).
safe_predicate(plus/3).
safe_predicate(subterm_with_address/3).
safe_predicate(max_list/2).
safe_predicate(min_list/2).
safe_predicate(sum_list/2).
safe_predicate(numlist/3).
safe_predicate(number_codes/2).
safe_predicate(number_chars/2).
safe_predicate(atom_codes/2).
safe_predicate(atom_chars/2).
safe_predicate(atom_length/2).
safe_predicate(atom_concat/3).
safe_predicate(char_code/2).
safe_predicate(sub_atom/5).
safe_predicate(atom_string/2).
safe_predicate(string_codes/2).
safe_predicate(string_concat/3).
safe_predicate(string_length/2).
safe_predicate(upcase_atom/2).
safe_predicate(downcase_atom/2).
