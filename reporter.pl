:- module(reporter, [
    report_lines/2,
    report_text/2,
    print_report/1
]).

% Stage 18 — Reporting Requirements.
%
% Converts optimisation_report/1 terms into human-readable text.

report_lines(optimisation_report(Items), Lines) :-
    !,
    maplist(report_item_line, Items, Lines).
report_lines(Items, Lines) :-
    is_list(Items),
    maplist(report_item_line, Items, Lines).

report_text(Report, Text) :-
    report_lines(Report, Lines),
    atomic_list_concat(Lines, '\n', Text).

print_report(Report) :-
    report_lines(Report, Lines),
    forall(member(Line, Lines), format('~w~n', [Line])).

report_item_line(unfolded(Pred), Line) :-
    !,
    format(atom(Line), 'unfolded: ~w', [Pred]).
report_item_line(memoised(Pred), Line) :-
    !,
    format(atom(Line), 'memoised: ~w', [Pred]).
report_item_line(formula_discovered(Pred, Formula), Line) :-
    !,
    format(atom(Line), 'formula_discovered: ~w => ~w', [Pred, Formula]).
report_item_line(indexical_mapping(Pred, Mapping), Line) :-
    !,
    format(atom(Line), 'indexical_mapping: ~w => ~w', [Pred, Mapping]).
report_item_line(loop_converted(Pred), Line) :-
    !,
    format(atom(Line), 'loop_converted: ~w', [Pred]).
report_item_line(loop_hoisted_count(Count), Line) :-
    !,
    format(atom(Line), 'Loop hoisted deps: ~w', [Count]).
report_item_line(global_hoisted_count(Count), Line) :-
    !,
    format(atom(Line), 'Global hoisted deps: ~w', [Count]).
report_item_line(left_in_loop_count(Count), Line) :-
    !,
    format(atom(Line), 'Deps left in loop: ~w', [Count]).
report_item_line(skipped(Pred, Reason), Line) :-
    !,
    format(atom(Line), 'skipped: ~w (~w)', [Pred, Reason]).
report_item_line(nd_classified(Pred, Class, _Reasons), Line) :-
    !,
    format(atom(Line), 'nd_classified: ~w => ~w', [Pred, Class]).
report_item_line(nd_map_converted(Pred), Line) :-
    !,
    format(atom(Line), 'nd_map_converted: ~w', [Pred]).
report_item_line(nd_fold_converted(Pred), Line) :-
    !,
    format(atom(Line), 'nd_fold_converted: ~w', [Pred]).
report_item_line(nd_flatmap_converted(Pred), Line) :-
    !,
    format(atom(Line), 'nd_flatmap_converted: ~w', [Pred]).
report_item_line(nd_splice_converted(Pred), Line) :-
    !,
    format(atom(Line), 'nd_splice_converted: ~w', [Pred]).
report_item_line(mnn_signature_matched(Pred, Sig), Line) :-
    !,
    format(atom(Line), 'mnn_signature_matched: ~w => ~w', [Pred, Sig]).
report_item_line(mnn_signature_unknown(Pred), Line) :-
    !,
    format(atom(Line), 'mnn_signature_unknown: ~w', [Pred]).
report_item_line(skipped_nd_conversion(Pred, Reason), Line) :-
    !,
    format(atom(Line), 'skipped_nd_conversion: ~w (~w)', [Pred, Reason]).
report_item_line(unsafe_nd_conversion(Pred, Reasons), Line) :-
    !,
    format(atom(Line), 'unsafe_nd_conversion: ~w (~w)', [Pred, Reasons]).
report_item_line(expensive_hoisted(Pred), Line) :-
    !,
    format(atom(Line), 'expensive_hoisted: ~w', [Pred]).
report_item_line(expensive_memoised(Pred), Line) :-
    !,
    format(atom(Line), 'expensive_memoised: ~w', [Pred]).
report_item_line(expensive_unknown(Pred), Line) :-
    !,
    format(atom(Line), 'expensive_unknown: ~w', [Pred]).
report_item_line(Item, Line) :-
    format(atom(Line), '~w', [Item]).
