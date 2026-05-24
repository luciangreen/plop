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
report_item_line(skipped(Pred, Reason), Line) :-
    !,
    format(atom(Line), 'skipped: ~w (~w)', [Pred, Reason]).
report_item_line(Item, Line) :-
    format(atom(Line), '~w', [Item]).
