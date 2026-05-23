:- module(parser, [parse_file/2, parse_terms/2]).

parse_file(Path, ProgramIR) :-
    setup_call_cleanup(
        open(Path, read, Stream),
        read_terms(Stream, Terms),
        close(Stream)
    ),
    parse_terms(Terms, ProgramIR).

read_terms(Stream, Terms) :-
    read_term(Stream, Term, []),
    (   Term == end_of_file
    ->  Terms = []
    ;   Terms = [Term | Rest],
        read_terms(Stream, Rest)
    ).

parse_terms(Terms, ProgramIR) :-
    parse_terms(Terms, 1, ProgramIR).

parse_terms([], _, []).
parse_terms([Term | Rest], Id0, [ir_clause(Id, Head, BodyList, []) | ParsedRest]) :-
    atom_concat(c, Id0, Id),
    term_to_clause(Term, Head, BodyList),
    Id1 is Id0 + 1,
    parse_terms(Rest, Id1, ParsedRest).

term_to_clause((Head :- Body), Head, Goals) :-
    !,
    body_to_goals(Body, Goals).
term_to_clause(Head, Head, []).

body_to_goals(true, []) :-
    !.
body_to_goals((A, B), [A | Goals]) :-
    !,
    body_to_goals(B, Goals).
body_to_goals(Goal, [Goal]).
