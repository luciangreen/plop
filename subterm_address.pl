:- module(subterm_address, [subterm_with_address/3, subterm_addresses/2]).

subterm_with_address(Term, [], Term).
subterm_with_address(Term, [Index | Rest], Subterm) :-
    integer(Index),
    Index > 0,
    child_at(Term, Index, Child),
    subterm_with_address(Child, Rest, Subterm).

subterm_addresses(Term, Pairs) :-
    collect_subterm_addresses(Term, [], Pairs).

collect_subterm_addresses(Term, Address, [Address-Term | RestPairs]) :-
    findall(
        ChildPairs,
        (
            child_at(Term, Index, Child),
            append(Address, [Index], ChildAddress),
            collect_subterm_addresses(Child, ChildAddress, ChildPairs)
        ),
        NestedLists
    ),
    append(NestedLists, RestPairs).

child_at(Term, Index, Child) :-
    is_list(Term),
    nth1(Index, Term, Child).
child_at(Term, Index, Child) :-
    compound(Term),
    \+ is_list(Term),
    arg(Index, Term, Child).
