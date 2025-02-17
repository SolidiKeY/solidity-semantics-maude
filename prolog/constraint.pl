:- use_module(library(chr)).

:- chr_constraint eq/2, neq/2, vDiff/2.

eq(X,X) <=> true.
neq(X,X) <=> false.
neq(X,Y) \ neq(X,Y) <=> true.
eq(X,Y), neq(X,Y) <=> false.
eq(X,Y), neq(Y,X) <=> false.

isFId($acc).
isFVal($age).

read(mtMem, _, P, 0) :- isFVal(P).
read(mtMem, Id, P, idC(Id, [P])) :- isFId(P).

read(write(_, Id1, S, Val), Id2, S, Val) :- eq(Id1, Id2).

read(write(Mem, Id1, Sel1, _), Id2, Sel2, X) :-
    (Sel1 \== Sel2;
    neq(Id1, Id2)),
    read(Mem, Id2, Sel2, X).

read(add(_, Id), Id, P, idC(Id, [P])) :- isFId(P).
read(add(_, Id), Id, P, 0) :- isFVal(P).

vDiff(add(Mem, Id1), Id2) <=> neq(Id2, Id1), vDiff(Mem, Id2).

ex(0, X) :-
    Mem1 = add(mtMem, idA),
    vDiff(Mem1, idB),
    Mem2 = write(Mem1, idB, $age, _),
    read(Mem2, idA, $age, X).

ex(1, X) :-
    Mem1 = add(mtMem, idA),
    vDiff(Mem1, idB),
    Mem2 = write(Mem1, idB, $acc, 0),
    read(Mem2, idA, $acc, X).
