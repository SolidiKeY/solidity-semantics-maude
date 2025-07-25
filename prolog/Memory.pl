:- use_module(library(clpfd)).

isFId($acc).
isFVal($age).

read(mtMem, _, P, 0) :- isFVal(P).
read(mtMem, Id, P, idC(Id, [P])) :- isFId(P).

read(write(_, Id, S, Val), Id, S, Val).

read(write(Mem, Id1, Sel1, _), Id2, Sel2, X) :-
    (Sel1 #\= Sel2;
     Id1 #\= Id2),
    read(Mem, Id2, Sel2, X).

read(add(_, Id), Id, P, idC(Id, [P])) :- isFId(P).
read(add(_, Id), Id, P, 0) :- isFVal(P).

vDiff(add(Mem, Id1), Id2) :- Id2 #\= Id1, vDiff(Mem, Id2).

ex(0, X) :-
    Mem1 = add(mtMem, IdA),
    vDiff(Mem1, IdB),
    Mem2 = write(Mem1, IdB, $age, _),
    read(Mem2, idA, $age, X).

ex(1, X) :-
    Mem1 = add(mtMem, IdA),
    vDiff(Mem1, IdB),
    Mem2 = write(Mem1, IdB, $acc, _),
    read(Mem2, idA, $acc, X).
