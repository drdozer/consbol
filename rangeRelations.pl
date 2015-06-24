/* A validation check and extractor for ranges. */

legalRange(R, Rl, Rr) :- left(R, Rl), right(R, Rr),  Rl >= 0, Rr >= Rl.


/* The Allen's interval algebra relations, slighlty renamed with DNA in mind. */

before_by_range(A, B) :-
  legalRange(A, _, Ar),
  legalRange(B, Bl, _),
  succ(Ar, Ar1),
  Ar1 < Bl.

before_known(A, B) :-
  before_by_range(A, B).

before_known(A, B) :-
  before_asserted(A, B).

before(A, C) :-
  before_known(A, C).

before(A, C) :-
  before_known(A, B),
  before(B, C).

before(A, C) :-
  touches(A, B),
  before(B, C).

before(A, C) :-
  startsWith(B, A),
  before(B, C).

before(A, C) :-
  overlaps(A, B),
  before(B, C).

before(A, C) :-
  within(A, B),
  before(B, C).

before(A, C) :-
  endsWith(A, B),
  before(B, C).

before(A, C) :-
  endsWith(B, A),
  before(B, C).

before(A, C) :-
  areEqual(A, B),
  before(B, C).

touches(A, B) :-
  legalRange(A, _, Ar),
  legalRange(B, Bl, _),
  succ(Ar, Bl).

startsWith(A, B) :-
  legalRange(A, L, Ar),
  legalRange(B, L, Br),
  Ar > Br.

overlaps(A, B) :-
  legalRange(A, Al, Ar),
  legalRange(B, Bl, Br),
  Al < Bl,
  Ar < Br,
  Bl < Ar.

within(A, B) :-
  legalRange(A, Al, Ar),
  legalRange(B, Bl, Br),
  Bl < Al,
  Ar < Br.

endsWith(A, B) :-
  legalRange(A, Al, R),
  legalRange(B, Bl, R),
  Al < Bl.

areEqual(A, B) :-
  legalRange(A, L, R),
  legalRange(B, L, R).


/* Ranges have size, and therefore can be shorter than each-other. */

rangeSize(R, S) :-
  legalRange(R, Rl, Rr),
  plus(L, Rl, Rr),
  plus(L, 1, S).

shorterThan(A, B) :-
  rangeSize(A, As),
  rangeSize(B, Bs),
  As < Bs.

shorterThan(A, B) :-
  startsWith(B, A).

shorterThan(A, B) :-
  endsWith(B, A).

shorterThan(A, B) :-
  within(A, B).


/* Strands */

sameOrientation(A, B) :-
  orientation(A, inline),
  orientation(B, inline).

sameOrientation(A, B) :-
  orientation(A, revCmp),
  orientation(B, revCmp).

sameOrientation(A, B) :-
  before_35(A, B).

sameOrientation(A, B) :-
  before_35(B, A).

differentOrientation(A, B) :-
  orientation(A, inline),
  orientation(B, revCmp).

differentOrientation(A, B) :-
  orientation(A, revCmp),
  orientation(B, inline).

differentOrientation(A, B) :-
  before_33(A, B).

differentOrientation(A, B) :-
  before_33(B, A).

differentOrientation(A, B) :-
  after_55(A, B).

differentOrientation(A, B) :-
  after_55(B, A).


/* Oriented constraints */

before_35(A, B) :-
  orientation(A, inline),
  orientation(B, inline),
  before(A, B).

before_35(A, B) :-
  orientation(A, revCmp),
  orientation(B, revCmp),
  before(B, A).

before_33(A, B) :-
  orientation(A, inline),
  orientation(B, revCmp),
  before(A, B).

before_33(A, B) :-
  orientation(A, revCmp),
  orientation(B, inline),
  before(B, A).
    
after_55(A, B) :-
  orientation(A, inline),
  orientation(B, revCmp),
  before(B, A).

after_55(A, B) :-
  orientation(A, revCmp),
  orientation(B, inline),
  before(A, B).  
  

/* facts */

left(r1, -4).
left(r2, 1).
left(r3, 5).
left(r4, 10).
left(r5, 16).
left(r6, 16).

right(r1, +4).
right(r2, 6).
right(r3, 3).
right(r4, 15).
right(r5, 20).
right(r6, 17).

startsWith(r7, r8).


before_asserted(a, b).
before_asserted(b, c).

