Require logic.
Require equal.
Require nat.
Require le.

Definition lt:
   nat -> nat -> Prop
:= lambda n: nat,
   lambda p: nat,
   le (succ n) p.

Definition lt_zero:
   forall n: nat,
   not (equal nat n zero) ->
   lt zero n
:= nat_induction (lambda n: nat, not (equal nat n zero) -> lt zero n)
      (lambda H1: not (equal nat zero zero),
       H1 (equal_reflexivity nat zero) (lt zero zero))
      (lambda n: nat,
       lambda IH: not (equal nat n zero) -> lt zero n,
       lambda H1: not (equal nat (succ n) zero),
       le_add_succ zero n (le_zero n)).

Definition lt_zero_succ:
   forall n: nat,
   lt zero (succ n)
:= lambda n: nat,
   le_add_succ zero n (le_zero n).

Definition lt_succ:
   forall i: nat,
   lt i (succ i)
:= lambda i: nat,
   le_reflexivity (succ i).

Definition lt_irreflexivity:
   forall i: nat,
   not (lt i i)
:= nat_induction (lambda i: nat, not (lt i i)) (not_le_succ_zero zero)
      (lambda i: nat,
       lambda H1: not (lt i i),
       lambda H2: lt (succ i) (succ i),
       H1 (le_remove_succ (succ i) i H2)).

Definition lt_not_symmetric:
   forall i: nat,
   forall j: nat,
   lt i j ->
   lt j i ->
   False
:= nat_induction
      (lambda i: nat, forall j: nat, lt i j -> lt j i -> False)
      (lambda j: nat, lambda H1: lt zero j, not_le_succ_zero j)
      (lambda i: nat,
       lambda IH: forall j: nat, lt i j -> lt j i -> False,
       nat_induction
          (lambda j: nat, lt (succ i) j -> lt j (succ i) -> False)
          (lambda H1: lt (succ i) zero, 
           lambda H2: lt zero (succ i), 
           not_le_succ_zero (succ i) H1)
          (lambda j: nat,
           lambda IH2: lt (succ i) j -> lt j (succ i) -> False,
           lambda H1: lt (succ i) (succ j),
           lambda H2: lt (succ j) (succ i),
           IH j (le_remove_succ (succ i) j H1)
                (le_remove_succ (succ j) i H2))).

Definition destruct_le:
   forall i: nat,
   forall j: nat,
   le i j ->
   or (equal nat i j) (lt i j)
:= lambda i: nat,
   le_induction i (lambda j: nat, or (equal nat i j) (lt i j))
      (or_left (equal nat i i) (lt i i) (equal_reflexivity nat i))
      (lambda j: nat,
       lambda H1: le i j,
       lambda H2: or (equal nat i j) (lt i j),
       or_right (equal nat i (succ j)) (lt i (succ j)) (le_add_succ i j H1)).

Definition lt_or_le:
   forall i: nat,
   forall j: nat,
   or (lt i j) (le j i)
:= nat_induction
      (lambda i: nat, forall j: nat, or (lt i j) (le j i))
      (nat_induction (lambda i: nat, or (lt zero i) (le i zero))
          (or_right (lt zero zero) (le zero zero) (le_reflexivity zero))
          (lambda i: nat,
           lambda H1: or (lt zero i) (le i zero),
           or_left (lt zero (succ i)) (le (succ i) zero) (lt_zero_succ i)))
      (lambda i: nat,
       lambda H1: forall j: nat, or (lt i j) (le j i),
       nat_induction (lambda j: nat, or (lt (succ i) j) (le j (succ i)))
          (or_right (lt (succ i) zero) (le zero (succ i)) (le_zero (succ i)))
          (lambda j: nat,
           lambda H2: or (lt (succ i) j) (le j (succ i)),
           or_induction (lt i j) (le j i)
              (or (lt (succ i) (succ j)) (le (succ j) (succ i)))
              (H1 j)
              (lambda H3: lt i j,
               or_left (lt (succ i) (succ j)) (le (succ j) (succ i))
                  (le_add_succ (succ i) j H3))
              (lambda H3: le j i,
               or_right (lt (succ i) (succ j)) (le (succ j) (succ i))
                  (le_add_succ j i H3)))).

Definition not_lt_and_ge:
   forall i: nat,
   forall j: nat,
   lt i j ->
   le j i ->
   False
:= lambda i: nat,
   lambda j: nat,
   lambda H1: lt i j,
   lambda H2: le j i,
   or_induction (equal nat j i) (lt j i) False (destruct_le j i H2)
      (lambda H3: equal nat j i, lt_irreflexivity i (rewrite nat (lt i) j i H3 H1))
      (lt_not_symmetric i j H1).

Definition not_lt_zero:
   forall i: nat,
   not (lt i zero)
:= lambda i: nat,
   lambda H: lt i zero,
   not_lt_and_ge i zero H (le_zero i).

Definition lt_add_succ:
   forall n: nat,
   forall p: nat,
   lt n p ->
   lt (succ n) (succ p)
:= lambda n: nat,
   lambda p: nat,
   lambda H1: lt n p,
   le_add_succ (succ n) p H1.

Definition lt_transitivity:
   forall i: nat,
   forall j: nat,
   forall k: nat,
   lt i j ->
   lt j k ->
   lt i k
:= lambda i: nat,
   lambda j: nat,
   lambda k: nat,
   lambda H1: lt i j,
   lambda H2: lt j k,
   le_transitivity (succ i) j k H1 (le_transitivity j (succ j) k (le_succ_refl j) H2).

Definition lt_le_transitivity:
   forall n: nat,
   forall p: nat,
   forall q: nat,
   lt n p ->
   le p q ->
   lt n q
:= lambda n: nat,
   lambda p: nat,
   lambda q: nat,
   lambda H1: lt n p,
   lambda H2: le p q,
   le_induction p (lt n) H1
      (lambda q: nat,
       lambda H1: le p q,
       lambda H2: lt n q,
       le_succ (succ n) q H2)
      q H2.

