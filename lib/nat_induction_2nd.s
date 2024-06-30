Require nat.
Require le.
Require lt.

Definition nat_induction_2nd:
   forall P: nat -> Prop,
   (forall n: nat, (forall p: nat, lt p n -> P p) -> P n) ->
   forall n: nat,
   P n
:= lambda P: nat -> Prop,
   lambda IH: forall n: nat, (forall p: nat, lt p n -> P p) -> P n,
   lambda n: nat,
   nat_induction (lambda n: nat, forall p: nat, lt p n -> P p)
      (lambda p: nat, lambda H: lt p zero, not_le_succ_zero p H (P p))
      (lambda n: nat,
       lambda H1: forall p: nat, lt p n -> P p,
       lambda p: nat,
       lambda H2: lt p (succ n),
       IH p
          (lambda q: nat,
           lambda H3: lt q p,
           H1 q (lt_le_transitivity q p n H3 (le_remove_succ p n H2))))
      (succ n) n (le_reflexivity (succ n)).

