Require logic.
Require equal.
Require nat.
Require pred.

Definition contains_le:
   nat -> (nat -> Prop) -> Prop
:= lambda n: nat,
   lambda P: nat -> Prop,
   and (P n) (forall p: nat, P p -> P (succ p)).

Definition le:
   nat -> nat -> Prop
:= lambda n: nat,
   lambda p: nat,
   forall P: nat -> Prop,
   contains_le n P ->
   P p.

Definition le_reflexivity_lemma1:
   forall n: nat,
   not (le n n) ->
   exists (nat -> Prop)
      (lambda P: nat -> Prop, not (contains_le n P -> P n))
:= lambda n: nat,
   lambda H: not (le n n),
   not_forall_exists (nat -> Prop)
      (lambda P: nat -> Prop, contains_le n P -> P n)
      H.

Definition le_reflexivity_discr:
   forall n: nat,
   not (le n n) ->
   nat ->
   Prop
:= lambda n: nat,
   lambda H: not (le n n),
   epsilon (nat -> Prop)
      (lambda P: nat -> Prop, not (contains_le n P -> P n))
      (le_reflexivity_lemma1 n H).

Definition le_reflexivity_lemma2:
   forall n: nat,
   forall H: not (le n n),
   and (contains_le n (le_reflexivity_discr n H))
       (not (le_reflexivity_discr n H n))
:= lambda n: nat,
   lambda H: not (le n n),
   not_impl_is_and
      (contains_le n (le_reflexivity_discr n H))
      (le_reflexivity_discr n H n)
      (epsilon_property (nat -> Prop)
          (lambda P: nat -> Prop, not ((contains_le n P -> P n)))
          (le_reflexivity_lemma1 n H)).

Definition le_reflexivity:
   forall n: nat,
   le n n
:= lambda n: nat,
   double_not (le n n)
      (lambda H: not (le n n),
       and_right
          (contains_le n (le_reflexivity_discr n H))
          (not (le_reflexivity_discr n H n))
          (le_reflexivity_lemma2 n H)
          (and_left
              (le_reflexivity_discr n H n)
              (forall p: nat,
               le_reflexivity_discr n H p ->
               le_reflexivity_discr n H (succ p))
              (and_left (contains_le n (le_reflexivity_discr n H))
                  (not (le_reflexivity_discr n H n))
                  (le_reflexivity_lemma2 n H)))).

Definition not_le_succ_zero:
   forall n: nat,
   le (succ n) zero ->
   False
:= lambda n: nat,
   lambda H: le (succ n) zero,
   H (lambda p: nat, not (equal nat p zero))
     (construct_and
         (not (equal nat (succ n) zero))
         (forall p: nat,
          (not (equal nat p zero)) ->
          (not (equal nat (succ p) zero)))
         (succ_is_not_zero n)
         (lambda p: nat, lambda H: not (equal nat p zero), succ_is_not_zero p))
     (equal_reflexivity nat zero).

Definition le_succ:
   forall n: nat,
   forall p: nat,
   le n p ->
   le n (succ p)
:= lambda n: nat,
   lambda p: nat,
   lambda H1: le n p,
   lambda P: nat -> Prop,
   lambda H2: contains_le n P,
   and_right (P n) (forall p: nat, P p -> P (succ p)) H2 p (H1 P H2).

Definition le_succ_refl:
   forall i: nat,
   le i (succ i)
:= lambda i: nat,
   le_succ i i (le_reflexivity i).

Definition le_zero:
   forall i: nat,
   le zero i
:= nat_induction (le zero) (le_reflexivity zero) (le_succ zero).

Definition le_induction:
   forall n: nat,
   forall P: nat -> Prop,
   P n ->
   (forall p: nat, le n p -> P p -> P (succ p)) ->
   forall p: nat,
   le n p ->
   P p
:= lambda n: nat,
   lambda P: nat -> Prop,
   lambda H1: P n,
   lambda H2: forall p: nat, le n p -> P p -> P (succ p),
   lambda p: nat,
   lambda H3: le n p,
   and_right (le n p) (P p)
      (H3 (lambda p: nat, and (le n p) (P p))
          (construct_and
              (and (le n n) (P n))
              (forall p: nat,
               and (le n p) (P p) ->
               and (le n (succ p)) (P (succ p)))
              (construct_and (le n n) (P n) (le_reflexivity n) H1)
              (lambda p: nat,
               lambda H3: and (le n p) (P p),
               construct_and (le n (succ p)) (P (succ p))
                  (le_succ n p (and_left (le n p) (P p) H3))
                  (H2 p (and_left (le n p) (P p) H3) 
                        (and_right (le n p) (P p) H3))))).

Definition le_transitivity:
   forall i: nat,
   forall j: nat,
   forall k: nat,
   le i j ->
   le j k ->
   le i k
:= lambda i: nat,
   lambda j: nat,
   lambda k: nat,
   lambda H1: le i j,
   le_induction j (le i) H1
      (lambda k: nat, lambda H2: le j k, lambda H3: le i k, le_succ i k H3)
      k.

Definition le_add_succ:
   forall n: nat,
   forall p: nat,
   le n p ->
   le (succ n) (succ p)
:= lambda n: nat,
   le_induction n (lambda p: nat, le (succ n) (succ p))
      (le_reflexivity (succ n))
      (lambda p: nat,
       lambda H1: le n p,
       le_succ (succ n) (succ p)).

Definition le_add_pred_lemma1:
   forall i: nat,
   forall j: nat,
   equal nat j zero ->
   le (pred i) (pred j) ->
   le (pred i) (pred (succ j))
:= lambda i: nat,
   lambda j: nat,
   lambda H1: equal nat j zero,
   rewrite nat (le (pred i)) (pred j) (pred (succ j))
      (rewrite nat (lambda j: nat, equal nat (pred j) (pred (succ j))) zero j 
          (equal_symmetry nat j zero H1)
          (equal_transitivity nat (pred zero) zero (pred (succ zero)) pred_zero
              (equal_symmetry nat (pred (succ zero)) zero (pred_succ zero)))).

Definition le_add_pred_lemma2:
   forall n: nat,
   forall p: nat,
   not (equal nat p zero) ->
   le (pred n) (pred p) ->
   le (pred n) (pred (succ p))
:= lambda n: nat,
   lambda p: nat,
   lambda H1: not (equal nat p zero),
   lambda H2: le (pred n) (pred p),
   rewrite nat (le (pred n)) (succ (pred p)) (pred (succ p))
      (equal_transitivity nat (succ (pred p)) p (pred (succ p)) (succ_pred p H1)
          (equal_symmetry nat (pred (succ p)) p (pred_succ p)))
      (le_succ (pred n) (pred p) H2).

Definition le_add_pred:
   forall n: nat,
   forall p: nat,
   le n p ->
   le (pred n) (pred p)
:= lambda n: nat,
   le_induction n (lambda p: nat, le (pred n) (pred p))
      (le_reflexivity (pred n))
      (lambda p: nat,
       lambda H1: le n p,
       or_induction (equal nat p zero) (not (equal nat p zero))
          (le (pred n) (pred p) -> le (pred n) (pred (succ p)))
          (lambda H: not (equal nat p zero), H)
          (le_add_pred_lemma1 n p)
          (le_add_pred_lemma2 n p)).

Definition le_remove_succ:
   forall n: nat,
   forall p: nat,
   le (succ n) (succ p) ->
   le n p
:= lambda n: nat,
   lambda p: nat,
   lambda H1: le (succ n) (succ p),
   rewrite nat (lambda i: nat, le i p) (pred (succ n)) n (pred_succ n)
      (rewrite nat (le (pred (succ n))) (pred (succ p)) p (pred_succ p)
          (le_add_pred (succ n) (succ p) H1)).

