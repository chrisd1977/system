Require logic.
Require equal.
Require nat.
Require lt.
Require nat_induction_2nd.
Require lt_eq_gt_cases.

Definition satisfies_nat_recursion:
   forall P: nat -> Type,
   forall p_zero: P zero,
   forall p_succ: forall i: nat, P i -> P (succ i),
   (forall i: nat, P i -> Prop) ->
   Prop
:= lambda P: nat -> Type,
   lambda p_zero: P zero,
   lambda p_succ: forall i: nat, P i -> P (succ i),
   lambda Q: forall i: nat, P i -> Prop,
   and (Q zero p_zero)
       (forall i: nat, forall p: P i, Q i p -> Q (succ i) (p_succ i p)).

Definition is_nat_recursion:
   forall P: nat -> Type,
   forall p_zero: P zero,
   forall p_succ: forall i: nat, P i -> P (succ i),
   forall i: nat,
   P i ->
   Prop
:= lambda P: nat -> Type,
   lambda p_zero: P zero,
   lambda p_succ: forall i: nat, P i -> P (succ i),
   lambda i: nat,
   lambda p: P i,
   forall Q: forall i: nat, P i -> Prop,
   satisfies_nat_recursion P p_zero p_succ Q ->
   Q i p.

Definition is_nat_recursion_zero:
   forall P: nat -> Type,
   forall p_zero: P zero,
   forall p_succ: forall i: nat, P i -> P (succ i),
   is_nat_recursion P p_zero p_succ zero p_zero
:= lambda P: nat -> Type,
   lambda p_zero: P zero,
   lambda p_succ: forall i: nat, P i -> P (succ i),
   lambda Q: forall i: nat, P i -> Prop,
   and_left (Q zero p_zero) (forall i: nat, forall p: P i, Q i p -> Q (succ i) (p_succ i p)).

Definition is_nat_recursion_succ:
   forall P: nat -> Type,
   forall p_zero: P zero,
   forall p_succ: forall i: nat, P i -> P (succ i),
   forall i: nat,
   forall p: P i,
   is_nat_recursion P p_zero p_succ i p ->
   is_nat_recursion P p_zero p_succ (succ i) (p_succ i p)
:= lambda P: nat -> Type,
   lambda p_zero: P zero,
   lambda p_succ: forall i: nat, P i -> P (succ i),
   lambda i: nat,
   lambda p: P i,
   lambda H1: is_nat_recursion P p_zero p_succ i p,
   lambda Q: forall i: nat, P i -> Prop,
   lambda H2: satisfies_nat_recursion P p_zero p_succ Q,
   and_right (Q zero p_zero) (forall i: nat, forall p: P i, Q i p -> Q (succ i) (p_succ i p))
      H2 i p 
      (H1 Q H2).

Definition exists_nat_recursion_succ:
   forall P: nat -> Type,
   forall p_zero: P zero,
   forall p_succ: forall i: nat, P i -> P (succ i),
   forall i: nat,
   exists (P i) (is_nat_recursion P p_zero p_succ i) ->
   exists (P (succ i)) (is_nat_recursion P p_zero p_succ (succ i))
:= lambda P: nat -> Type,
   lambda p_zero: P zero,
   lambda p_succ: forall i: nat, P i -> P (succ i),
   lambda i: nat,
   lambda H1: exists (P i) (is_nat_recursion P p_zero p_succ i),
   construct_exists (P (succ i)) (is_nat_recursion P p_zero p_succ (succ i))
      (p_succ i (epsilon (P i) (is_nat_recursion P p_zero p_succ i) H1))
      (is_nat_recursion_succ P p_zero p_succ i
          (epsilon (P i) (is_nat_recursion P p_zero p_succ i) H1)
          (epsilon_property (P i) (is_nat_recursion P p_zero p_succ i) H1)).

Definition nat_recursion_exists:
   forall P: nat -> Type,
   forall p_zero: P zero,
   forall p_succ: forall i: nat, P i -> P (succ i),
   forall i: nat,
   exists (P i) (is_nat_recursion P p_zero p_succ i)
:= lambda P: nat -> Type,
   lambda p_zero: P zero,
   lambda p_succ: forall i: nat, P i -> P (succ i),
   nat_induction (lambda i: nat, exists (P i) (is_nat_recursion P p_zero p_succ i))
      (construct_exists (P zero) (is_nat_recursion P p_zero p_succ zero) p_zero
          (is_nat_recursion_zero P p_zero p_succ))
      (exists_nat_recursion_succ P p_zero p_succ).

Definition nat_recursion:
   forall P: nat -> Type,
   forall p_zero: P zero,
   forall p_succ: forall i: nat, P i -> P (succ i),
   forall i: nat,
   P i
:= lambda P: nat -> Type,
   lambda p_zero: P zero,
   lambda p_succ: forall i: nat, P i -> P (succ i),
   lambda i: nat,
   epsilon (P i) (is_nat_recursion P p_zero p_succ i)
      (nat_recursion_exists P p_zero p_succ i).

Definition nat_recursion_is_nat_recursion:
   forall P: nat -> Type,
   forall p_zero: P zero,
   forall p_succ: forall i: nat, P i -> P (succ i),
   forall i: nat,
   is_nat_recursion P p_zero p_succ i (nat_recursion P p_zero p_succ i)
:= lambda P: nat -> Type,
   lambda p_zero: P zero,
   lambda p_succ: forall i: nat, P i -> P (succ i),
   lambda i: nat,
   epsilon_property (P i) (is_nat_recursion P p_zero p_succ i)
      (nat_recursion_exists P p_zero p_succ i).

Definition partial_nat_recursion_for_zero:
   forall P: nat -> Type,
   forall p_zero: P zero,
   forall p_succ: forall i: nat, P i -> P (succ i),
   forall i: nat,
   P i ->
   Prop
:= lambda P: nat -> Type,
   lambda p_zero: P zero,
   lambda p_succ: forall i: nat, P i -> P (succ i),
   lt_eq_gt_cases (lambda i: nat, P i -> Prop) zero
      (lambda i: nat, lambda p: P i, True)
      (equal (P zero) p_zero)
      (lambda i: nat, lambda p: P i, True).

Definition partial_nat_recursion_for_zero_zero:
   forall P: nat -> Type,
   forall p_zero: P zero,
   forall p_succ: forall i: nat, P i -> P (succ i),
   partial_nat_recursion_for_zero P p_zero p_succ zero p_zero
:= lambda P: nat -> Type,
   lambda p_zero: P zero,
   lambda p_succ: forall i: nat, P i -> P (succ i),
   rewrite (P zero -> Prop) (lambda Q: P zero -> Prop, Q p_zero) (equal (P zero) p_zero)
      (partial_nat_recursion_for_zero P p_zero p_succ zero)
      (equal_symmetry (P zero -> Prop) (partial_nat_recursion_for_zero P p_zero p_succ zero)
          (equal (P zero) p_zero)
          (lt_eq_gt_cases_equal (lambda i: nat, P i -> Prop) zero
              (lambda i: nat, lambda p: P i, True)
              (equal (P zero) p_zero)
              (lambda i: nat, lambda p: P i, True)))
      (equal_reflexivity (P zero) p_zero).

Definition partial_nat_recursion_for_zero_succ:
   forall P: nat -> Type,
   forall p_zero: P zero,
   forall p_succ: forall i: nat, P i -> P (succ i),
   forall i: nat,
   forall p2: P i,
   partial_nat_recursion_for_zero P p_zero p_succ i p2 ->
   partial_nat_recursion_for_zero P p_zero p_succ (succ i) (p_succ i p2)
:= lambda P: nat -> Type,
   lambda p_zero: P zero,
   lambda p_succ: forall i: nat, P i -> P (succ i),
   lambda i: nat,
   lambda p2: P i,
   lambda H2: partial_nat_recursion_for_zero P p_zero p_succ i p2,
   rewrite (P (succ i) -> Prop) (lambda Q: P (succ i) -> Prop, Q (p_succ i p2))
      (lambda p: P (succ i), True)
      (partial_nat_recursion_for_zero P p_zero p_succ (succ i))
      (equal_symmetry (P (succ i) -> Prop) 
          (partial_nat_recursion_for_zero P p_zero p_succ (succ i))
          (lambda p: P (succ i), True)
          (lt_eq_gt_cases_greater (lambda i: nat, P i -> Prop) zero
              (lambda i: nat, lambda p: P i, True)
              (equal (P zero) p_zero)
              (lambda i: nat, lambda p: P i, True)
              (succ i)
              (lt_zero_succ i)))
      (lambda P: Prop, lambda p: P, p).

Definition nat_recursion_zero_is_p_zero:
   forall P: nat -> Type,
   forall p_zero: P zero,
   forall p_succ: forall i: nat, P i -> P (succ i),
   forall p: P zero,
   is_nat_recursion P p_zero p_succ zero p ->
   equal (P zero) p_zero p
:= lambda P: nat -> Type,
   lambda p_zero: P zero,
   lambda p_succ: forall i: nat, P i -> P (succ i),
   lambda p: P zero,
   lambda H1: is_nat_recursion P p_zero p_succ zero p,
   rewrite (P zero -> Prop) (lambda Q: P zero -> Prop, Q p)
      (lt_eq_gt_cases (lambda i: nat, P i -> Prop) zero (lambda i: nat, lambda p: P i, True)
          (equal (P zero) p_zero)
          (lambda i: nat, lambda p: P i, True)
          zero)
      (equal (P zero) p_zero)
      (lt_eq_gt_cases_equal (lambda i: nat, P i -> Prop) zero
          (lambda i: nat, lambda p: P i, True)
          (equal (P zero) p_zero)
          (lambda i: nat, lambda p: P i, True))
      (H1 (partial_nat_recursion_for_zero P p_zero p_succ)
          (construct_and (partial_nat_recursion_for_zero P p_zero p_succ zero p_zero)
              (forall i: nat,
               forall p: P i,
               partial_nat_recursion_for_zero P p_zero p_succ i p ->
               partial_nat_recursion_for_zero P p_zero p_succ (succ i) (p_succ i p))
              (partial_nat_recursion_for_zero_zero P p_zero p_succ)
              (partial_nat_recursion_for_zero_succ P p_zero p_succ))).

Definition nat_recursion_unique_prop:
   forall P: nat -> Type,
   forall p_zero: P zero,
   forall p_succ: forall i: nat, P i -> P (succ i),
   nat ->
   Prop
:= lambda P: nat -> Type,
   lambda p_zero: P zero,
   lambda p_succ: forall i: nat, P i -> P (succ i),
   lambda i: nat,
   forall p1: P i,
   forall p2: P i,
   is_nat_recursion P p_zero p_succ i p1 ->
   is_nat_recursion P p_zero p_succ i p2 ->
   equal (P i) p1 p2.

Definition nat_recursion_zero_unique:
   forall P: nat -> Type,
   forall p_zero: P zero,
   forall p_succ: forall i: nat, P i -> P (succ i),
   forall i: nat,
   equal nat i zero ->
   nat_recursion_unique_prop P p_zero p_succ i
:= lambda P: nat -> Type,
   lambda p_zero: P zero,
   lambda p_succ: forall i: nat, P i -> P (succ i),
   lambda i: nat,
   lambda H1: equal nat i zero,
   rewrite nat (nat_recursion_unique_prop P p_zero p_succ) zero i
      (equal_symmetry nat i zero H1)
      (lambda p1: P zero,
       lambda p2: P zero,
       lambda H2: is_nat_recursion P p_zero p_succ zero p1,
       lambda H3: is_nat_recursion P p_zero p_succ zero p2,
       equal_transitivity (P zero) p1 p_zero p2
          (equal_symmetry (P zero) p_zero p1
              (nat_recursion_zero_is_p_zero P p_zero p_succ p1 H2))
          (nat_recursion_zero_is_p_zero P p_zero p_succ p2 H3)).

Definition partial_nat_recursion:
   forall P: nat -> Type,
   forall p_zero: P zero,
   forall p_succ: forall i: nat, P i -> P (succ i),
   forall j: nat,
   forall i: nat,
   P i ->
   Prop
:= lambda P: nat -> Type,
   lambda p_zero: P zero,
   lambda p_succ: forall i: nat, P i -> P (succ i),
   lambda j: nat,
   lt_eq_gt_cases (lambda i: nat, P i -> Prop) (succ j)
      (lambda i: nat, equal (P i) (nat_recursion P p_zero p_succ i))
      (equal (P (succ j)) (p_succ j (nat_recursion P p_zero p_succ j)))
      (lambda i: nat, lambda p: P i, True).

Definition partial_nat_recursion_zero:
   forall P: nat -> Type,
   forall p_zero: P zero,
   forall p_succ: forall i: nat, P i -> P (succ i),
   forall i: nat,
   (forall j: nat, lt j i -> nat_recursion_unique_prop P p_zero p_succ j) ->
   forall j: nat,
   equal nat i (succ j) ->
   partial_nat_recursion P p_zero p_succ j zero p_zero
:= lambda P: nat -> Type,
   lambda p_zero: P zero,
   lambda p_succ: forall i: nat, P i -> P (succ i),
   lambda i: nat,
   lambda H1: forall j: nat, lt j i -> nat_recursion_unique_prop P p_zero p_succ j,
   lambda j: nat,
   lambda H2: equal nat i (succ j),
   rewrite (P zero -> Prop) (lambda Q: P zero -> Prop, Q p_zero)
      (equal (P zero) (nat_recursion P p_zero p_succ zero))
      (partial_nat_recursion P p_zero p_succ j zero)
      (equal_symmetry (P zero -> Prop) (partial_nat_recursion P p_zero p_succ j zero)
          (equal (P zero) (nat_recursion P p_zero p_succ zero))
          (lt_eq_gt_cases_smaller (lambda i: nat, P i -> Prop) (succ j)
              (lambda i: nat, equal (P i) (nat_recursion P p_zero p_succ i))
              (equal (P (succ j)) (p_succ j (nat_recursion P p_zero p_succ j)))
              (lambda i: nat, lambda p: P i, True)
              zero
              (lt_zero_succ j)))
      (H1 zero (rewrite_rev nat (lt zero) i (succ j) H2 (lt_zero_succ j))
          (nat_recursion P p_zero p_succ zero)
          p_zero
          (nat_recursion_is_nat_recursion P p_zero p_succ zero)
          (is_nat_recursion_zero P p_zero p_succ)).

Definition partial_nat_recursion_succ_smaller:
   forall P: nat -> Type,
   forall p_zero: P zero,
   forall p_succ: forall i: nat, P i -> P (succ i),
   forall i: nat,
   (forall j: nat, lt j i -> nat_recursion_unique_prop P p_zero p_succ j) ->
   forall j: nat,
   equal nat i (succ j) ->
   forall k: nat,
   lt k j ->
   forall p: P k,
   partial_nat_recursion P p_zero p_succ j k p ->
   partial_nat_recursion P p_zero p_succ j (succ k) (p_succ k p)
:= lambda P: nat -> Type,
   lambda p_zero: P zero,
   lambda p_succ: forall i: nat, P i -> P (succ i),
   lambda i: nat,
   lambda H1: forall j: nat, lt j i -> nat_recursion_unique_prop P p_zero p_succ j,
   lambda j: nat,
   lambda H2: equal nat i (succ j),
   lambda k: nat,
   lambda H3: lt k j,
   lambda p: P k,
   lambda H4: partial_nat_recursion P p_zero p_succ j k p,
   rewrite_rev (P (succ k) -> Prop) (lambda q: P (succ k) -> Prop, q (p_succ k p))
      (partial_nat_recursion P p_zero p_succ j (succ k))
      (equal (P (succ k)) (nat_recursion P p_zero p_succ (succ k)))
      (lt_eq_gt_cases_smaller (lambda i: nat, P i -> Prop) (succ j)
          (lambda i: nat, equal (P i) (nat_recursion P p_zero p_succ i))
          (equal (P (succ j)) (p_succ j (nat_recursion P p_zero p_succ j)))
          (lambda i: nat, lambda p: P i, True)
          (succ k)
          (lt_add_succ k j H3))
      (H1 (succ k) (rewrite_rev nat (lt (succ k)) i (succ j) H2 (lt_add_succ k j H3))
          (nat_recursion P p_zero p_succ (succ k))
          (p_succ k p)
          (nat_recursion_is_nat_recursion P p_zero p_succ (succ k))
          (is_nat_recursion_succ P p_zero p_succ k p
              (rewrite (P k) (is_nat_recursion P p_zero p_succ k) 
                  (nat_recursion P p_zero p_succ k) p
                  (rewrite (P k -> Prop) (lambda Q: P k -> Prop, Q p)
                      (partial_nat_recursion P p_zero p_succ j k)
                      (equal (P k) (nat_recursion P p_zero p_succ k))
                      (lt_eq_gt_cases_smaller (lambda i: nat, P i -> Prop) (succ j)
                          (lambda i: nat, equal (P i) (nat_recursion P p_zero p_succ i))
                          (equal (P (succ j)) (p_succ j (nat_recursion P p_zero p_succ j)))
                          (lambda i: nat, lambda p: P i, True)
                          k
                          (lt_transitivity k j (succ j) H3 (lt_succ j)))
                      H4)
                  (nat_recursion_is_nat_recursion P p_zero p_succ k)))).

Definition partial_nat_recursion_succ_equal:
   forall P: nat -> Type,
   forall p_zero: P zero,
   forall p_succ: forall i: nat, P i -> P (succ i),
   forall j: nat,
   forall p: P j,
   partial_nat_recursion P p_zero p_succ j j p ->
   partial_nat_recursion P p_zero p_succ j (succ j) (p_succ j p)
:= lambda P: nat -> Type,
   lambda p_zero: P zero,
   lambda p_succ: forall i: nat, P i -> P (succ i),
   lambda j: nat,
   lambda p: P j,
   lambda H1: partial_nat_recursion P p_zero p_succ j j p,
   rewrite_rev (P (succ j) -> Prop) (lambda Q: P (succ j) -> Prop, Q (p_succ j p))
      (partial_nat_recursion P p_zero p_succ j (succ j))
      (equal (P (succ j)) (p_succ j (nat_recursion P p_zero p_succ j)))
      (lt_eq_gt_cases_equal (lambda i: nat, P i -> Prop) (succ j)
          (lambda i: nat, equal (P i) (nat_recursion P p_zero p_succ i))
          (equal (P (succ j)) (p_succ j (nat_recursion P p_zero p_succ j)))
          (lambda i: nat, lambda p: P i, True))
      (equal_function (P j) (P (succ j)) (p_succ j) (nat_recursion P p_zero p_succ j) p
          (rewrite (P j -> Prop) (lambda Q: P j -> Prop, Q p)
              (partial_nat_recursion P p_zero p_succ j j)
              (equal (P j) (nat_recursion P p_zero p_succ j))
              (lt_eq_gt_cases_smaller (lambda i: nat, P i -> Prop) (succ j)
                  (lambda i: nat, equal (P i) (nat_recursion P p_zero p_succ i))
                  (equal (P (succ j)) (p_succ j (nat_recursion P p_zero p_succ j)))
                  (lambda i: nat, lambda p: P i, True)
                  j
                  (lt_succ j))
              H1)).

Definition partial_nat_recursion_succ_greater:
   forall P: nat -> Type,
   forall p_zero: P zero,
   forall p_succ: forall i: nat, P i -> P (succ i),
   forall j: nat,
   forall k: nat,
   lt j k ->
   forall p: P k,
   partial_nat_recursion P p_zero p_succ j k p ->
   partial_nat_recursion P p_zero p_succ j (succ k) (p_succ k p)
:= lambda P: nat -> Type,
   lambda p_zero: P zero,
   lambda p_succ: forall i: nat, P i -> P (succ i),
   lambda j: nat,
   lambda k: nat,
   lambda H1: lt j k,
   lambda p: P k,
   lambda H2: partial_nat_recursion P p_zero p_succ j k p,
   rewrite_rev (P (succ k) -> Prop) (lambda Q: P (succ k) -> Prop, Q (p_succ k p))
      (partial_nat_recursion P p_zero p_succ j (succ k))
      (lambda p: P (succ k), True)
      (lt_eq_gt_cases_greater (lambda i: nat, P i -> Prop) (succ j)
          (lambda i: nat, equal (P i) (nat_recursion P p_zero p_succ i))
          (equal (P (succ j)) (p_succ j (nat_recursion P p_zero p_succ j)))
          (lambda i: nat, lambda p: P i, True)
          (succ k)
          (lt_add_succ j k H1))
      (lambda P: Prop, lambda p: P, p).

Definition partial_nat_recursion_succ:
   forall P: nat -> Type,
   forall p_zero: P zero,
   forall p_succ: forall i: nat, P i -> P (succ i),
   forall i: nat,
   (forall j: nat, lt j i -> nat_recursion_unique_prop P p_zero p_succ j) ->
   forall j: nat,
   equal nat i (succ j) ->
   forall k: nat,
   forall p: P k,
   partial_nat_recursion P p_zero p_succ j k p ->
   partial_nat_recursion P p_zero p_succ j (succ k) (p_succ k p)
:= lambda P: nat -> Type,
   lambda p_zero: P zero,
   lambda p_succ: forall i: nat, P i -> P (succ i),
   lambda i: nat,
   lambda H1: forall j: nat, lt j i -> nat_recursion_unique_prop P p_zero p_succ j,
   lambda j: nat,
   lambda H3: equal nat i (succ j),
   lt_eq_gt_induction j
      (lambda k: nat,
       forall p: P k,
       partial_nat_recursion P p_zero p_succ j k p ->
       partial_nat_recursion P p_zero p_succ j (succ k) (p_succ k p))
      (partial_nat_recursion_succ_smaller P p_zero p_succ i H1 j H3)
      (partial_nat_recursion_succ_equal P p_zero p_succ j)
      (partial_nat_recursion_succ_greater P p_zero p_succ j).

Definition partial_nat_recursion_satisfies_recursion:
   forall P: nat -> Type,
   forall p_zero: P zero,
   forall p_succ: forall i: nat, P i -> P (succ i),
   forall i: nat,
   (forall j: nat, lt j i -> nat_recursion_unique_prop P p_zero p_succ j) ->
   forall j: nat,
   equal nat i (succ j) ->
   satisfies_nat_recursion P p_zero p_succ (partial_nat_recursion P p_zero p_succ j)
:= lambda P: nat -> Type,
   lambda p_zero: P zero,
   lambda p_succ: forall i: nat, P i -> P (succ i),
   lambda i: nat,
   lambda H1: forall j: nat, lt j i -> nat_recursion_unique_prop P p_zero p_succ j,
   lambda j: nat,
   lambda H3: equal nat i (succ j),
   construct_and (partial_nat_recursion P p_zero p_succ j zero p_zero)
      (forall i: nat, 
       forall p: P i, 
       partial_nat_recursion P p_zero p_succ j i p -> 
       partial_nat_recursion P p_zero p_succ j (succ i) (p_succ i p))
      (partial_nat_recursion_zero P p_zero p_succ i H1 j H3)
      (partial_nat_recursion_succ P p_zero p_succ i H1 j H3).

Definition nat_recurions_succ_is_p_succ:
   forall P: nat -> Type,
   forall p_zero: P zero,
   forall p_succ: forall i: nat, P i -> P (succ i),
   forall i: nat,
   (forall j: nat, lt j i -> nat_recursion_unique_prop P p_zero p_succ j) ->
   forall j: nat,
   equal nat i (succ j) ->
   forall p: P (succ j),
   is_nat_recursion P p_zero p_succ (succ j) p ->
   equal (P (succ j)) (p_succ j (nat_recursion P p_zero p_succ j)) p
:= lambda P: nat -> Type,
   lambda p_zero: P zero,
   lambda p_succ: forall i: nat, P i -> P (succ i),
   lambda i: nat,
   lambda H1: forall j: nat, lt j i -> nat_recursion_unique_prop P p_zero p_succ j,
   lambda j: nat,
   lambda H2: equal nat i (succ j),
   lambda p: P (succ j),
   lambda H3: is_nat_recursion P p_zero p_succ (succ j) p,
   rewrite (P (succ j) -> Prop) (lambda Q: P (succ j) -> Prop, Q p)
      (partial_nat_recursion P p_zero p_succ j (succ j))
      (equal (P (succ j)) (p_succ j (nat_recursion P p_zero p_succ j)))
      (lt_eq_gt_cases_equal (lambda i: nat, P i -> Prop) (succ j)
          (lambda i: nat, equal (P i) (nat_recursion P p_zero p_succ i))
          (equal (P (succ j)) (p_succ j (nat_recursion P p_zero p_succ j)))
          (lambda i: nat, lambda p: P i, True))
      (H3 (partial_nat_recursion P p_zero p_succ j)
          (partial_nat_recursion_satisfies_recursion P p_zero p_succ i H1 j H2)).

Definition nat_recursion_unique_is_successor:
   forall P: nat -> Type,
   forall p_zero: P zero,
   forall p_succ: forall i: nat, P i -> P (succ i),
   forall i: nat,
   (forall j: nat, lt j i -> nat_recursion_unique_prop P p_zero p_succ j) ->
   forall j: nat,
   equal nat i (succ j) ->
   nat_recursion_unique_prop P p_zero p_succ i
:= lambda P: nat -> Type,
   lambda p_zero: P zero,
   lambda p_succ: forall i: nat, P i -> P (succ i),
   lambda i: nat,
   lambda H1: forall j: nat, lt j i -> nat_recursion_unique_prop P p_zero p_succ j,
   lambda j: nat,
   lambda H2: equal nat i (succ j),
   rewrite_rev nat (nat_recursion_unique_prop P p_zero p_succ) i (succ j) H2
      (lambda p1: P (succ j),
       lambda p2: P (succ j),
       lambda H3: is_nat_recursion P p_zero p_succ (succ j) p1,
       lambda H4: is_nat_recursion P p_zero p_succ (succ j) p2,
       equal_transitivity (P (succ j)) p1 (p_succ j (nat_recursion P p_zero p_succ j)) p2
          (equal_symmetry (P (succ j)) (p_succ j (nat_recursion P p_zero p_succ j)) p1
              (nat_recurions_succ_is_p_succ P p_zero p_succ i H1 j H2 p1 H3))
          (nat_recurions_succ_is_p_succ P p_zero p_succ i H1 j H2 p2 H4)).

Definition is_nat_recursion_unique:
   forall P: nat -> Type,
   forall p_zero: P zero,
   forall p_succ: forall i: nat, P i -> P (succ i),
   forall i: nat,
   forall p1: P i,
   forall p2: P i,
   is_nat_recursion P p_zero p_succ i p1 ->
   is_nat_recursion P p_zero p_succ i p2 ->
   equal (P i) p1 p2
:= lambda P: nat -> Type,
   lambda p_zero: P zero,
   lambda p_succ: forall i: nat, P i -> P (succ i),
   nat_induction_2nd (nat_recursion_unique_prop P p_zero p_succ)
      (lambda i: nat,
       lambda H1: forall j: nat, lt j i -> nat_recursion_unique_prop P p_zero p_succ j,
       or_induction (equal nat i zero) (exists nat (lambda j: nat, equal nat i (succ j)))
          (nat_recursion_unique_prop P p_zero p_succ i)
          (nat_destruct i)
          (nat_recursion_zero_unique P p_zero p_succ i)
          (lambda H2: exists nat (lambda j: nat, equal nat i (succ j)),
           nat_recursion_unique_is_successor P p_zero p_succ i H1
              (epsilon nat (lambda j: nat, equal nat i (succ j)) H2)
              (epsilon_property nat (lambda j: nat, equal nat i (succ j)) H2))).

Definition nat_recursion_zero:
   forall P: nat -> Type,
   forall p_zero: P zero,
   forall p_succ: forall i: nat, P i -> P (succ i),
   equal (P zero) (nat_recursion P p_zero p_succ zero) p_zero
:= lambda P: nat -> Type,
   lambda p_zero: P zero,
   lambda p_succ: forall i: nat, P i -> P (succ i),
   is_nat_recursion_unique P p_zero p_succ zero (nat_recursion P p_zero p_succ zero) p_zero
      (nat_recursion_is_nat_recursion P p_zero p_succ zero)
      (is_nat_recursion_zero P p_zero p_succ).

Definition nat_recursion_succ:
   forall P: nat -> Type,
   forall p_zero: P zero,
   forall p_succ: forall i: nat, P i -> P (succ i),
   forall i: nat,
   equal (P (succ i)) (nat_recursion P p_zero p_succ (succ i))
      (p_succ i (nat_recursion P p_zero p_succ i))
:= lambda P: nat -> Type,
   lambda p_zero: P zero,
   lambda p_succ: forall i: nat, P i -> P (succ i),
   lambda i: nat,
   is_nat_recursion_unique P p_zero p_succ (succ i) (nat_recursion P p_zero p_succ (succ i))
      (p_succ i (nat_recursion P p_zero p_succ i))
      (nat_recursion_is_nat_recursion P p_zero p_succ (succ i))
      (is_nat_recursion_succ P p_zero p_succ i (nat_recursion P p_zero p_succ i)
          (nat_recursion_is_nat_recursion P p_zero p_succ i)).

