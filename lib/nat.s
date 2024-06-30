Require logic.
Require equal.
Require function.
Require pair.

Axiom ind: Type.

Axiom ind_infinite:
   exists (ind -> ind) (infinite_function ind).

Definition proto_succ: ind -> ind
:= epsilon (ind -> ind) (infinite_function ind) ind_infinite.

Definition proto_succ_injective: injective ind ind proto_succ
:= and_left (injective ind ind proto_succ)
      (not (surjective ind ind proto_succ))
      (epsilon_property (ind -> ind) (infinite_function ind) ind_infinite).

Definition proto_succ_not_surjective: not (surjective ind ind proto_succ)
:= and_right (injective ind ind proto_succ)
      (not (surjective ind ind proto_succ))
      (epsilon_property (ind -> ind) (infinite_function ind) ind_infinite).

Definition proto_zero_exists:
    exists ind
       (lambda n: ind,
        not (exists ind (lambda m: ind, equal ind (proto_succ m) n)))
:= lambda P: forall n: ind,
             not
                (not (exists ind (lambda m: ind, equal ind (proto_succ m) n))),
   proto_succ_not_surjective
      (lambda n: ind,
       double_not (exists ind (lambda m: ind, equal ind (proto_succ m) n))
          (P n)).

Definition proto_zero: ind
:= epsilon ind
      (lambda n: ind,
       not (exists ind (lambda m: ind, equal ind (proto_succ m) n)))
      proto_zero_exists.

Definition contains_nat: (ind -> Prop) -> Prop
:= lambda P: ind -> Prop,
   and (P proto_zero) (forall n: ind, P n -> P (proto_succ n)).

Definition is_nat: ind -> Prop
:= lambda n: ind,
   forall P: ind -> Prop,
   contains_nat P ->
   P n.

Definition zero_is_nat: is_nat proto_zero
:= lambda P: ind -> Prop,
   lambda H: and (P proto_zero) (forall n: ind, P n -> P (proto_succ n)),
   and_left (P proto_zero) (forall n: ind, P n -> P (proto_succ n)) H.

Definition succ_is_nat:
   forall n: ind,
   is_nat n ->
   is_nat (proto_succ n)
:= lambda n: ind,
   lambda H1: is_nat n,
   lambda P: ind -> Prop,
   lambda H2: contains_nat P,
   and_right (P proto_zero) (forall n: ind, P n -> P (proto_succ n))
      H2 n (H1 P H2).

Definition nat: Type
:= pair ind is_nat.

Definition zero: nat
:= make_pair ind is_nat proto_zero zero_is_nat.

Definition succ: nat -> nat
:= lambda n: nat,
   make_pair ind is_nat (proto_succ (first ind is_nat n))
      (succ_is_nat (first ind is_nat n) (second ind is_nat n)).

Definition one: nat := succ zero.
Definition two: nat := succ one.

Definition succ_is_not_zero:
   forall n: nat,
   not (equal nat (succ n) zero)
:= lambda n: nat,
   lambda H1: equal nat (succ n) zero,
   epsilon_property ind
      (lambda i: ind,
       not (exists ind (lambda j: ind, equal ind (proto_succ j) i)))
      proto_zero_exists
      (construct_exists ind (lambda j: ind, equal ind (proto_succ j) proto_zero)
          (first ind is_nat n)
          (equal_transitivity ind (proto_succ (first ind is_nat n))
              (first ind is_nat (succ n))
              proto_zero
              (equal_symmetry ind
                  (first ind is_nat
                      (make_pair ind is_nat (proto_succ (first ind is_nat n))
                          (succ_is_nat (first ind is_nat n) (second ind is_nat n))))
                  (proto_succ (first ind is_nat n))
                  (make_pair_first ind is_nat (proto_succ (first ind is_nat n))
                      (succ_is_nat (first ind is_nat n) (second ind is_nat n))))
              (equal_transitivity ind (first ind is_nat (succ n)) (first ind is_nat zero) 
                  proto_zero
                  (equal_function nat ind (first ind is_nat) (succ n) zero H1)
                  (make_pair_first ind is_nat proto_zero zero_is_nat)))).

Definition zero_is_not_succ:
   forall n: nat,
   not (equal nat zero (succ n))
:= lambda n: nat,
   lambda H: equal nat zero (succ n),
   succ_is_not_zero n (equal_symmetry nat zero (succ n) H).

Definition equal_ind_to_equal_nat:
   forall i: nat,
   forall j: nat,
   equal ind (first ind is_nat i) (first ind is_nat j) ->
   equal nat (make_pair ind is_nat (first ind is_nat i) (second ind is_nat i))
      (make_pair ind is_nat (first ind is_nat j) (second ind is_nat j))
:= lambda i: nat,
   lambda j: nat,
   lambda H2: equal ind (first ind is_nat i) (first ind is_nat j),
   rewrite ind
      (lambda k: ind,
       forall H2: is_nat k,
       equal nat (make_pair ind is_nat (first ind is_nat i) (second ind is_nat i))
          (make_pair ind is_nat k H2))
      (first ind is_nat i)
      (first ind is_nat j)
      H2
      (lambda H2: is_nat (first ind is_nat i),
       equal_function (is_nat (first ind is_nat i)) nat
          (make_pair ind is_nat (first ind is_nat i))
          (second ind is_nat i)
          H2
          (proof_irrelevance (is_nat (first ind is_nat i)) (second ind is_nat i) H2))
      (second ind is_nat j).

Definition equal_succ_to_equal_proto_succ:
   forall i: nat,
   forall j: nat,
   equal nat (succ i) (succ j) ->
   equal ind (proto_succ (first ind is_nat i)) (proto_succ (first ind is_nat j))
:= lambda i: nat,
   lambda j: nat,
   lambda H1: equal nat (succ i) (succ j),
   equal_transitivity ind (proto_succ (first ind is_nat i))
      (first ind is_nat
          (make_pair ind is_nat (proto_succ (first ind is_nat i))
              (succ_is_nat (first ind is_nat i) (second ind is_nat i))))
      (proto_succ (first ind is_nat j))
      (equal_symmetry ind
          (first ind is_nat
              (make_pair ind is_nat (proto_succ (first ind is_nat i))
                  (succ_is_nat (first ind is_nat i) (second ind is_nat i))))
          (proto_succ (first ind is_nat i))
          (make_pair_first ind is_nat (proto_succ (first ind is_nat i))
              (succ_is_nat (first ind is_nat i) (second ind is_nat i))))
      (equal_transitivity ind
          (first ind is_nat
              (make_pair ind is_nat (proto_succ (first ind is_nat i))
                  (succ_is_nat (first ind is_nat i) (second ind is_nat i))))
          (first ind is_nat
              (make_pair ind is_nat (proto_succ (first ind is_nat j))
                  (succ_is_nat (first ind is_nat j) (second ind is_nat j))))
          (proto_succ (first ind is_nat j))
          (equal_function nat ind (first ind is_nat) (succ i) (succ j) H1)
          (make_pair_first ind is_nat (proto_succ (first ind is_nat j))
              (succ_is_nat (first ind is_nat j) (second ind is_nat j)))).

Definition equal_remove_succ:
   forall i: nat,
   forall j: nat,
   equal nat (succ i) (succ j) ->
   equal nat i j
:= lambda i: nat,
   lambda j: nat,
   lambda H1: equal nat (succ i) (succ j),
   equal_transitivity nat i (make_pair ind is_nat (first ind is_nat i) (second ind is_nat i))
      j
      (pair_unique ind is_nat i)
      (equal_transitivity nat
          (make_pair ind is_nat (first ind is_nat i) (second ind is_nat i))
          (make_pair ind is_nat (first ind is_nat j) (second ind is_nat j))
          j
          (equal_ind_to_equal_nat i j
              (proto_succ_injective (first ind is_nat i) (first ind is_nat j)
                  (equal_succ_to_equal_proto_succ i j H1)))
          (equal_symmetry nat j
              (make_pair ind is_nat (first ind is_nat j) (second ind is_nat j))
              (pair_unique ind is_nat j))).

Definition nat_prop_succ_proof_irrelevant:
   forall P: nat -> Prop,
   (forall i: nat, P i -> P (succ i)) ->
   forall i: ind,
   forall H3: is_nat i,
   P (make_pair ind is_nat i H3) ->
   forall H6: is_nat (proto_succ (first ind is_nat (make_pair ind is_nat i H3))),
   P (make_pair ind is_nat (proto_succ (first ind is_nat (make_pair ind is_nat i H3))) H6)
:= lambda P: nat -> Prop,
   lambda H2: forall i: nat, P i -> P (succ i),
   lambda i: ind,
   lambda H3: is_nat i,
   lambda H5: P (make_pair ind is_nat i H3),
   lambda H6: is_nat (proto_succ (first ind is_nat (make_pair ind is_nat i H3))),
   rewrite (is_nat (proto_succ (first ind is_nat (make_pair ind is_nat i H3))))
      (lambda H: is_nat (proto_succ (first ind is_nat (make_pair ind is_nat i H3))),
       P (make_pair ind is_nat (proto_succ (first ind is_nat (make_pair ind is_nat i H3)))
             H))
      (succ_is_nat (first ind is_nat (make_pair ind is_nat i H3))
          (second ind is_nat (make_pair ind is_nat i H3)))
      H6
      (proof_irrelevance (is_nat (proto_succ (first ind is_nat (make_pair ind is_nat i H3)))) 
          (succ_is_nat (first ind is_nat (make_pair ind is_nat i H3))
              (second ind is_nat (make_pair ind is_nat i H3)))
          H6)
      (H2 (make_pair ind is_nat i H3) H5).

Definition induction_step_ind:
   forall P: nat -> Prop,
   (forall i: nat, P i -> P (succ i)) ->
   forall i: ind,
   forall H3: is_nat i,
   forall H4: is_nat (proto_succ i),
   P (make_pair ind is_nat i H3) ->
   P (make_pair ind is_nat (proto_succ i) H4)
:= lambda P: nat -> Prop,
   lambda H2: forall i: nat, P i -> P (succ i),
   lambda i: ind,
   lambda H3: is_nat i,
   lambda H4: is_nat (proto_succ i),
   lambda H5: P (make_pair ind is_nat i H3),
   rewrite ind
      (lambda i: ind,
       forall H6: is_nat (proto_succ i), P (make_pair ind is_nat (proto_succ i) H6))
      (first ind is_nat (make_pair ind is_nat i H3))
      i
      (make_pair_first ind is_nat i H3)
      (nat_prop_succ_proof_irrelevant P H2 i H3 H5)
      H4.

Definition nat_prop_to_ind_prop:
   forall P: nat -> Prop,
   ind ->
   Prop
:= lambda P: nat -> Prop,
   lambda i: ind,
   and (is_nat i) (forall H: is_nat i, P (make_pair ind is_nat i H)).

Definition property_proto_zero:
   forall P: nat -> Prop,
   P zero ->
   nat_prop_to_ind_prop P proto_zero
:= lambda P: nat -> Prop,
   lambda H1: P zero,
   construct_and (is_nat proto_zero)
      (forall H: is_nat proto_zero, P (make_pair ind is_nat proto_zero H))
      zero_is_nat
      (lambda H3: is_nat proto_zero,
       rewrite (is_nat proto_zero)
          (lambda H3: is_nat proto_zero, P (make_pair ind is_nat proto_zero H3))
          zero_is_nat 
          H3
          (proof_irrelevance (is_nat proto_zero) zero_is_nat H3)
          H1).

Definition property_proto_succ:
   forall P: nat -> Prop,
   (forall i: nat, P i -> P (succ i)) ->
   forall i: ind,
   nat_prop_to_ind_prop P i ->
   nat_prop_to_ind_prop P (proto_succ i)
:= lambda P: nat -> Prop,
   lambda H2: forall i: nat, P i -> P (succ i),
   lambda i: ind,
   lambda H3: nat_prop_to_ind_prop P i,
   construct_and (is_nat (proto_succ i))
      (forall H: is_nat (proto_succ i), P (make_pair ind is_nat (proto_succ i) H))
      (succ_is_nat i
          (and_left (is_nat i) (forall H: is_nat i, P (make_pair ind is_nat i H)) H3))
      (lambda H4: is_nat (proto_succ i),
       induction_step_ind P H2 i
          (and_left (is_nat i) (forall H: is_nat i, P (make_pair ind is_nat i H)) H3)
          H4
          (and_right (is_nat i) (forall H: is_nat i, P (make_pair ind is_nat i H)) H3
              (and_left (is_nat i) (forall H: is_nat i, P (make_pair ind is_nat i H)) H3))).

Definition contains_nat_ind_prop:
   forall P: nat -> Prop,
   P zero ->
   (forall i: nat, P i -> P (succ i)) ->
   contains_nat (nat_prop_to_ind_prop P)
:= lambda P: nat -> Prop,
   lambda H1: P zero,
   lambda H2: forall i: nat, P i -> P (succ i),
   construct_and (nat_prop_to_ind_prop P proto_zero)
      (forall n: ind, nat_prop_to_ind_prop P n -> nat_prop_to_ind_prop P (proto_succ n))
      (property_proto_zero P H1)
      (property_proto_succ P H2).

Definition is_nat_contains_nat:
   forall P: nat -> Prop,
   P zero ->
   (forall i: nat, P i -> P (succ i)) ->
   forall i: ind,
   is_nat i->
   nat_prop_to_ind_prop P i
:= lambda P: nat -> Prop,
   lambda H1: P zero,
   lambda H2: forall i: nat, P i -> P (succ i),
   lambda i: ind,
   lambda H3: is_nat i,
   H3 (nat_prop_to_ind_prop P) (contains_nat_ind_prop P H1 H2).

Definition nat_induction:
   forall P: nat -> Prop,
   P zero ->
   (forall i: nat, P i -> P (succ i)) ->
   forall i: nat,
   P i
:= lambda P: nat -> Prop,
   lambda H1: P zero,
   lambda H2: forall i: nat, P i -> P (succ i),
   lambda i: nat,
   rewrite nat P (make_pair ind is_nat (first ind is_nat i) (second ind is_nat i)) i
      (equal_symmetry nat i (make_pair ind is_nat (first ind is_nat i) (second ind is_nat i))
          (pair_unique ind is_nat i))
      (and_right (is_nat (first ind is_nat i)) 
          (forall H: is_nat (first ind is_nat i),
           P (make_pair ind is_nat (first ind is_nat i) H))
          (is_nat_contains_nat P H1 H2 (first ind is_nat i) (second ind is_nat i))
          (second ind is_nat i)).

Definition nat_destruct:
   forall i: nat,
   or (equal nat i zero) (exists nat (lambda j: nat, equal nat i (succ j)))
:= nat_induction
      (lambda i: nat,
       or (equal nat i zero) (exists nat (lambda j: nat, equal nat i (succ j))))
      (or_left (equal nat zero zero) (exists nat (lambda j: nat, equal nat zero (succ j)))
          (equal_reflexivity nat zero))
      (lambda n: nat,
       lambda H1: or (equal nat n zero) (exists nat (lambda j: nat, equal nat n (succ j))),
       or_right (equal nat (succ n) zero)
          (exists nat (lambda j: nat, equal nat (succ n) (succ j)))
          (construct_exists nat (lambda j: nat, equal nat (succ n) (succ j)) n
              (equal_reflexivity nat (succ n)))).

