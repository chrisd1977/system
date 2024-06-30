Require logic.
Require equal.
Require nat.

Definition defines_pred:
   nat -> nat -> Prop
:= lambda n: nat,
   lambda p: nat,
   or (equal nat n (succ p)) (and (equal nat n zero) (equal nat p zero)).

Definition defines_pred_zero:
   defines_pred zero zero
:= or_right
      (equal nat zero (succ zero))
      (and (equal nat zero zero) (equal nat zero zero))
      (construct_and (equal nat zero zero) (equal nat zero zero)
          (equal_reflexivity nat zero) (equal_reflexivity nat zero)).

Definition defines_pred_succ:
   forall n: nat,
   defines_pred (succ n) n
:= lambda n: nat,
   or_left (equal nat (succ n) (succ n))
      (and (equal nat (succ n) zero) (equal nat n zero))
      (equal_reflexivity nat (succ n)).

Definition exists_pred:
   forall n: nat,
   exists nat (defines_pred n)
:= nat_induction (lambda p: nat, exists nat (defines_pred p))
      (construct_exists nat (defines_pred zero) zero defines_pred_zero)
      (lambda n: nat,
       lambda H: exists nat (defines_pred n),
       construct_exists nat (defines_pred (succ n)) n (defines_pred_succ n)).

Definition pred_unique_zero:
   forall p: nat,
   forall q: nat,
   forall H1: defines_pred zero p,
   forall H2: defines_pred zero q,
   equal nat p q
:= lambda p: nat,
   lambda q: nat,
   lambda H1: defines_pred zero p,
   lambda H2: defines_pred zero q,
   equal_transitivity nat p zero q
      (and_right (equal nat zero zero) (equal nat p zero)
          (H1 (zero_is_not_succ p)))
      (equal_symmetry nat q zero
          (and_right (equal nat zero zero) (equal nat q zero)
              (H2 (zero_is_not_succ q)))).

Definition defines_pred_succ_inversion:
   forall n: nat,
   forall p: nat,
   defines_pred (succ n) p ->
   equal nat (succ n) (succ p)
:= lambda n: nat,
   lambda p: nat,
   lambda H1: defines_pred (succ n) p,
   or_not_right (equal nat (succ n) (succ p))
      (and (equal nat (succ n) zero) (equal nat p zero))
      H1
      (lambda H2: and (equal nat (succ n) zero) (equal nat p zero),
       succ_is_not_zero n
          (and_left (equal nat (succ n) zero) (equal nat p zero) H2)).

Definition pred_unique:
   forall n: nat,
   forall p: nat,
   forall q: nat,
   defines_pred n p ->
   defines_pred n q ->
   equal nat p q
:= nat_induction
      (lambda n: nat,
       forall p: nat,
       forall q: nat,
       defines_pred n p ->
       defines_pred n q ->
       equal nat p q)
      pred_unique_zero
      (lambda n: nat,
       lambda H1: forall p: nat,
                  forall q: nat,
                  defines_pred n p ->
                 defines_pred n q ->
                  equal nat p q,
       lambda p: nat,
       lambda q: nat,
       lambda H1: defines_pred (succ n) p,
       lambda H2: defines_pred (succ n) q,
       equal_remove_succ p q
          (equal_transitivity nat (succ p) (succ n) (succ q)
              (equal_symmetry nat (succ n) (succ p)
                  (defines_pred_succ_inversion n p H1))
              (defines_pred_succ_inversion n q H2))).

Definition pred:
   nat -> nat
:= lambda n: nat, epsilon nat (defines_pred n) (exists_pred n).

Definition pred_properties:
   forall n: nat,
   defines_pred n (pred n)
:= lambda n: nat,
   epsilon_property nat (defines_pred n) (exists_pred n).

Definition pred_zero:
   equal nat (pred zero) zero
:= pred_unique zero (pred zero) zero (pred_properties zero) defines_pred_zero.

Definition pred_succ:
   forall n: nat,
   equal nat (pred (succ n)) n
:= lambda n: nat,
   pred_unique (succ n) (pred (succ n)) n (pred_properties (succ n))
      (defines_pred_succ n).

Definition succ_pred:
   forall i: nat, 
   not (equal nat i zero) ->
   equal nat (succ (pred i)) i
:= nat_induction (lambda i: nat, not (equal nat i zero) -> equal nat (succ (pred i)) i)
      (lambda H1: not (equal nat zero zero),
       H1 (equal_reflexivity nat zero) (equal nat (succ (pred zero)) zero))
      (lambda i: nat,
       lambda IH: not (equal nat i zero) -> equal nat (succ (pred i)) i,
       lambda H1: not (equal nat (succ i) zero),
       equal_function nat nat succ (pred (succ i)) i (pred_succ i)).

