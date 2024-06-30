Require logic.
Require equal.
Require nat.
Require le.
Require nat_recursion.
Require plus.

Definition mult: nat -> nat -> nat
:= lambda n: nat,
   nat_recursion (lambda i: nat, nat) zero (lambda m: nat, lambda p: nat, plus n p).

Definition mult_zero_right:
   forall n: nat,
   equal nat (mult n zero) zero
:= lambda n: nat,
   nat_recursion_zero (lambda i: nat, nat) zero (lambda m: nat, lambda p: nat, plus n p).

Definition mult_succ_right:
   forall i: nat,
   forall j: nat,
   equal nat (mult i (succ j)) (plus i (mult i j))
:= lambda i: nat,
   nat_recursion_succ (lambda i: nat, nat) zero (lambda m: nat, lambda p: nat, plus i p).

Definition mult_zero_left:
   forall n: nat,
   equal nat (mult zero n) zero
:= nat_induction (lambda n: nat, equal nat (mult zero n) zero)
      (mult_zero_right zero)
      (lambda i: nat,
       lambda H: equal nat (mult zero i) zero,
       equal_transitivity nat (mult zero (succ i)) (plus zero (mult zero i))
           zero (mult_succ_right zero i)
           (equal_symmetry nat (mult zero i) zero H
               (lambda i: nat, equal nat (plus zero i) zero)
               (plus_zero_right zero))).

Definition mult_succ_left_lemma:
   forall i: nat,
   forall j: nat,
   equal nat (plus (succ i) (plus j (mult i j)))
             (plus (succ j) (plus i (mult i j)))
:= lambda i: nat,
   lambda j: nat,
   equal_transitivity nat (plus (succ i) (plus j (mult i j)))
      (plus (plus (succ i) j) (mult i j))
      (plus (succ j) (plus i (mult i j)))
      (equal_symmetry nat (plus (plus (succ i) j) (mult i j))
          (plus (succ i) (plus j (mult i j))) 
          (plus_associativity (succ i) j (mult i j)))
      (equal_transitivity nat (plus (plus (succ i) j) (mult i j))
          (plus (plus (succ j) i) (mult i j))
          (plus (succ j) (plus i (mult i j)))
          (equal_function nat nat (lambda k: nat, plus k (mult i j))
              (plus (succ i) j) (plus (succ j) i)
              (equal_transitivity nat (plus (succ i) j) (succ (plus i j))
                  (plus (succ j) i)
                  (plus_succ_left i j)
                  (equal_transitivity nat (succ (plus i j)) (succ (plus j i))
                      (plus (succ j) i)
                      (equal_function nat nat succ (plus i j) (plus j i)
                          (plus_commutative i j))
                      (equal_symmetry nat (plus (succ j) i) (succ (plus j i))
                          (plus_succ_left j i)))))
          (plus_associativity (succ j) i (mult i  j))).

Definition mult_succ_left:
   forall i: nat,
   forall j: nat,
   equal nat (mult (succ i) j) (plus j (mult i j))
:= lambda i: nat,
   nat_induction
      (lambda j: nat, equal nat (mult (succ i) j) (plus j (mult i j)))
      (equal_transitivity nat (mult (succ i) zero) zero
          (plus zero (mult i zero)) (mult_zero_right (succ i))
          (equal_symmetry nat (mult i zero) zero (mult_zero_right i)
              (lambda j: nat, equal nat zero (plus zero j))
              (equal_symmetry nat (plus zero zero) zero
                  (plus_zero_right zero))))
      (lambda j: nat,
       lambda H: equal nat (mult (succ i) j) (plus j (mult i j)),
       equal_transitivity nat (mult (succ i) (succ j))
          (plus (succ i) (mult (succ i) j)) (plus (succ j) (mult i (succ j)))
          (mult_succ_right (succ i) j)
          (equal_transitivity nat (plus (succ i) (mult (succ i) j))
              (plus (succ j) (plus i (mult i j)))
              (plus (succ j) (mult i (succ j)))
              (equal_transitivity nat (plus (succ i) (mult (succ i) j))
                  (plus (succ i) (plus j (mult i j)))
                  (plus (succ j) (plus i (mult i j)))
                  (equal_function nat nat (plus (succ i)) (mult (succ i) j)
                      (plus j (mult i j)) H)
                  (mult_succ_left_lemma i j))
              (equal_function nat nat (plus (succ j)) (plus i (mult i j))
                  (mult i (succ j))
                  (equal_symmetry nat (mult i (succ j)) (plus i (mult i j))
                      (mult_succ_right i j))))).

Definition mult_commutative_zero:
   forall i: nat,
   equal nat (mult i zero) (mult zero i)
:= lambda i: nat,
   equal_transitivity nat (mult i zero) zero (mult zero i) (mult_zero_right i)
      (equal_symmetry nat (mult zero i) zero (mult_zero_left i)).

Definition mult_commutative_succ:
   forall n: nat,
   forall m: nat,
   equal nat (mult n m) (mult m n) ->
   equal nat (mult n (succ m)) (mult (succ m) n)
:= lambda n: nat,
   lambda m: nat,
   lambda H: equal nat (mult n m) (mult m n),
   equal_transitivity nat (mult n (succ m)) (plus n (mult n m))
      (mult (succ m) n) (mult_succ_right n m)
      (equal_transitivity nat (plus n (mult n m)) (plus n (mult m n))
          (mult (succ m) n)
          (equal_function nat nat (plus n) (mult n m) (mult m n) H)
          (equal_symmetry nat (mult (succ m) n) (plus n (mult m n))
              (mult_succ_left m n))).

Definition mult_commutative:
   forall n: nat,
   forall m: nat,
   equal nat (mult n m) (mult m n)
:= lambda n: nat,
   nat_induction (lambda m: nat, equal nat (mult n m) (mult m n))
      (mult_commutative_zero n) (mult_commutative_succ n).

Definition le_mult_right_succ:
   forall n: nat,
   forall m: nat,
   le n (mult n (succ m))
:= lambda n: nat,
   lambda m: nat,
   equal_symmetry nat (mult n (succ m)) (plus n (mult n m))
      (mult_succ_right n m) (le n) (le_plus_right n (mult n m)).

Definition le_mult_right:
   forall n: nat,
   forall m: nat,
   not (equal nat m zero) ->
   le n (mult n m)
:= lambda n: nat,
   nat_induction (lambda m: nat, not (equal nat m zero) -> le n (mult n m))
      (lambda H: not (equal nat zero zero), 
       H (equal_reflexivity nat zero) (le n (mult n zero)))
      (lambda m: nat,
       lambda H1: not (equal nat m zero) -> le n (mult n m),
       lambda H2: not (equal nat (succ m) zero),
       le_mult_right_succ n m).

Definition le_mult_left:
   forall n: nat,
   forall m: nat,
   not (equal nat m zero) ->
   le n (mult m n)
:= lambda n: nat,
   lambda m: nat,
   lambda H: not (equal nat m zero),
   mult_commutative n m (le n) (le_mult_right n m H).

Definition mult_one_right:
   forall i: nat,
   equal nat (mult i one) i
:= lambda i: nat,
   equal_transitivity nat (mult i one) (plus i zero) i
      (equal_transitivity nat (mult i one) (plus i (mult i zero)) (plus i zero)
          (mult_succ_right i zero)
          (equal_function nat nat (plus i) (mult i zero) zero 
              (mult_zero_right i)))
      (plus_zero_right i).

