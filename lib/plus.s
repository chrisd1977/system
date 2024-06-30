Require logic.
Require equal.
Require nat.
Require nat_recursion.
Require le.

Definition plus:
   nat -> nat -> nat
:= lambda i: nat,
   nat_recursion (lambda i: nat, nat) i (lambda j: nat, lambda k: nat, succ k).

Definition plus_zero_right:
   forall i: nat,
   equal nat (plus i zero) i
:= lambda i: nat,
   nat_recursion_zero (lambda i: nat, nat) i (lambda j: nat, lambda j: nat, succ j).

Definition plus_succ_right:
   forall i: nat,
   forall j: nat,
   equal nat (plus i (succ j)) (succ (plus i j))
:= lambda i: nat,
   lambda j: nat,
   nat_recursion_succ (lambda i: nat, nat) i (lambda j: nat, lambda k: nat, succ k) j.

Definition succ_is_plus_one:
   forall i: nat,
   equal nat (succ i) (plus i one)
:= lambda i: nat,
   equal_symmetry nat (plus i one) (succ i)
      (equal_transitivity nat (plus i one) (succ (plus i zero)) (succ i)
          (plus_succ_right i zero)
          (equal_function nat nat succ (plus i zero) i (plus_zero_right i))).

Definition plus_zero_recursion:
   forall i: nat,
   equal nat (plus zero i) i ->
   equal nat (plus zero (succ i)) (succ i)
:= lambda i: nat,
   lambda H: equal nat (plus zero i) i,
   equal_transitivity nat (plus zero (succ i)) (succ (plus zero i)) (succ i)
      (plus_succ_right zero i)
      (equal_function nat nat succ (plus zero i) i H).

Definition plus_zero_left:
   forall i: nat,
   equal nat (plus zero i) i
:= nat_induction (lambda i: nat, equal nat (plus zero i) i) (plus_zero_right zero)
      plus_zero_recursion.

Definition plus_succ_left_zero:
   forall i: nat,
   equal nat (plus (succ i) zero) (succ (plus i zero))
:= lambda i: nat,
   equal_transitivity nat (plus (succ i) zero) (succ i) (succ (plus i zero))
      (plus_zero_right (succ i))
      (equal_function nat nat succ i (plus i zero)
          (equal_symmetry nat (plus i zero) i (plus_zero_right i))).

Definition plus_commutative_zero:
   forall i: nat,
   equal nat (plus i zero) (plus zero i)
:= lambda i: nat,
   equal_transitivity nat (plus i zero) i (plus zero i)
      (plus_zero_right i)
      (equal_symmetry nat (plus zero i) i (plus_zero_left i)).

Definition plus_succ_left_succ:
   forall i: nat,
   forall j: nat,
   forall H1: equal nat (plus (succ i) j) (succ (plus i j)),
   equal nat (plus (succ i) (succ j)) (succ (plus i (succ j)))
:= lambda i: nat,
   lambda j: nat,
   lambda H: equal nat (plus (succ i) j) (succ (plus i j)),
   equal_transitivity nat
      (plus (succ i) (succ j))
      (succ (plus (succ i) j))
      (succ (plus i (succ j)))
      (plus_succ_right (succ i) j)
      (equal_function nat nat succ (plus (succ i) j) (plus i (succ j))
          (equal_transitivity nat
              (plus (succ i) j) (succ (plus i j)) (plus i (succ j))
              H 
              (equal_symmetry nat (plus i (succ j)) (succ (plus i j)) 
                 (plus_succ_right i j)))).

Definition plus_succ_left:
   forall i: nat,
   forall j: nat,
   equal nat (plus (succ i) j) (succ (plus i j))
:= lambda i: nat,
   nat_induction
      (lambda j: nat, equal nat (plus (succ i) j) (succ (plus i j)))
      (plus_succ_left_zero i) (plus_succ_left_succ i).

Definition plus_commutative_succ:
   forall i: nat,
   forall j: nat,
   equal nat (plus i j) (plus j i) ->
   equal nat (plus i (succ j)) (plus (succ j) i)
:= lambda i: nat,
   lambda j: nat,
   lambda H: equal nat (plus i j) (plus j i),
   equal_transitivity nat (plus i (succ j)) (succ (plus i j)) (plus (succ j) i)
      (nat_recursion_succ (lambda i: nat, nat) i 
          (lambda k: nat, lambda l: nat, succ l) j)
      (equal_transitivity nat
          (succ (plus i j))
          (succ (plus j i))
          (plus (succ j) i)
          (equal_function nat nat succ (plus i j) (plus j i) H)
          (equal_symmetry nat (plus (succ j) i) (succ (plus j i))
              (plus_succ_left j i))).

Definition plus_commutative:
   forall i: nat,
   forall j: nat,
   equal nat (plus i j) (plus j i)
:= lambda i: nat,
   nat_induction (lambda j: nat, equal nat (plus i j) (plus j i))
      (plus_commutative_zero i) (plus_commutative_succ i).

Definition le_plus_right:
   forall i: nat,
   forall j: nat,
   le i (plus i j)
:= lambda i: nat,
   nat_induction (lambda j: nat, le i (plus i j))
      (rewrite_rev nat (le i) (plus i zero) i (plus_zero_right i) (le_reflexivity i))
      (lambda j: nat,
       lambda H1: le i (plus i j),
       le_transitivity i (plus i j) (plus i (succ j)) H1
          (rewrite_rev nat (le (plus i j)) (plus i (succ j)) (succ (plus i j))
              (plus_succ_right i j) (le_succ_refl (plus i j)))).

Definition plus_associativity:
   forall i: nat,
   forall j: nat,
   forall k: nat,
   equal nat (plus (plus i j) k) (plus i (plus j k))
:= lambda i: nat,
   lambda j: nat,
   nat_induction
      (lambda k: nat, equal nat (plus (plus i j) k) (plus i (plus j k)))
      (equal_transitivity nat (plus (plus i j) zero) (plus i j)
          (plus i (plus j zero)) (plus_zero_right (plus i j))
          (equal_function nat nat (plus i) j (plus j zero)
              (equal_symmetry nat (plus j zero) j (plus_zero_right j))))
      (lambda k: nat,
       lambda H: equal nat (plus (plus i j) k) (plus i (plus j k)),
       equal_transitivity nat (plus (plus i j) (succ k))
          (succ (plus (plus i j) k)) (plus i (plus j (succ k)))
          (plus_succ_right (plus i j) k)
          (equal_transitivity nat (succ (plus (plus i j) k)) 
              (plus i (succ (plus j k))) (plus i (plus j (succ k)))
              (equal_symmetry nat (plus i (succ (plus j k))) 
                  (succ (plus (plus i j) k))
                  (equal_transitivity nat (plus i (succ (plus j k)))
                      (succ (plus i (plus j k)))
                      (succ (plus (plus i j) k)) (plus_succ_right i (plus j k))
                      (equal_function nat nat succ (plus i (plus j k))
                          (plus (plus i j) k)
                          (equal_symmetry nat (plus (plus i j) k)
                              (plus i (plus j k)) H))))
              (equal_function nat nat (plus i) (succ (plus j k))
                  (plus j (succ k))
                  (equal_symmetry nat (plus j (succ k)) (succ (plus j k))
                      (plus_succ_right j k))))).

Definition plus_cancel_left:
   forall i: nat,
   forall j: nat,
   forall k: nat,
   equal nat (plus i j) (plus i k) ->
   equal nat j k
:= lambda i: nat,
   lambda j: nat,
   lambda k: nat,
   nat_induction
      (lambda i: nat, equal nat (plus i j) (plus i k) -> equal nat j k)
      (lambda H: equal nat (plus zero j) (plus zero k),
       equal_transitivity nat j (plus zero j) k
          (equal_symmetry nat (plus zero j) j (plus_zero_left j))
          (equal_transitivity nat (plus zero j) (plus zero k) k H 
              (plus_zero_left k)))
      (lambda i: nat,
       lambda H1: equal nat (plus i j) (plus i k) -> equal nat j k,
       lambda H2: equal nat (plus (succ i) j) (plus (succ i) k),
       H1
          (equal_remove_succ (plus i j) (plus i k)
              (equal_transitivity nat (succ (plus i j)) (plus (succ i) j)
                  (succ (plus i k))
                  (equal_symmetry nat (plus (succ i) j) (succ (plus i j))
                      (plus_succ_left i j))
                  (equal_transitivity nat (plus (succ i) j) (plus (succ i) k)
                      (succ (plus i k)) H2 (plus_succ_left i k)))))
      i.

