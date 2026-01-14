Require logic.
Require equal.
Require dep_pair.
Require unit.
Require pair.
Require nat.
Require nat_recursion.

Definition listn: Type -> nat -> Type
:= lambda S: Type,
   lambda n: nat,
   nat_recursion (lambda n: nat, Type) unit (lambda i: nat, lambda T: Type, pair S T) n.

Definition listn_zero_is_unit:
   forall S: Type,
   equal Type (listn S zero) unit
:= lambda S: Type,
   nat_recursion_zero (lambda n: nat, Type) unit (lambda i: nat, lambda T: Type, pair S T).

Definition listn_succ:
   forall S: Type,
   forall i: nat, 
   equal Type (listn S (succ i)) (pair S (listn S i))
:= lambda S: Type,
   nat_recursion_succ (lambda n: nat, Type) unit (lambda i: nat, lambda T: Type, pair S T).

Definition listn_zero:
   forall S: Type,
   listn S zero
:= lambda S: Type,
   rewrite_rev Type (lambda S: Type, S) (listn S zero) unit (listn_zero_is_unit S) tt.

Definition listn_cons:
   forall S: Type,
   forall i: nat,
   S ->
   listn S i ->
   listn S (succ i)
:= lambda S: Type,
   lambda i: nat,
   lambda s: S,
   lambda l: listn S i,
   rewrite_rev Type (lambda S: Type, S) (listn S (succ i)) (pair S (listn S i))
      (listn_succ S i)
      (make_pair S (listn S i) s l).

Definition listn_head:
   forall S: Type,
   forall i: nat,
   listn S (succ i) ->
   S
:= lambda S: Type,
   lambda i: nat,
   lambda l: listn S (succ i),
   first S (listn S i)
      (rewrite Type (lambda S: Type, S) (listn S (succ i)) (pair S (listn S i))
          (listn_succ S i)
          l).

Definition listn_tail:
   forall S: Type,
   forall i: nat,
   listn S (succ i) ->
   listn S i
:= lambda S: Type,
   lambda i: nat,
   lambda l: listn S (succ i),
   second S (listn S i)
      (rewrite Type (lambda S: Type, S) (listn S (succ i)) (pair S (listn S i)) 
          (listn_succ S i)
          l).

Definition listn_zero_unique:
   forall S: Type,
   forall l: listn S zero,
   equal (listn S zero) l (listn_zero S)
:= lambda S: Type,
   lambda l: listn S zero,
   equal_symmetry Type (listn S zero) unit (listn_zero_is_unit S)
      (lambda T: Type, forall l1: T, forall l2: T, equal T l1 l2)
      unit_unique
      l
      (listn_zero S).

Definition listn_unique:
   forall S: Type,
   forall i: nat,
   forall l: listn S (succ i),
   equal (listn S (succ i)) l (listn_cons S i (listn_head S i l) (listn_tail S i l))
:= lambda S: Type,
   lambda i: nat,
   lambda l: listn S (succ i),
   pair_unique S (listn S i)
      (rewrite Type (lambda S: Type, S) (listn S (succ i)) (pair S (listn S i))
          (listn_succ S i)
          l)
      (lambda p: pair S (listn S i),
       equal (listn S (succ i)) l
          (rewrite_rev Type (lambda S: Type, S) (listn S (succ i)) (pair S (listn S i))
              (listn_succ S i)
              p))
      (equal_symmetry (listn S (succ i))
          (rewrite_rev Type (lambda S: Type, S) (listn S (succ i)) (pair S (listn S i))
              (listn_succ S i)
              (rewrite Type (lambda S: Type, S) (listn S (succ i)) (pair S (listn S i))
                  (listn_succ S i)
                  l))
          l
          (rewrite_rev_rewrite_inverse Type (lambda S: Type, S) (listn S (succ i)) 
              (pair S (listn S i))
              (listn_succ S i)
              l)).

Definition list: Type -> Type
:= lambda S: Type,
   dep_pair nat (listn S).

Definition length:
   forall S: Type,
   list S ->
   nat
:= lambda S: Type,
   lambda l: list S,
   dep_first nat (listn S) l.

Definition nil: forall S: Type, list S
:= lambda S: Type,
   make_dep_pair nat (listn S) zero (listn_zero S).

Definition cons:
   forall S: Type,
   S ->
   list S ->
   list S
:= lambda S: Type,
   lambda s: S,
   lambda l: list S,
   make_dep_pair nat (listn S) (succ (length S l))
      (listn_cons S (length S l) s (dep_second nat (listn S) l)).

Definition list_induction_listn_cons:
   forall S: Type,
   forall P: list S -> Prop,
   (forall s: S, forall l: list S, P l -> P (cons S s l)) ->
   forall i: nat,
   (forall l: listn S i, P (make_dep_pair nat (listn S) i l)) ->
   forall l: listn S (succ i),
   P (make_dep_pair nat (listn S) (succ i)
         (listn_cons S i (listn_head S i l) (listn_tail S i l)))
:= lambda S: Type,
   lambda P: list S -> Prop,
   lambda H2: forall s: S, forall l: list S, P l -> P (cons S s l),
   lambda i: nat,
   lambda H3: forall l: listn S i, P (make_dep_pair nat (listn S) i l),
   lambda l: listn S (succ i),
   dep_pair_property_reduce nat (listn S)
      (lambda s: nat,
       lambda m: listn S s,
       P (make_dep_pair nat (listn S) (succ s) (listn_cons S s (listn_head S i l) m)))
      i
      (listn_tail S i l)
      (H2 (listn_head S i l) (make_dep_pair nat (listn S) i (listn_tail S i l))
          (H3 (listn_tail S i l))).

Definition list_induction:
   forall S: Type,
   forall P: list S -> Prop,
   P (nil S) ->
   (forall s: S, forall l: list S, P l -> P (cons S s l)) ->
   forall l: list S,
   P l
:= lambda S: Type,
   lambda P: list S -> Prop,
   lambda H1: P (nil S),
   lambda H2: forall s: S, forall l: list S, P l -> P (cons S s l),
   lambda l: list S,
   rewrite_rev (list S) P l
      (make_dep_pair nat (listn S) (dep_first nat (listn S) l) (dep_second nat (listn S) l))
      (dep_pair_unique nat (listn S) l)
      (nat_induction (lambda n: nat, forall l: listn S n, P (make_dep_pair nat (listn S) n l))
          (lambda l: listn S zero,
           rewrite_rev (listn S zero)
              (lambda l: listn S zero, P (make_dep_pair nat (listn S) zero l))
              l
              (listn_zero S)
              (listn_zero_unique S l)
              H1)
          (lambda i: nat,
           lambda H3: forall l: listn S i, P (make_dep_pair nat (listn S) i l),
           lambda l: listn S (succ i),
           equal_symmetry (listn S (succ i)) l
              (listn_cons S i (listn_head S i l) (listn_tail S i l))
              (listn_unique S i l)
              (lambda l: listn S (succ i), P (make_dep_pair nat (listn S) (succ i) l))
              (list_induction_listn_cons S P H2 i H3 l))
          (dep_first nat (listn S) l)
          (dep_second nat (listn S) l)).

