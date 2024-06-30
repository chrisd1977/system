Require logic.
Require equal.
Require nat.
Require le.
Require lt.

Definition lt_eq_gt_induction:
   forall i: nat,
   forall P: nat -> Prop,
   (forall j: nat, lt j i -> P j) ->
   P i ->
   (forall j: nat, lt i j -> P j) ->
   forall j: nat,
   P j
:= lambda i: nat,
   lambda P: nat -> Prop,
   lambda H1: forall j: nat, lt j i -> P j,
   lambda H2: P i,
   lambda H3: forall j: nat, lt i j -> P j,
   lambda j: nat,
   or_induction (lt i j) (le j i) (P j) (lt_or_le i j)
      (lambda H4: lt i j, H3 j H4)
      (lambda H4: le j i,
       or_induction (equal nat j i) (lt j i) (P j) (destruct_le j i H4) 
          (lambda H5: equal nat j i, rewrite_rev nat P j i H5 H2)
          (H1 j)).

Definition satisfies_lt_eq_gt_cases:
   forall P: nat -> Type,
   forall i: nat,
   forall P_lt: forall i: nat, P i,
   forall P_eq: P i,
   forall P_gt: forall i: nat, P i,
   forall j: nat,
   P j ->
   Prop
:= lambda P: nat -> Type,
   lambda i: nat,
   lambda P_lt: forall i: nat, P i,
   lambda P_eq: P i,
   lambda P_gt: forall i: nat, P i,
   lambda j: nat,
   lambda p: P j,
   and (and (lt j i -> equal (P j) (P_lt j) p)
            (forall H: equal nat i j, equal (P j) (rewrite nat P i j H P_eq) p))
       (lt i j -> equal (P j) (P_gt j) p).

Definition lt_eq_gt_cases_exists_lt:
   forall P: nat -> Type,
   forall i: nat,
   forall P_lt: forall i: nat, P i,
   forall P_eq: P i,
   forall P_gt: forall i: nat, P i,
   forall j: nat,
   lt j i ->
   exists (P j) (satisfies_lt_eq_gt_cases P i P_lt P_eq P_gt j)
:= lambda P: nat -> Type,
   lambda i: nat,
   lambda P_lt: forall i: nat, P i,
   lambda P_eq: P i,
   lambda P_gt: forall i: nat, P i,
   lambda j: nat,
   lambda H1: lt j i,
   construct_exists (P j) (satisfies_lt_eq_gt_cases P i P_lt P_eq P_gt j) (P_lt j)
      (construct_and
          (and (lt j i -> equal (P j) (P_lt j) (P_lt j))
               (forall H: equal nat i j, equal (P j) (rewrite nat P i j H P_eq) (P_lt j)))
          (lt i j -> equal (P j) (P_gt j) (P_lt j))
          (construct_and (lt j i -> equal (P j) (P_lt j) (P_lt j))
              (forall H: equal nat i j, equal (P j) (rewrite nat P i j H P_eq) (P_lt j))
              (lambda H: lt j i, equal_reflexivity (P j) (P_lt j))
              (lambda H2: equal nat i j,
               lt_irreflexivity j (rewrite nat (lt j) i j H2 H1)
                  (equal (P j) (rewrite nat P i j H2 P_eq) (P_lt j))))
          (lambda H2: lt i j,
           lt_not_symmetric i j H2 H1 (equal (P j) (P_gt j) (P_lt j)))).

Definition lt_eq_gt_cases_exists_eq:
   forall P: nat -> Type,
   forall i: nat,
   forall P_lt: forall i: nat, P i,
   forall P_eq: P i,
   forall P_gt: forall i: nat, P i,
   exists (P i) (satisfies_lt_eq_gt_cases P i P_lt P_eq P_gt i)
:= lambda P: nat -> Type,
   lambda i: nat,
   lambda P_lt: forall i: nat, P i,
   lambda P_eq: P i,
   lambda P_gt: forall i: nat, P i,
   construct_exists (P i) (satisfies_lt_eq_gt_cases P i P_lt P_eq P_gt i) P_eq
      (construct_and
          (and (lt i i -> equal (P i) (P_lt i) P_eq)
               (forall H: equal nat i i, equal (P i) (rewrite nat P i i H P_eq) P_eq))
          (lt i i -> equal (P i) (P_gt i) P_eq)
          (construct_and (lt i i -> equal (P i) (P_lt i) P_eq)
              (forall H: equal nat i i, equal (P i) (rewrite nat P i i H P_eq) P_eq)
              (lambda H: lt i i, lt_irreflexivity i H (equal (P i) (P_lt i) P_eq))
              (lambda H: equal nat i i, rewrite_same nat P i H P_eq))
          (lambda H: lt i i, lt_irreflexivity i H (equal (P i) (P_gt i) P_eq))).

Definition lt_eq_gt_cases_exists_gt:
   forall P: nat -> Type,
   forall i: nat,
   forall P_lt: forall i: nat, P i,
   forall P_eq: P i,
   forall P_gt: forall i: nat, P i,
   forall j: nat,
   lt i j ->
   exists (P j) (satisfies_lt_eq_gt_cases P i P_lt P_eq P_gt j)
:= lambda P: nat -> Type,
   lambda i: nat,
   lambda P_lt: forall i: nat, P i,
   lambda P_eq: P i,
   lambda P_gt: forall i: nat, P i,
   lambda j: nat,
   lambda H1: lt i j,
   construct_exists (P j) (satisfies_lt_eq_gt_cases P i P_lt P_eq P_gt j) (P_gt j)
      (construct_and
          (and (lt j i -> equal (P j) (P_lt j) (P_gt j))
               (forall H: equal nat i j, equal (P j) (rewrite nat P i j H P_eq) (P_gt j)))
          (lt i j -> equal (P j) (P_gt j) (P_gt j))
          (construct_and (lt j i -> equal (P j) (P_lt j) (P_gt j))
              (forall H: equal nat i j, equal (P j) (rewrite nat P i j H P_eq) (P_gt j))
              (lambda H2: lt j i, lt_not_symmetric i j H1 H2 (equal (P j) (P_lt j) (P_gt j)))
              (lambda H2: equal nat i j,
               lt_irreflexivity i (rewrite_rev nat (lt i) i j H2 H1)
                  (equal (P j) (rewrite nat P i j H2 P_eq) (P_gt j))))
          (lambda H2: lt i j, equal_reflexivity (P j) (P_gt j))).

Definition lt_eq_gt_cases_exists:
   forall P: nat -> Type,
   forall i: nat,
   forall P_lt: forall i: nat, P i,
   forall P_eq: P i,
   forall P_gt: forall i: nat, P i,
   forall j: nat,
   exists (P j) (satisfies_lt_eq_gt_cases P i P_lt P_eq P_gt j)
:= lambda P: nat -> Type,
   lambda i: nat,
   lambda P_lt: forall i: nat, P i,
   lambda P_eq: P i,
   lambda P_gt: forall i: nat, P i,
   lt_eq_gt_induction i
      (lambda j: nat, exists (P j) (satisfies_lt_eq_gt_cases P i P_lt P_eq P_gt j))
      (lt_eq_gt_cases_exists_lt P i P_lt P_eq P_gt)
      (lt_eq_gt_cases_exists_eq P i P_lt P_eq P_gt)
      (lt_eq_gt_cases_exists_gt P i P_lt P_eq P_gt).

Definition lt_eq_gt_cases:
   forall P: nat -> Type,
   forall i: nat,
   (forall i: nat, P i) ->
   P i ->
   (forall i: nat, P i) ->
   forall i: nat,
   P i
:= lambda P: nat -> Type,
   lambda i: nat,
   lambda P_lt: forall i: nat, P i,
   lambda P_eq: P i,
   lambda P_gt: forall i: nat, P i,
   lambda j: nat,
   epsilon (P j) (satisfies_lt_eq_gt_cases P i P_lt P_eq P_gt j)
      (lt_eq_gt_cases_exists P i P_lt P_eq P_gt j).

Definition lt_eq_gt_cases_property:
   forall P: nat -> Type,
   forall i: nat,
   forall P_lt: forall i: nat, P i,
   forall P_eq: P i,
   forall P_gt: forall i: nat, P i,
   forall j: nat,
   satisfies_lt_eq_gt_cases P i P_lt P_eq P_gt j (lt_eq_gt_cases P i P_lt P_eq P_gt j)
:= lambda P: nat -> Type,
   lambda i: nat,
   lambda P_lt: forall i: nat, P i,
   lambda P_eq: P i,
   lambda P_gt: forall i: nat, P i,
   lambda j: nat,
   epsilon_property (P j) (satisfies_lt_eq_gt_cases P i P_lt P_eq P_gt j)
      (lt_eq_gt_cases_exists P i P_lt P_eq P_gt j).

Definition satisfies_lt_eq_gt_cases_lt:
   forall P: nat -> Type,
   forall i: nat,
   forall P_lt: forall i: nat, P i,
   forall P_eq: P i,
   forall P_gt: forall i: nat, P i,
   forall j: nat,
   lt j i ->
   forall p: P j,
   satisfies_lt_eq_gt_cases P i P_lt P_eq P_gt j p ->
   equal (P j) p (P_lt j)
:= lambda P: nat -> Type,
   lambda i: nat,
   lambda P_lt: forall i: nat, P i,
   lambda P_eq: P i,
   lambda P_gt: forall i: nat, P i,
   lambda j: nat,
   lambda H1: lt j i,
   lambda p: P j,
   lambda H2: satisfies_lt_eq_gt_cases P i P_lt P_eq P_gt j p,
   equal_symmetry (P j) (P_lt j) p
      (and_left (lt j i -> equal (P j) (P_lt j) p)
          (forall H3: equal nat i j, equal (P j) (rewrite nat P i j H3 P_eq) p)
          (and_left
              (and (lt j i -> equal (P j) (P_lt j) p)
                   (forall H3: equal nat i j, equal (P j) (rewrite nat P i j H3 P_eq) p))
              (lt i j -> equal (P j) (P_gt j) p)
              H2)
          H1).

Definition satisfies_lt_eq_gt_cases_eq:
   forall P: nat -> Type,
   forall i: nat,
   forall P_lt: forall i: nat, P i,
   forall P_eq: P i,
   forall P_gt: forall i: nat, P i,
   forall p: P i,
   satisfies_lt_eq_gt_cases P i P_lt P_eq P_gt i p ->
   equal (P i) p P_eq
:= lambda P: nat -> Type,
   lambda i: nat,
   lambda P_lt: forall i: nat, P i,
   lambda P_eq: P i,
   lambda P_gt: forall i: nat, P i,
   lambda p: P i,
   lambda H1: satisfies_lt_eq_gt_cases P i P_lt P_eq P_gt i p,
   equal_transitivity (P i) p (rewrite nat P i i (equal_reflexivity nat i) P_eq) P_eq
      (equal_symmetry (P i) (rewrite nat P i i (equal_reflexivity nat i) P_eq) p
          (and_right (lt i i -> equal (P i) (P_lt i) p)
              (forall H2: equal nat i i, equal (P i) (rewrite nat P i i H2 P_eq) p)
              (and_left
                  (and (lt i i -> equal (P i) (P_lt i) p)
                       (forall H2: equal nat i i, equal (P i) (rewrite nat P i i H2 P_eq) p))
                  (lt i i -> equal (P i) (P_gt i) p)
                  H1)
              (equal_reflexivity nat i)))
      (rewrite_same nat P i (equal_reflexivity nat i) P_eq).

Definition satisfies_lt_eq_gt_cases_gt:
   forall P: nat -> Type,
   forall i: nat,
   forall P_lt: forall i: nat, P i,
   forall P_eq: P i,
   forall P_gt: forall i: nat, P i,
   forall j: nat,
   lt i j ->
   forall p: P j,
   satisfies_lt_eq_gt_cases P i P_lt P_eq P_gt j p ->
   equal (P j) (P_gt j) p
:= lambda P: nat -> Type,
   lambda i: nat,
   lambda P_lt: forall i: nat, P i,
   lambda P_eq: P i,
   lambda P_gt: forall i: nat, P i,
   lambda j: nat,
   lambda H1: lt i j,
   lambda p: P j,
   lambda H2: satisfies_lt_eq_gt_cases P i P_lt P_eq P_gt j p,
   and_right
      (and (lt j i -> equal (P j) (P_lt j) p)
           (forall H: equal nat i j, equal (P j) (rewrite nat P i j H P_eq) p))
      (lt i j -> equal (P j) (P_gt j) p)
      H2 H1.

Definition lt_eq_gt_cases_smaller:
   forall P: nat -> Type,
   forall i: nat,
   forall P_lt: forall i: nat, P i,
   forall P_eq: P i,
   forall P_gt: forall i: nat, P i,
   forall j: nat,
   lt j i ->
   equal (P j) (lt_eq_gt_cases P i P_lt P_eq P_gt j) (P_lt j)
:= lambda P: nat -> Type,
   lambda i: nat,
   lambda P_lt: forall i: nat, P i,
   lambda P_eq: P i,
   lambda P_gt: forall i: nat, P i,
   lambda j: nat,
   lambda H1: lt j i,
   satisfies_lt_eq_gt_cases_lt P i P_lt P_eq P_gt j H1 (lt_eq_gt_cases P i P_lt P_eq P_gt j)
      (lt_eq_gt_cases_property P i P_lt P_eq P_gt j).

Definition lt_eq_gt_cases_equal:
   forall P: nat -> Type,
   forall i: nat,
   forall P_lt: forall i: nat, P i,
   forall P_eq: P i,
   forall P_gt: forall i: nat, P i,
   equal (P i) (lt_eq_gt_cases P i P_lt P_eq P_gt i) P_eq
:= lambda P: nat -> Type,
   lambda i: nat,
   lambda P_lt: forall i: nat, P i,
   lambda P_eq: P i,
   lambda P_gt: forall i: nat, P i,
   satisfies_lt_eq_gt_cases_eq P i P_lt P_eq P_gt (lt_eq_gt_cases P i P_lt P_eq P_gt i)
      (lt_eq_gt_cases_property P i P_lt P_eq P_gt i).

Definition lt_eq_gt_cases_greater:
   forall P: nat -> Type,
   forall i: nat,
   forall P_lt: forall i: nat, P i,
   forall P_eq: P i,
   forall P_gt: forall i: nat, P i,
   forall j: nat,
   lt i j ->
   equal (P j) (lt_eq_gt_cases P i P_lt P_eq P_gt j) (P_gt j)
:= lambda P: nat -> Type,
   lambda i: nat,
   lambda P_lt: forall i: nat, P i,
   lambda P_eq: P i,
   lambda P_gt: forall i: nat, P i,
   lambda j: nat,
   lambda H1: lt i j,
   equal_symmetry (P j) (P_gt j) (lt_eq_gt_cases P i P_lt P_eq P_gt j)
      (satisfies_lt_eq_gt_cases_gt P i P_lt P_eq P_gt j H1
          (lt_eq_gt_cases P i P_lt P_eq P_gt j)
          (lt_eq_gt_cases_property P i P_lt P_eq P_gt j)).

