Require logic.
Require equal.
Require dep_pair.

Definition pair:
   forall S: Type,
   forall T: Type,
   Type
:= lambda S: Type,
   lambda T: Type,
   dep_pair S (lambda s: S, T).

Definition make_pair:
   forall S: Type,
   forall T: Type,
   forall s: S,
   forall t: T,
   pair S T
:= lambda S: Type,
   lambda T: Type,
   make_dep_pair S (lambda s: S, T).

Definition first:
   forall S: Type,
   forall T: Type,
   pair S T ->
   S
:= lambda S: Type,
   lambda T: Type,
   dep_first S (lambda s: S, T).

Definition second:
   forall S: Type,
   forall T: Type,
   forall p: pair S T,
   T
:= lambda S: Type,
   lambda T: Type,
   dep_second S (lambda s: S, T).

Definition make_pair_first:
   forall S: Type,
   forall T: Type,
   forall s: S,
   forall t: T,
   equal S (first S T (make_pair S T s t)) s
:= lambda S: Type,
   lambda T: Type,
   make_dep_pair_first S (lambda s: S, T).

Definition make_pair_second_any_first_equality:
   forall S: Type,
   forall T: Type,
   forall s: S,
   forall t: T,
   forall H1: equal S (first S T (make_pair S T s t)) s,
   equal T
      (rewrite S (lambda s: S, T) (first S T (make_pair S T s t)) s H1
          (second S T (make_pair S T s t)))
      t
:= lambda S: Type,
   lambda T: Type,
   lambda s: S,
   lambda t: T,
   lambda H1: equal S (first S T (make_pair S T s t)) s,
   proof_irrelevance (equal S (first S T (make_pair S T s t)) s) (make_pair_first S T s t)
      H1
      (lambda H2: equal S (first S T (make_pair S T s t)) s,
       equal T
          (rewrite S (lambda s: S, T) (first S T (make_pair S T s t)) s H2
              (second S T (make_pair S T s t)))
          t)
      (make_dep_pair_second S (lambda s: S, T) s t).

Definition make_pair_second:
   forall S: Type,
   forall T: Type,
   forall s: S,
   forall t: T,
   equal T (second S T (make_pair S T s t)) t
:= lambda S: Type,
   lambda T: Type,
   lambda s: S,
   lambda t: T,
   equal_transitivity T (second S T (make_pair S T s t))
      (rewrite S (lambda s: S, T) s s (equal_reflexivity S s)
          (second S T (make_pair S T s t)))
      t
      (equal_symmetry T
          (rewrite S (lambda s: S, T) s s (equal_reflexivity S s)
              (second S T (make_pair S T s t)))
          (second S T (make_pair S T s t))
          (rewrite_same S (lambda s: S, T) s (equal_reflexivity S s) 
              (second S T (make_pair S T s t))))
      (make_pair_first S T s t
          (lambda s2: S,
           forall H1: equal S s2 s,
           equal T (rewrite S (lambda s: S, T) s2 s H1 (second S T (make_pair S T s t))) t)
          (make_pair_second_any_first_equality S T s t)
          (equal_reflexivity S s)).

Definition pair_unique:
   forall S: Type,
   forall T: Type,
   forall p: pair S T,
   equal (pair S T) p (make_pair S T (first S T p) (second S T p))
:= lambda S: Type,
   lambda T: Type,
   dep_pair_unique S (lambda s: S, T).

