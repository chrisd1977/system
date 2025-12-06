Require logic.
Require equal.

Axiom dep_pair:
   forall S: Type,
   forall T: S -> Type,
   Type.

Axiom make_dep_pair:
   forall S: Type,
   forall T: S -> Type,
   forall s: S,
   forall t: T s,
   dep_pair S T.

Axiom dep_first:
   forall S: Type,
   forall T: S -> Type,
   dep_pair S T ->
   S.

Axiom dep_second:
   forall S: Type,
   forall T: S -> Type,
   forall p: dep_pair S T,
   T (dep_first S T p).

Axiom make_dep_pair_first:
   forall S: Type,
   forall T: S -> Type,
   forall s: S,
   forall t: T s,
   equal S (dep_first S T (make_dep_pair S T s t)) s.

Axiom make_dep_pair_second:
   forall S: Type,
   forall T: S -> Type,
   forall s: S,
   forall t: T s,
   equal (T s)
      (rewrite S T (dep_first S T (make_dep_pair S T s t)) s (make_dep_pair_first S T s t)
          (dep_second S T (make_dep_pair S T s t)))
      t.

Axiom dep_pair_unique:
   forall S: Type,
   forall T: S -> Type,
   forall p: dep_pair S T,
   equal (dep_pair S T) p (make_dep_pair S T (dep_first S T p) (dep_second S T p)).

Definition equal_dep_pair_from_rewrite_double_equal:
   forall S: Type,
   forall T: S -> Type,
   forall s1: S,
   forall s2: S,
   equal S s1 s2 ->
   forall t1: T s1,
   forall t2: T s2,
   forall H2: equal S s1 s2,
   equal (T s2) (rewrite S T s1 s2 H2 t1) t2 ->
   equal (dep_pair S T) (make_dep_pair S T s1 t1) (make_dep_pair S T s2 t2)
:= lambda S: Type,
   lambda T: S -> Type,
   lambda s1: S,
   lambda s2: S,
   lambda H1: equal S s1 s2,
   lambda t1: T s1,
   H1 (lambda s: S,
       forall t2: T s,
       forall H2: equal S s1 s,
       equal (T s) (rewrite S T s1 s H2 t1) t2 ->
       equal (dep_pair S T) (make_dep_pair S T s1 t1) (make_dep_pair S T s t2))
      (lambda t2: T s1,
       lambda H2: equal S s1 s1,
       lambda H3: equal (T s1) (rewrite S T s1 s1 H2 t1) t2,
       equal_function (T s1) (dep_pair S T) (make_dep_pair S T s1) t1 t2
          (equal_transitivity (T s1) t1 (rewrite S T s1 s1 H2 t1) t2
              (equal_symmetry (T s1) (rewrite S T s1 s1 H2 t1) t1 (rewrite_same S T s1 H2 t1))
              H3)).

Definition equal_dep_pair_from_rewrite:
   forall S: Type,
   forall T: S -> Type,
   forall s1: S,
   forall s2: S,
   forall t1: T s1,
   forall t2: T s2,
   forall H1: equal S s1 s2,
   equal (T s2) (rewrite S T s1 s2 H1 t1) t2 ->
   equal (dep_pair S T) (make_dep_pair S T s1 t1) (make_dep_pair S T s2 t2)
:= lambda S: Type,
   lambda T: S -> Type,
   lambda s1: S,
   lambda s2: S,
   lambda t1: T s1,
   lambda t2: T s2,
   lambda H1: equal S s1 s2,
   equal_dep_pair_from_rewrite_double_equal S T s1 s2 H1 t1 t2 H1.

