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
   equal (T (dep_first S T (make_dep_pair S T s t)))
      (dep_second S T (make_dep_pair S T s t))
      (rewrite_rev S T (dep_first S T (make_dep_pair S T s t)) s (make_dep_pair_first S T s t)
          t).

Definition make_dep_pair_second_rev:
   forall S: Type,
   forall T: S -> Type,
   forall s: S,
   forall t: T s,
   equal (T s)
      (rewrite S T (dep_first S T (make_dep_pair S T s t)) s (make_dep_pair_first S T s t)
          (dep_second S T (make_dep_pair S T s t)))
      t
:= lambda S: Type,
   lambda T: S -> Type,
   lambda s: S,
   lambda t: T s,
   equal_transitivity (T s)
      (rewrite S T (dep_first S T (make_dep_pair S T s t)) s (make_dep_pair_first S T s t)
          (dep_second S T (make_dep_pair S T s t)))
      (rewrite S T (dep_first S T (make_dep_pair S T s t)) s (make_dep_pair_first S T s t)
          (rewrite_rev S T (dep_first S T (make_dep_pair S T s t)) s
              (make_dep_pair_first S T s t)
              t))
      t
      (equal_function (T (dep_first S T (make_dep_pair S T s t))) (T s)
          (rewrite S T (dep_first S T (make_dep_pair S T s t)) s
              (make_dep_pair_first S T s t))
          (dep_second S T (make_dep_pair S T s t))
          (rewrite_rev S T (dep_first S T (make_dep_pair S T s t)) s
              (make_dep_pair_first S T s t)
              t)
          (make_dep_pair_second S T s t))
      (rewrite_rewrite_rev_inverse S T (dep_first S T (make_dep_pair S T s t)) s
          (make_dep_pair_first S T s t)
          t).

Axiom dep_pair_unique:
   forall S: Type,
   forall T: S -> Type,
   forall p: dep_pair S T,
   equal (dep_pair S T) p (make_dep_pair S T (dep_first S T p) (dep_second S T p)).

Definition dep_pair_property_reduce:
   forall S: Type,
   forall T: S -> Type,
   forall P: forall s: S, T s -> Prop,
   forall s: S,
   forall t: T s,
   P (dep_first S T (make_dep_pair S T s t)) (dep_second S T (make_dep_pair S T s t)) ->
   P s t
:= lambda S: Type,
   lambda T: S -> Type,
   lambda P: forall s: S, T s -> Prop,
   lambda s: S,
   lambda t: T s,
   lambda H1: P (dep_first S T (make_dep_pair S T s t))
                (dep_second S T (make_dep_pair S T s t)),
   rewrite_same S T s (equal_symmetry S s s (equal_reflexivity S s)) t
      (P s)
      (make_dep_pair_first S T s t
          (lambda s2: S, forall H2: equal S s2 s, P s2 (rewrite_rev S T s2 s H2 t))
          (lambda H2: equal S (dep_first S T (make_dep_pair S T s t)) s,
           proof_irrelevance (equal S (dep_first S T (make_dep_pair S T s t)) s)
              (make_dep_pair_first S T s t) H2
              (lambda H3: equal S (dep_first S T (make_dep_pair S T s t)) s,
               P (dep_first S T (make_dep_pair S T s t))
                 (rewrite_rev S T (dep_first S T (make_dep_pair S T s t)) s H3 t))
              (make_dep_pair_second S T s t (P (dep_first S T (make_dep_pair S T s t))) H1))
          (equal_reflexivity S s)).

