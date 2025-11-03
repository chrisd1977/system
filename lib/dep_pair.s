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

