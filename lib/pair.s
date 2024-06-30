Require logic.
Require equal.

Axiom pair:
   forall S: Type,
   forall T: S -> Type,
   Type.

Axiom make_pair:
   forall S: Type,
   forall T: S -> Type,
   forall s: S,
   forall t: T s,
   pair S T.

Axiom first:
   forall S: Type,
   forall T: S -> Type,
   pair S T ->
   S.

Axiom second:
   forall S: Type,
   forall T: S -> Type,
   forall p: pair S T,
   T (first S T p).

Axiom make_pair_first:
   forall S: Type,
   forall T: S -> Type,
   forall s: S,
   forall t: T s,
   equal S (first S T (make_pair S T s t)) s.

Axiom make_pair_second:
   forall S: Type,
   forall T: S -> Type,
   forall s: S,
   forall t: T s,
   equal (T s)
      (rewrite S T (first S T (make_pair S T s t)) s (make_pair_first S T s t)
          (second S T (make_pair S T s t)))
      t.

Axiom pair_unique:
   forall S: Type,
   forall T: S -> Type,
   forall p: pair S T,
   equal (pair S T) p (make_pair S T (first S T p) (second S T p)).

