Require logic.

Definition equal:
   forall S: Type, S -> S -> Prop
:= lambda S: Type,
   lambda s1: S,
   lambda s2: S,
   forall P: S -> Prop,
   P s1 ->
   P s2.

Definition equal_reflexivity:
   forall S: Type,
   forall s: S,
   equal S s s
:= lambda S: Type,
   lambda s: S,
   lambda P: S -> Prop,
   lambda p: P s,
   p.

Definition equal_symmetry:
   forall S: Type,
   forall s: S,
   forall t: S,
   equal S s t ->
   equal S t s
:= lambda S: Type,
   lambda s: S,
   lambda t: S,
   lambda H1: equal S s t,
   lambda P: S -> Prop,
   lambda H2: P t,
   double_not (P s) (lambda H3: not (P s), H1 (lambda s: S, not (P s)) H3 H2).

Definition equal_transitivity:
   forall S: Type,
   forall s: S,
   forall t: S,
   forall u: S,
   equal S s t ->
   equal S t u ->
   equal S s u
:= lambda S: Type,
   lambda s: S,
   lambda t: S,
   lambda u: S,
   lambda H1: equal S s t,
   lambda H2: equal S t u,
   H2 (equal S s) H1.

Axiom proof_irrelevance:
   forall P: Prop,
   forall H1: P,
   forall H2: P,
   equal P H1 H2.

Axiom rewrite:
   forall S: Type,
   forall P: S -> Type,
   forall s1: S,
   forall s2: S,
   equal S s1 s2 ->
   P s1 ->
   P s2.

Axiom rewrite_same:
   forall S: Type,
   forall P: S -> Type,
   forall s: S,
   forall H: equal S s s,
   forall p: P s,
   equal (P s) (rewrite S P s s H p) p.

Definition rewrite_rev:
   forall S: Type,
   forall P: S -> Type,
   forall s1: S,
   forall s2: S,
   equal S s1 s2 ->
   P s2 ->
   P s1
:= lambda S: Type,
   lambda P: S -> Type,
   lambda s1: S,
   lambda s2: S,
   lambda H1: equal S s1 s2,
   rewrite S P s2 s1 (equal_symmetry S s1 s2 H1).

Definition equal_function:
   forall S: Type,
   forall T: Type,
   forall f: S -> T,
   forall s1: S,
   forall s2: S,
   equal S s1 s2 ->
   equal T (f s1) (f s2)
:= lambda S: Type,
   lambda T: Type,
   lambda f: S -> T,
   lambda s1: S,
   lambda s2: S,
   lambda H1: equal S s1 s2,
   rewrite S (lambda s: S, equal T (f s1) (f s)) s1 s2 H1 (equal_reflexivity T (f s1)).

