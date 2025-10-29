Require logic.
Require equal.

Definition satisfies_if:
   forall S: Type,
   Prop ->
   S ->
   S ->
   S ->
   Prop
:= lambda S: Type,
   lambda P: Prop,
   lambda s1: S,
   lambda s2: S,
   lambda s: S,
   and (P -> equal S s s1) (not P -> equal S s s2).

Definition if_exists:
   forall S: Type,
   forall P: Prop,
   forall s1: S,
   forall s2: S,
   exists S (satisfies_if S P s1 s2)
:= lambda S: Type,
   lambda P: Prop,
   lambda s1: S,
   lambda s2: S,
   or_induction P (not P) (exists S (satisfies_if S P s1 s2)) (excluded_middle P)
      (lambda H1: P,
       construct_exists S (satisfies_if S P s1 s2) s1
          (construct_and (P -> equal S s1 s1) (not P -> equal S s1 s2)
              (lambda H1: P, equal_reflexivity S s1)
              (lambda H2: not P, H2 H1 (equal S s1 s2))))
      (lambda H1: not P,
       construct_exists S (satisfies_if S P s1 s2) s2
          (construct_and (P -> equal S s2 s1) (not P -> equal S s2 s2)
              (lambda H2: P, H1 H2 (equal S s2 s1))
              (lambda H1: not P, equal_reflexivity S s2))).

Definition if:
   forall S: Type,
   Prop ->
   S ->
   S ->
   S
:= lambda S: Type,
   lambda P: Prop,
   lambda s1: S,
   lambda s2: S,
   epsilon S (satisfies_if S P s1 s2) (if_exists S P s1 s2).

Definition if_true:
   forall S: Type,
   forall P: Prop,
   forall s1: S,
   forall s2: S,
   P ->
   equal S (if S P s1 s2) s1
:= lambda S: Type,
   lambda P: Prop,
   lambda s1: S,
   lambda s2: S,
   and_left (P -> equal S (if S P s1 s2) s1) (not P -> equal S (if S P s1 s2) s2) 
      (epsilon_property S (satisfies_if S P s1 s2) (if_exists S P s1 s2)).

Definition if_false:
   forall S: Type,
   forall P: Prop,
   forall s1: S,
   forall s2: S,
   not P ->
   equal S (if S P s1 s2) s2
:= lambda S: Type,
   lambda P: Prop,
   lambda s1: S,
   lambda s2: S,
   and_right (P -> equal S (if S P s1 s2) s1) (not P -> equal S (if S P s1 s2) s2)
      (epsilon_property S (satisfies_if S P s1 s2) (if_exists S P s1 s2)).

