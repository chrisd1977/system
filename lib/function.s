Require logic.
Require equal.

Definition injective: forall S: Type, forall T: Type, (S -> T) -> Prop
:= lambda S: Type,
   lambda T: Type,
   lambda f: S -> T,
   forall s1: S,
   forall s2: S,
   equal T (f s1) (f s2) ->
   equal S s1 s2.

Definition surjective: forall S: Type, forall T: Type, (S -> T) -> Prop
:= lambda S: Type,
   lambda T: Type,
   lambda f: S -> T,
   forall t: T,
   exists S (lambda s: S, equal T (f s) t).

Definition infinite_function: forall S: Type, (S -> S) -> Prop
:= lambda S: Type,
   lambda f: S -> S,
   and (injective S S f) (not (surjective S S f)).

