
Definition True: Prop
:= forall P: Prop, P -> P.

Definition False: Prop
:= forall P: Prop, P.

Definition not: Prop -> Prop
:= lambda P: Prop, P -> False.

Definition impl_reverse:
   forall P: Prop,
   forall Q: Prop,
   (P -> Q) ->
   not Q ->
   not P
:= lambda P: Prop,
   lambda Q: Prop,
   lambda H1: P -> Q,
   lambda H2: not Q,
   lambda H3: P,
   H2 (H1 H3).

Definition or: Prop -> Prop -> Prop
:= lambda P: Prop,
   lambda Q: Prop,
   not P ->
   Q.

Definition or_left:
   forall P: Prop,
   forall Q: Prop,
   P ->
   or P Q
:= lambda P: Prop,
   lambda Q: Prop,
   lambda H1: P,
   lambda H2: not P,
   H2 H1 Q.

Definition or_right:
   forall P: Prop,
   forall Q: Prop,
   Q ->
   or P Q
:= lambda P: Prop,
   lambda Q: Prop,
   lambda H1: Q,
   lambda H2: not P,
   H1.

Definition and: Prop -> Prop -> Prop
:= lambda P: Prop,
   lambda Q: Prop,
   not (or (not P) (not Q)).

Definition exists: forall S: Type, forall P: S -> Prop, Prop
:= lambda S: Type,
   lambda P: S -> Prop,
   not (forall s: S, not (P s)).

Definition construct_exists:
   forall S: Type,
   forall P: S -> Prop,
   forall s: S,
   P s ->
   exists S P
:= lambda S: Type,
   lambda P: S -> Prop,
   lambda s: S,
   lambda H1: P s,
   lambda H2: forall s: S, not (P s),
   H2 s H1.

Axiom epsilon:
   forall S: Type,
   forall P: S -> Prop,
   exists S P ->
   S.

Axiom epsilon_property:
   forall S: Type,
   forall P: S -> Prop,
   forall H: exists S P,
   P (epsilon S P H).

Definition double_not:
   forall P: Prop,
   not (not P) ->
   P
:= lambda P: Prop,
   lambda H: not (not P),
   epsilon_property Prop (lambda Q: Prop, P)
      (lambda Q: Prop -> not P, H (Q P)).

Definition excluded_middle:
   forall P: Prop,
   or P (not P)
:= lambda P: Prop,
   lambda H: not P,
   H.

Definition and_left:
   forall P: Prop,
   forall Q: Prop,
   and P Q ->
   P
:= lambda P: Prop,
   lambda Q: Prop,
   lambda H1: and P Q,
   double_not P
      (lambda H2: not P, H1 (lambda H3: not (not P), lambda H4: Q, H3 H2)).

Definition and_right:
   forall P: Prop,
   forall Q: Prop,
   and P Q ->
   Q
:= lambda P: Prop,
   lambda Q: Prop,
   lambda H1: and P Q,
   double_not Q (lambda H2: not Q, H1 (lambda R: not (not P), H2)).

Definition construct_and:
   forall P: Prop,
   forall Q: Prop,
   P ->
   Q ->
   and P Q
:= lambda P: Prop,
   lambda Q: Prop,
   lambda H1: P,
   lambda H2: Q,
   lambda H3: or (not P) (not Q),
   H3 (lambda H4: not P, H4 H1) H2.

Definition not_impl_is_and:
   forall P: Prop,
   forall Q: Prop,
   not (P -> Q) ->
   and P (not Q)
:= lambda P: Prop,
   lambda Q: Prop,
   lambda H1: not (P -> Q),
   construct_and P (not Q)
      (double_not P (lambda H2: not P, H1 (lambda H3: P, H2 H3 Q)))
      (lambda H2: Q, H1 (lambda H3: P, H2)).

Definition or_not_right:
   forall P: Prop,
   forall Q: Prop,
   or P Q ->
   not Q ->
   P
:= lambda P: Prop,
   lambda Q: Prop,
   lambda H1: or P Q,
   lambda H2: not Q,
   double_not P (lambda H3: not P, H2 (H1 H3)).

Definition or_induction:
   forall P: Prop,
   forall Q: Prop,
   forall R: Prop,
   or P Q ->
   (P -> R) ->
   (Q -> R) ->
   R
:= lambda P: Prop,
   lambda Q: Prop,
   lambda R: Prop,
   lambda H1: or P Q,
   lambda H2: P -> R,
   lambda H3: Q -> R,
   double_not R (lambda H4: not R, H4 (H3 (H1 (impl_reverse P R H2 H4)))).

Definition not_forall_exists:
   forall S: Type,
   forall P: S -> Prop,
   not (forall s: S, P s) ->
   exists S (lambda s: S, not (P s))
:= lambda S: Type,
   lambda P: S -> Prop,
   lambda H1: not (forall s: S, P s),
   lambda H2: forall s: S, not (not (P s)),
   H1 (lambda s: S, double_not (P s) (H2 s)).

