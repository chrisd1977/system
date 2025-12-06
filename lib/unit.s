Require logic.
Require equal.
Require dep_pair.

Definition unit: Type
:= dep_pair Prop (equal Prop True).

Definition tt: unit
:= make_dep_pair Prop (equal Prop True) True (equal_reflexivity Prop True).

Definition split_pair_is_tt:
   forall tt2: unit,
   equal unit
      (make_dep_pair Prop (equal Prop True) (dep_first Prop (equal Prop True) tt2)
          (dep_second Prop (equal Prop True) tt2))
      tt
:= lambda tt2: unit,
   equal_symmetry Prop True (dep_first Prop (equal Prop True) tt2)
      (dep_second Prop (equal Prop True) tt2)
      (lambda R: Prop,
       forall H2: equal Prop True (dep_first Prop (equal Prop True) tt2),
       forall H3: equal Prop True R,
       equal unit
          (make_dep_pair Prop (equal Prop True) (dep_first Prop (equal Prop True) tt2) H2)
          (make_dep_pair Prop (equal Prop True) R H3))
      (lambda H2: equal Prop True (dep_first Prop (equal Prop True) tt2),
       lambda H3: equal Prop True (dep_first Prop (equal Prop True) tt2),
       equal_function (equal Prop True (dep_first Prop (equal Prop True) tt2)) unit
          (make_dep_pair Prop (equal Prop True) (dep_first Prop (equal Prop True) tt2))
          H2 H3
          (proof_irrelevance (equal Prop True (dep_first Prop (equal Prop True) tt2)) H2 H3))
      (dep_second Prop (equal Prop True) tt2)
      (equal_reflexivity Prop True).

Definition unit_is_tt:
   forall tt2: unit,
   equal unit tt2 tt
:= lambda tt2: unit,
   equal_transitivity unit tt2
      (make_dep_pair Prop (equal Prop True) (dep_first Prop (equal Prop True) tt2)
          (dep_second Prop (equal Prop True) tt2))
      tt
      (dep_pair_unique Prop (equal Prop True) tt2)
      (split_pair_is_tt tt2).

Definition unit_unique:
   forall tt1: unit,
   forall tt2: unit,
   equal unit tt1 tt2
:= lambda tt1: unit,
   lambda tt2: unit,
   equal_transitivity unit tt1 tt tt2 (unit_is_tt tt1)
      (equal_symmetry unit tt2 tt (unit_is_tt tt2)).

