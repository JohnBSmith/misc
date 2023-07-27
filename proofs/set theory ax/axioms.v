
Require Import Coq.Unicode.Utf8.
Require Export Coq.Logic.Classical.

Parameter set: Type.
Parameter EmptySet: set.
Parameter In: set → set → Prop.
Notation "x ∈ y" := (In x y) (at level 70): type_scope.
Notation "x ∉ y" := (¬In x y) (at level 70): type_scope.
Notation "∅" := EmptySet: type_scope.

Definition Subset (A B: set): Prop :=
  ∀x, x ∈ A → x ∈ B.

Notation "A ⊆ B" := (Subset A B) (at level 70): type_scope.

Axiom set_ext: ∀A B, (∀x, x ∈ A ↔ x ∈ B) → A = B.
Axiom empty_set_axiom: ∀x, x ∉ ∅.

Parameter Sep: set → (set → Prop) → set.
Notation "{ x ∈ X | P }" := (Sep X (fun x: set => P)) (x at level 69).

Axiom sep: ∀X: set, ∀P: set → Prop,
  ∀x, x ∈ {u ∈ X | P u} ↔ x ∈ X ∧ P x.

Definition Intersection (A B: set) :=
  {x ∈ A | x ∈ B}.
Notation "A ∩ B" := (Intersection A B) (at level 60): type_scope.

