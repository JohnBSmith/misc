
Require Import Coq.Unicode.Utf8.
Require Export Coq.Logic.Classical.

Parameter set: Type.
Parameter EmptySet: set.
Parameter In: set → set → Prop.

Declare Scope set_scope.
Bind Scope set_scope with set.
Open Scope set_scope.

Notation "x ∈ y" := (In x y) (at level 70): set_scope.
Notation "x ∉ y" := (¬In x y) (at level 70): set_scope.
Notation "∅" := EmptySet: set_scope.

Definition Subset (A B: set): Prop :=
  ∀x, x ∈ A → x ∈ B.
Notation "A ⊆ B" := (Subset A B) (at level 70): set_scope.

Axiom set_ext: ∀A B, (∀x, x ∈ A ↔ x ∈ B) → A = B.
Axiom empty_set_axiom: ∀x, x ∉ ∅.

Parameter Comp: (set → Prop) → set.
Notation "{ x | P }" := (Comp (fun x: set => P)): set_scope.

Axiom comp: ∀P: set → Prop,
  ∀x, x ∈ {u | P u} ↔ P x.

Lemma comp_intro {P: set → Prop} {x: set}:
  P x → x ∈ {u | P u}.
Proof.
  intro h. apply comp. exact h.
Qed.

Lemma comp_elim {P: set → Prop} {x: set}:
  x ∈ {u | P u} → P x.
Proof.
  intro h. apply -> comp in h. exact h.
Qed.

Definition Intersection2 (A B: set) :=
  {x | x ∈ A ∧ x ∈ B}.

Definition Union2 (A B: set) :=
  {x | x ∈ A ∨ x ∈ B}.

Definition SetDiff (A B: set) :=
  {x | x ∈ A ∧ x ∉ B}.

Definition Intersection (M: set) :=
  {x | ∀A, A ∈ M → x ∈ A}.

Definition Union (M: set) :=
  {x | ∃A, A ∈ M ∧ x ∈ A}.

Notation "A ∩ B" := (Intersection2 A B) (at level 40): set_scope.
Notation "A ∪ B" := (Union2 A B) (at level 50): set_scope.
Notation "A \ B" := (SetDiff A B) (at level 50): set_scope.
Notation "⋂ M" := (Intersection M) (at level 30): set_scope.
Notation "⋃ M" := (Union M) (at level 30): set_scope.

Lemma intersection2_intro {A B x: set}:
  x ∈ A ∧ x ∈ B → x ∈ A ∩ B.
Proof.
  intro h. apply comp_intro. exact h.
Qed.

Lemma intersection2_elim {A B x: set}:
  x ∈ A ∩ B → x ∈ A ∧ x ∈ B.
Proof.
  intro h. apply comp_elim in h.
  simpl in h. exact h.
Qed.

Lemma union2_intro {A B x: set}:
  x ∈ A ∨ x ∈ B → x ∈ A ∪ B.
Proof.
  intro h. apply comp_intro. exact h.
Qed.

Lemma union2_elim {A B x: set}:
  x ∈ A ∪ B → x ∈ A ∨ x ∈ B.
Proof.
  intro h. apply comp_elim in h.
  simpl in h. exact h.
Qed.

Lemma set_diff_intro {A B x: set}:
  x ∈ A ∧ x ∉ B → x ∈ A \ B.
Proof.
  intro h. apply comp_intro. exact h.
Qed.

Lemma set_diff_elim {A B x: set}:
  x ∈ A \ B → x ∈ A ∧ x ∉ B.
Proof.
  intro h. apply comp_elim in h.
  simpl in h. exact h.
Qed.

Lemma intersection_intro {M x: set}:
  (∀A, A ∈ M → x ∈ A) → x ∈ ⋂M.
Proof.
  intro h. apply comp_intro. exact h.
Qed.

Lemma intersection_elim (M x: set):
  x ∈ ⋂M → (∀A, A ∈ M → x ∈ A).
Proof.
  intro h. apply comp_elim in h.
  simpl in h. exact h.
Qed.

