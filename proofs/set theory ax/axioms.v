
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
Notation "{ x ∈ X | P }" :=
  (Sep X (fun x: set => P)) (x at level 69).

Axiom sep: ∀X: set, ∀P: set → Prop,
  ∀x, x ∈ {u ∈ X | P u} ↔ x ∈ X ∧ P x.

Parameter Union: set → set.
Axiom union_axiom: ∀M x: set,
  x ∈ Union M ↔ ∃A, x ∈ A ∧ A ∈ M.
Notation "⋃ M" := (Union M) (at level 50): type_scope.

Definition Intersection (M: set): set :=
  {x ∈ ⋃ M | ∀A, A ∈ M → x ∈ A}.
Notation "⋂ M" := (Intersection M) (at level 50): type_scope.

Parameter PairSet: set → set → set.
Axiom pair_set_axiom: ∀a x y: set,
  a ∈ (PairSet x y) ↔ a = x ∨ a = y.

Parameter 𝓟: set → set.
Axiom power_set_axiom: ∀A M: set,
  A ∈ 𝓟 M ↔ A ⊆ M.

Definition Intersection2 (A B: set) :=
  {x ∈ A | x ∈ B}.
Notation "A ∩ B" := (Intersection2 A B) (at level 60): type_scope.

Definition Union2 (A B: set) :=
  ⋃(PairSet A B).
Notation "A ∪ B" := (Union2 A B) (at level 60): type_scope.

Definition Difference (A B: set) :=
  {x ∈ A | x ∉ B}.
Notation "A \ B" := (Difference A B) (at level 60): type_scope.

Lemma intersection2_intro {A B x: set}:
  x ∈ A ∧ x ∈ B → x ∈ A ∩ B.
Proof.
  intro h. apply sep. exact h.
Qed.

Lemma intersection2_elim {A B x: set}:
  x ∈ A ∩ B → x ∈ A ∧ x ∈ B.
Proof.
  intro h. apply sep in h. exact h.
Qed.

Lemma diff_intro {A B x: set}:
  x ∈ A ∧ x ∉ B → x ∈ A \ B  .
Proof.
  intro h. apply sep. exact h.
Qed.

Lemma diff_elim {A B x: set}:
  x ∈ A \ B → x ∈ A ∧ x ∉ B.
Proof.
  intro h. apply sep in h. exact h.
Qed.

Lemma union2_intro {A B x: set}:
  x ∈ A ∨ x ∈ B → x ∈ A ∪ B.
Proof.
  intro h. apply union_axiom.
  destruct h as [hA | hB].
  * exists A. split.
    - exact hA.
    - apply pair_set_axiom. left. reflexivity.
  * exists B. split.
    - exact hB.
    - apply pair_set_axiom. right. reflexivity.
Qed.

Lemma union2_elim {A B x: set}:
  x ∈ A ∪ B → x ∈ A ∨ x ∈ B.
Proof.
  intro h. apply union_axiom in h.
  destruct h as (X, (hx, hX)).
  apply pair_set_axiom in hX.
  destruct hX as [hA | hB].
  * left. rewrite hA in hx. exact hx.
  * right. rewrite hB in hx. exact hx.
Qed.

Lemma intersection_pair_set {A B: set}:
  ⋂(PairSet A B) = A ∩ B.
Proof.
  apply set_ext. intro x. split.
  * intro h. apply sep in h. destruct h as (hAB, hq).
    apply union2_elim in hAB.
    apply intersection2_intro. split.
    - destruct hAB as [hA | hB].
      -- exact hA.
      -- apply (hq A). apply pair_set_axiom.
         left. reflexivity.
    - destruct hAB as [hA | hB].
      -- apply (hq B). apply pair_set_axiom.
         right. reflexivity.
      -- exact hB.
  * intro h. apply intersection2_elim in h.
    destruct h as (hA, hB).
    apply sep. split.
    - apply union_axiom. exists A. split.
      -- exact hA.
      -- apply pair_set_axiom. left. reflexivity.
    - intro X. intro hX. apply pair_set_axiom in hX.
      destruct hX as [hXA | hXB].
      -- rewrite hXA. exact hA.
      -- rewrite hXB. exact hB.
Qed.

Lemma sep_is_subset (X: set) (P: set → Prop):
  {x ∈ X | P x} ⊆ X.
Proof.
  intro u. intro hu. apply sep in hu.
  exact (proj1 hu).
Qed.

