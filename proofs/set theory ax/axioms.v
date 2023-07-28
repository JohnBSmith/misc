
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

Parameter UnionSystem: set → set.
Axiom union_system_ext: ∀M x: set,
  x ∈ UnionSystem M ↔ ∃A, x ∈ A ∧ A ∈ M.
Notation "⋃ M" := (UnionSystem M) (at level 50): type_scope.

Definition IntersectionSystem (M: set): set :=
  {x ∈ ⋃ M | ∀A, A ∈ M → x ∈ A}.
Notation "⋂ M" := (IntersectionSystem M) (at level 50): type_scope.

Parameter PairSet: set → set → set.
Axiom pair_set_ext: ∀a x y: set,
  a ∈ (PairSet x y) ↔ a = x ∨ a = y.

Parameter 𝓟: set → set.
Axiom power_set_ext: ∀A M: set,
  A ∈ 𝓟 M ↔ A ⊆ M.

Definition Intersection (A B: set) :=
  {x ∈ A | x ∈ B}.
Notation "A ∩ B" := (Intersection A B) (at level 60): type_scope.

Definition Union (A B: set) :=
  ⋃(PairSet A B).
Notation "A ∪ B" := (Union A B) (at level 60): type_scope.

Definition Difference (A B: set) :=
  {x ∈ A | x ∉ B}.
Notation "A \ B" := (Difference A B) (at level 60): type_scope.

Lemma intersection_intro {A B x: set}:
  x ∈ A ∧ x ∈ B → x ∈ A ∩ B.
Proof.
  intro h. apply sep. exact h.
Qed.

Lemma intersection_elim {A B x: set}:
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

Lemma union_intro {A B x: set}:
  x ∈ A ∨ x ∈ B → x ∈ A ∪ B.
Proof.
  intro h. apply union_system_ext.
  destruct h as [hA | hB].
  * exists A. split.
    - exact hA.
    - apply pair_set_ext. left. reflexivity.
  * exists B. split.
    - exact hB.
    - apply pair_set_ext. right. reflexivity.
Qed.

Lemma union_elim {A B x: set}:
  x ∈ A ∪ B → x ∈ A ∨ x ∈ B.
Proof.
  intro h. apply union_system_ext in h.
  destruct h as (X, (hx, hX)).
  apply pair_set_ext in hX.
  destruct hX as [hA | hB].
  * left. rewrite hA in hx. exact hx.
  * right. rewrite hB in hx. exact hx.
Qed.

Lemma intersection_pair_set {A B: set}:
  ⋂(PairSet A B) = A ∩ B.
Proof.
  apply set_ext. intro x. split.
  * intro h. apply sep in h. destruct h as (hAB, hq).
    apply union_elim in hAB.
    apply intersection_intro. split.
    - destruct hAB as [hA | hB].
      -- exact hA.
      -- apply (hq A). apply pair_set_ext.
         left. reflexivity.
    - destruct hAB as [hA | hB].
      -- apply (hq B). apply pair_set_ext.
         right. reflexivity.
      -- exact hB.
  * intro h. apply intersection_elim in h.
    destruct h as (hA, hB).
    apply sep. split.
    - apply union_system_ext. exists A. split.
      -- exact hA.
      -- apply pair_set_ext. left. reflexivity.
    - intro X. intro hX. apply pair_set_ext in hX.
      destruct hX as [hXA | hXB].
      -- rewrite hXA. exact hA.
      -- rewrite hXB. exact hB.
Qed.

