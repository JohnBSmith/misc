
Require Import Coq.Unicode.Utf8.

Definition LEM := ∀(A: Prop), A ∨ ¬A.

Parameter Class: Type.
Parameter In: Class → Class → Prop.
Parameter Comp: (Class → Prop) → Class.

Declare Scope class_scope.
Bind Scope class_scope with Class.
Open Scope class_scope.

Notation "x ∈ y" := (In x y) (at level 70): class_scope.
Notation "x ∉ y" := (¬In x y) (at level 70): class_scope.
Notation "{ x | P }" := (Comp (fun x: Class => P)): class_scope.

Definition set (A: Class) := ∃C, A ∈ C.
Definition Subclass (A B: Class) :=
  ∀x, x ∈ A → x ∈ B.
Notation "A ⊆ B" := (Subclass A B) (at level 70): class_scope.

Axiom comp: ∀P: Class → Prop,
  ∀x, set x ∧ P x ↔ x ∈ {u | P u}.

Axiom ext: ∀(A B: Class),
  A = B ↔ (∀x, x ∈ A ↔ x ∈ B).

Axiom subset: ∀(A B: Class),
  set B → A ⊆ B → set A.

Parameter Pair: Class → Class → Class.
Notation "( x , y )" := (Pair x y) (at level 0): class_scope.

Axiom pair_eq: ∀x y x' y',
  (x, y) = (x', y') ↔ x = x' ∧ y = y'.

Axiom pair_is_set: ∀(x y: Class),
  set x ∧ set y ↔ set (x, y).

Definition EmptySet :=
  {x | False}.
Definition Intersection2 (A B: Class) :=
  {x | x ∈ A ∧ x ∈ B}.
Definition Union2 (A B: Class) :=
  {x | x ∈ A ∨ x ∈ B}.
Definition Difference (A B: Class) :=
  {x | x ∈ A ∧ x ∉ B}.
Definition SymDiff (A B: Class) :=
  {x | (x ∈ A ∧ x ∉ B) ∨ (x ∈ B ∧ x ∉ A)}.
Definition Compl (A: Class) :=
  {x | x ∉ A}.
Definition Intersection (M: Class) :=
  {x | ∀A, A ∈ M → x ∈ A}.
Definition Union (M: Class) :=
  {x | ∃A, A ∈ M ∧ x ∈ A}.
Definition Prod (A B: Class) :=
  {t | ∃x y, x ∈ A ∧ y ∈ B ∧ t = (x, y)}.

Notation "∅" := EmptySet (at level 0): class_scope.
Notation "A ∩ B" := (Intersection2 A B) (at level 40): class_scope.
Notation "A ∪ B" := (Union2 A B) (at level 50): class_scope.
Notation "A \ B" := (Difference A B) (at level 50): class_scope.
Notation "A × B" := (Prod A B) (at level 40): class_scope.
Notation "⋂ M" := (Intersection M) (at level 30): class_scope.
Notation "⋃ M" := (Union M) (at level 30): class_scope.

Definition non_empty A := ∃x, x ∈ A.

Lemma empty_set_property:
  ∀x, x ∉ ∅.
Proof.
  intro x. intro h. apply comp in h.
  exact (proj2 h).
Qed.

Lemma set_intro {x A}:
  x ∈ A → set x.
Proof.
  intro h. unfold set. exists A. exact h.
Qed.

Theorem subclass_refl A:
  A ⊆ A.
Proof.
  unfold Subclass. intro x. intro h. exact h.
Qed.

Theorem subclass_antisym {A B}:
  A ⊆ B ∧ B ⊆ A → A = B.
Proof.
  intros (hAB, hBA). apply ext. intro x. split.
  * intro h. unfold Subclass in hAB. exact (hAB x h).
  * intro h. unfold Subclass in hBA. exact (hBA x h).
Qed.

Theorem subclass_trans {A B C}:
  A ⊆ B ∧ B ⊆ C → A ⊆ C.
Proof.
  intros (hAB, hBC). unfold Subclass.
  intro x. intro h.
  unfold Subclass in hAB.
  unfold Subclass in hBC.
  exact (hBC x (hAB x h)).
Qed.

Lemma intersection2_intro {A B x}:
  x ∈ A ∧ x ∈ B → x ∈ A ∩ B.
Proof.
  intro h. apply -> comp. split.
  * unfold set. exists A. exact (proj1 h).
  * exact h.
Qed.

Lemma intersection2_elim {A B x}:
  x ∈ A ∩ B → x ∈ A ∧ x ∈ B.
Proof.
  intro h. apply comp in h. exact (proj2 h).
Qed.

Lemma union2_intro {A B x}:
  x ∈ A ∨ x ∈ B → x ∈ A ∪ B.
Proof.
  intro h. apply -> comp. split.
  * unfold set. destruct h as [hA | hB].
    - exists A. exact hA.
    - exists B. exact hB.
  * exact h.
Qed.

Lemma union2_elim {A B x}:
  x ∈ A ∪ B → x ∈ A ∨ x ∈ B.
Proof.
  intro h. apply comp in h. exact (proj2 h).
Qed.

Lemma difference_intro {A B x}:
  x ∈ A ∧ x ∉ B → x ∈ A \ B.
Proof.
  intro h. apply -> comp. split.
  * unfold set. exists A. exact (proj1 h).
  * exact h.
Qed.

Lemma difference_elim {A B x}:
  x ∈ A \ B → x ∈ A ∧ x ∉ B.
Proof.
  intro h. apply comp in h. exact (proj2 h).
Qed.

Lemma intersection_intro {M x}:
  set x → (∀A, A ∈ M → x ∈ A) → x ∈ ⋂M.
Proof.
  intros hx h. apply -> comp. split.
  * exact hx.
  * exact h.
Qed.

Lemma intersection_elim {M x}:
  x ∈ ⋂M → (∀A, A ∈ M → x ∈ A).
Proof.
  intro h. intro A. intro hA.
  apply comp in h.
  exact ((proj2 h) A hA).
Qed.

Lemma union_intro {M x}:
  (∃A, A ∈ M ∧ x ∈ A) → x ∈ ⋃M.
Proof.
  intro h. destruct h as (A, (hA, hx)).
  apply -> comp. split.
  * exact (set_intro hx).
  * exists A. exact (conj hA hx).
Qed.

Lemma union_elim {M x}:
  x ∈ ⋃M → (∃A, A ∈ M ∧ x ∈ A).
Proof.
  intro h. apply comp in h. exact (proj2 h).
Qed.

Lemma prod_intro {A B t}:
  (∃x y, x ∈ A ∧ y ∈ B ∧ t = (x, y)) → t ∈ A × B.
Proof.
  intro h. apply -> comp. split.
  * destruct h as (x, (y, (hx, (hy, ht)))).
    rewrite ht. apply pair_is_set.
    exact (conj (set_intro hx) (set_intro hy)).
  * exact h.
Qed.

Lemma prod_elim {A B t}:
  t ∈ A × B → (∃x y, x ∈ A ∧ y ∈ B ∧ t = (x, y)).
Proof.
  intro h. apply comp in h.
  apply proj2 in h. exact h.
Qed.

Lemma prod_intro_term {A B x y}:
  x ∈ A ∧ y ∈ B → (x, y) ∈ A × B.
Proof.
  intros (hx, hy). apply -> comp.
  split.
  * apply pair_is_set.
    exact (conj (set_intro hx) (set_intro hy)).
  * exists x. exists y.
    exact (conj hx (conj hy (eq_refl (x, y)))).
Qed.

Lemma prod_elim_term {A B x y}:
  (x, y) ∈ A × B → x ∈ A ∧ y ∈ B.
Proof.
  intro h. apply comp in h. apply proj2 in h.
  destruct h as (x', (y', (hx', (hy', heq)))).
  apply pair_eq in heq. destruct heq as (hxx', hyy').
  rewrite hxx'. rewrite hyy'. exact (conj hx' hy').
Qed.

