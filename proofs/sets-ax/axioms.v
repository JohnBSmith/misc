
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
Definition EmptySet :=
  {x | False}.
Definition SgSet a :=
  {x | set a → x = a}.
Definition PairSet a b :=
  {x | (set a → x = a) ∨ (set b → x = b)}.
Definition Pair x y :=
  (PairSet (SgSet x) (PairSet x y)).

Notation "A ⊆ B" := (Subclass A B) (at level 70): class_scope.
Notation "( x , y )" := (Pair x y) (at level 0): class_scope.

Definition Power (X: Class) :=
  {A | A ⊆ X}.
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

Axiom comp: ∀P: Class → Prop,
  ∀x, set x ∧ P x ↔ x ∈ {u | P u}.

Axiom ext: ∀(A B: Class),
  A = B ↔ (∀x, x ∈ A ↔ x ∈ B).

Axiom subset: ∀(A B: Class),
  set B → A ⊆ B → set A.

Axiom pair_set: ∀(x y: Class),
  set x ∧ set y → set (PairSet x y).

Axiom union: ∀x,
  set x → set (⋃x).

Axiom pair_eq: ∀(x y x' y': Class), set x ∧ set y
  → ((x, y) = (x', y') ↔ x = x' ∧ y = y').

Axiom power_set: ∀(X: Class),
  set X → set (Power X).

Definition non_empty A := ∃x, x ∈ A.

Lemma dne_from_lem:
  LEM → ∀(A: Prop), ¬¬A → A.
Proof.
  intro lem. intro A. intro h.
  destruct (lem A) as [hl | hr].
  * exact hl.
  * exfalso. exact (h hr).
Qed.

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

Theorem pair_set_self x:
  set x → (PairSet x x) = (SgSet x).
Proof.
  intro hx. apply ext. intro u. split.
  * intro h. apply comp in h.
    destruct h as (hu, hux).
    apply -> comp. split.
    - exact hu.
    - destruct hux as [hl | hr].
      -- intros _. exact (hl hx).
      -- intros _. exact (hr hx).
  * intro h. apply comp in h.
    destruct h as (hu, hux).
    apply -> comp. split.
    - exact hu.
    - left. exact hux.
Qed.

Theorem sg_is_set x:
  set x → set (SgSet x).
Proof.
  intro h. rewrite <- (pair_set_self x h).
  exact (pair_set x x (conj h h)).
Qed.

Theorem pair_is_set {x y}:
  set x ∧ set y → set (x, y).
Proof.
  intros (hx, hy). unfold Pair.
  apply pair_set. split.
  * rewrite <- (pair_set_self x hx). apply pair_set.
    exact (conj hx hx).
  * apply pair_set.
    exact (conj hx hy).
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
  assert (hset := (conj (set_intro hx') (set_intro hy'))).
  apply eq_sym in heq.
  apply (pair_eq x' y' x y hset) in heq.
  destruct heq as (hxx', hyy').
  rewrite hxx' in hx'. rewrite hyy' in hy'.
  exact (conj hx' hy').
Qed.

Theorem sep (A: Class) (P: Class → Prop):
  set A → set {x | x ∈ A ∧ P x}.
Proof.
  intro h. apply (subset _ A h).
  unfold Subclass. intro x. intro hx.
  apply comp in hx. exact (proj1 (proj2 hx)).
Qed.

Theorem union_sg x:
  set x → x = ⋃(SgSet x).
Proof.
  intro hx. apply ext. intro u. split.
  * intro h. apply -> comp. split.
    - exact (set_intro h).
    - exists x. split.
      -- apply -> comp. split.
         --- exact hx.
         --- intros _. reflexivity.
      -- exact h.
  * intro h. apply comp in h. apply proj2 in h.
    destruct h as (x', (hx', hu)).
    apply comp in hx'. apply proj2 in hx'.
    rewrite (hx' hx) in hu. exact hu.
Qed.

Theorem pair_set_is_union_sg x y:
  (PairSet x y) = (SgSet x) ∪ (SgSet y).
Proof.
  apply ext. intro u. split.
  * intro h. apply union2_intro.
    apply comp in h. destruct h as (hu, h).
    destruct h as [hl | hr].
    - left. apply -> comp. exact (conj hu hl).
    - right. apply -> comp. exact (conj hu hr).
  * intro h.  apply comp in h.
    destruct h as (hu, h).
    apply -> comp. split.
    - exact hu.
    - destruct h as [hl | hr].
      -- apply comp in hl. apply proj2 in hl.
         left. exact hl.
      -- apply comp in hr. apply proj2 in hr.
         right. exact hr.
Qed.

