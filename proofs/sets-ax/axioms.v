
Require Import Coq.Unicode.Utf8.

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

Definition succ n := n ∪ (SgSet n).
Definition InductiveSets :=
  {A | ∅ ∈ A ∧ (∀n, n ∈ A → succ n ∈ A)}.
Definition ℕ := ⋂InductiveSets.

Axiom LEM:
  ∀(A: Prop), A ∨ ¬A.

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

Axiom power_set: ∀(X: Class),
  set X → set (Power X).

Axiom infinity:
  ∃A, A ∈ InductiveSets.

Definition non_empty A := ∃x, x ∈ A.

Theorem DNE:
  ∀(A: Prop), ¬¬A → A.
Proof.
  intro A. intro h.
  destruct (LEM A) as [hl | hr].
  * exact hl.
  * exfalso. exact (h hr).
Qed.

Theorem neg_ex {X: Type} {P: X → Prop}:
  (¬∃x, P x) → (∀x, ¬P x).
Proof.
  intro hn. intro x. intro hx.
  assert (h := ex_intro P x hx).
  exact (hn h).
Qed.

Lemma ext_rev {A B}:
  A = B → ∀x, x ∈ A ↔ x ∈ B.
Proof.
  intro h. intro x. rewrite h. split.
  * intro hx. exact hx.
  * intro hx. exact hx.
Qed.

Lemma set_intro {x A}:
  x ∈ A → set x.
Proof.
  intro h. unfold set. exists A. exact h.
Qed.

Lemma empty_set_property:
  ∀x, x ∉ ∅.
Proof.
  intro x. intro h. apply comp in h.
  exact (proj2 h).
Qed.

Theorem subclass1_pair_set x y:
  (SgSet x) ⊆ (PairSet x y).
Proof.
  unfold Subclass. intros u.
  intro h. apply -> comp. split.
  * exact (set_intro h).
  * left. apply comp in h. exact (proj2 h).
Qed.

Theorem subclass2_pair_set x y:
  (SgSet y) ⊆ (PairSet x y).
Proof.
  unfold Subclass. intros u.
  intro h. apply -> comp. split.
  * exact (set_intro h).
  * right. apply comp in h. exact (proj2 h).
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


(* Results about what constitutes a set *)
(* ==================================== *)

Theorem empty_set_is_set:
  set ∅.
Proof.
  destruct infinity as (A, h).
  apply comp in h. destruct h as (_, (h, _)).
  exact (set_intro h).
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

Theorem sep_is_set (A: Class) (P: Class → Prop):
  set A → set {x | x ∈ A ∧ P x}.
Proof.
  intro h. apply (subset _ A h).
  unfold Subclass. intro x. intro hx.
  apply comp in hx. exact (proj1 (proj2 hx)).
Qed.

Theorem non_empty_class A:
  A ≠ ∅ → ∃x, x ∈ A.
Proof.
  intro h. apply DNE. intro hn.
  assert (hn' := neg_ex hn). simpl in hn'.
  assert (h0: A = ∅). {
    apply ext. intro x. split.
    * intro hx. exfalso. exact (hn' x hx).
    * intro hx. exfalso. exact ((empty_set_property x) hx).
  }
  exact (h h0).
Qed.

Theorem intersection_is_set M:
  M ≠ ∅ → set (⋂M).
Proof.
  intro hM. apply non_empty_class in hM.
  destruct hM as (A, hA).
  apply (subset _ A (set_intro hA)).
  unfold Subclass. intros x hx.
  apply comp in hx. apply proj2 in hx.
  exact (hx A hA).
Qed.


(* Basic lemmas and theorems *)
(* ========================= *)

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

Lemma intersection2_equi {A B x}:
  x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B.
Proof.
  split.
  * exact intersection2_elim.
  * exact intersection2_intro.
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

Lemma union2_equi {A B x}:
  x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B.
Proof.
  split.
  * exact union2_elim.
  * exact union2_intro.
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


(* Basic results about classes *)
(* =========================== *)

(* The universal class. *)
Definition UnivCl := {x | True}.

(* The diagonal class (Russell's class). *)
Definition DiagCl := {x | x ∉ x}.

Theorem iff_contra {A: Prop}:
  (A ↔ ¬A) → False.
Proof.
  intro h. destruct h as (hl, hr).
  assert (hnA: ¬A). {
    intro hA. exact ((hl hA) hA).
  }
  exact (hnA (hr hnA)).
Qed.

(* Russell's paradox. *)
Theorem DiagCl_is_proper:
  ¬set DiagCl.
Proof.
  set (R := DiagCl). intro hR.
  assert (h: R ∈ R ↔ R ∉ R). {
    split.
    * intro h. unfold R in h at 2. apply comp in h.
      exact (proj2 h).
    * intro h. unfold R at 2. apply -> comp.
      exact (conj hR h).
  }
  exact (iff_contra h).
Qed.

Theorem UnivCl_by_eq:
  UnivCl = {x | x = x}.
Proof.
  apply ext. intro x. split.
  * intro h. apply comp in h. destruct h as (h, _).
    apply -> comp. split.
    - exact h.
    - reflexivity.
  * intro h. apply comp in h. destruct h as (h, _).
    apply -> comp. split.
    - exact h.
    - exact I.
Qed.

Theorem in_UnivCl_iff_set x:
  x ∈ UnivCl ↔ set x.
Proof.
  split.
  * intro h. apply comp in h. exact (proj1 h).
  * intro h. apply -> comp. exact (conj h I).
Qed.

Theorem DiagCl_subclass_UnivCl:
  DiagCl ⊆ UnivCl.
Proof.
  unfold Subclass. intro x. intro h.
  apply comp in h. apply -> comp.
  exact (conj (proj1 h) I).
Qed.

Theorem UnivCl_is_proper:
  ¬set UnivCl.
Proof.
  assert (hR := DiagCl_subclass_UnivCl).
  intro h. apply (subset DiagCl UnivCl h) in hR.
  exact (DiagCl_is_proper hR).
Qed.

Theorem compl_empty_set:
  Compl ∅ = UnivCl.
Proof.
  apply ext. intro x. split.
  * intro h. apply comp in h. apply proj1 in h.
    apply -> comp. exact (conj h I).
  * intro h. apply comp in h. apply proj1 in h.
    apply -> comp.
    exact (conj h (empty_set_property x)).
Qed.

Theorem UnivCl_extremal A:
  UnivCl ∪ A = UnivCl.
Proof.
  apply ext. split.
  * intro h. apply -> comp.
    apply comp in h. exact ((conj (proj1 h) I)).
  * intro h. apply comp in h. apply proj1 in h.
    apply -> comp. split.
    - exact h.
    - left. apply -> comp. exact (conj h I).
Qed.

Theorem comp_subclass_UnivCl:
  ∀(P: Class → Prop), {x | P x} ⊆ UnivCl.
Proof.
  intros P. unfold Subclass. intros x hx.
  apply comp in hx. apply -> comp.
  exact (conj (proj1 hx) I).
Qed.

Theorem SgSet_of_proper_class C:
  ¬set C → SgSet C = UnivCl.
Proof.
  intro h. apply ext. intro x. split.
  * intro hx. apply comp in hx.
    apply proj1 in hx.
    apply -> comp. exact (conj hx I).
  * intro hx. apply comp in hx.
    apply proj1 in hx.
    apply -> comp. split.
    - exact hx.
    - intro hC. exfalso.
      exact (h hC).
Qed.

Definition SgSetBogus a :=
  {x | x = a}.

Theorem SgSetBogus_of_proper_class C:
  ¬set C → SgSetBogus C = ∅.
Proof.
  intro h. apply ext. intro x. split.
  * intro hx. exfalso. apply comp in hx.
    destruct hx as (hx, heq).
    rewrite heq in hx.
    exact (h hx).
  * intro hx. exfalso.
    exact (empty_set_property x hx).
Qed.

Theorem sg_is_set_rev x:
  set (SgSet x) → set x.
Proof.
  intro h. apply DNE. intro hn.
  assert (heq := SgSet_of_proper_class x hn).
  rewrite heq in h. exact (UnivCl_is_proper h).
Qed.

Theorem pair_set_is_set_rev x y:
  set (PairSet x y) → set x ∧ set y.
Proof.
  intro h. 
  assert (h1 := subclass1_pair_set x y).
  assert (h2 := subclass2_pair_set x y).
  apply (subset _ _ h) in h1.
  apply (subset _ _ h) in h2.
  apply sg_is_set_rev in h1.
  apply sg_is_set_rev in h2.
  exact (conj h1 h2).
Qed.

Theorem pair_is_set_rev x y:
  set (x, y) → set x ∧ set y.
Proof.
  intro h. unfold Pair in h.
  apply pair_set_is_set_rev in h.
  destruct h as (_, hxy).
  apply pair_set_is_set_rev in hxy.
  exact hxy.
Qed.

Theorem intersection_empty_set:
  ⋂∅ = UnivCl.
Proof.
  apply ext. intro x. split.
  * intro h. apply comp in h.
    apply -> comp. apply proj1 in h.
    exact (conj h I).
  * intro h. apply comp in h. apply proj1 in h.
    apply -> comp. split.
    - exact h.
    - intros A hA. exfalso.
      exact ((empty_set_property A) hA).
Qed.

Theorem intersection_UnivCl:
  ⋂UnivCl = ∅.
Proof.
  apply ext. intro x. split.
  * intro h. apply comp in h. apply proj2 in h.
    assert (h0 := empty_set_is_set).
    apply (in_UnivCl_iff_set ∅) in h0.
    exact (h ∅ h0).
  * intro h. exfalso. exact (empty_set_property x h).
Qed.

Theorem union_empty_set:
  ⋃∅ = ∅.
Proof.
  apply ext. intro x. split.
  * intro h. apply comp in h. exfalso.
    destruct h as (_, (A, (hA, _))).
    exact ((empty_set_property A) hA).
  * intro hx. exfalso.
    exact ((empty_set_property x) hx).
Qed.

Theorem union_UnivCl:
  ⋃UnivCl = UnivCl.
Proof.
  apply ext. intro x. split.
  * intro h. apply comp in h. apply proj2 in h.
    destruct h as (A, (hA, hx)).
    apply (in_UnivCl_iff_set x). exact (set_intro hx).
  * intro h. apply -> comp. split.
    - exact (set_intro h).
    - pose (Px := Power x). exists Px. split.
      -- assert (hPx := power_set x (set_intro h)).
         apply (in_UnivCl_iff_set Px).
         fold Px in hPx. exact hPx.
      -- unfold Px. unfold Power.
         apply -> comp. split.
         --- exact (set_intro h).
         --- exact (subclass_refl x).
Qed.

Theorem power_UnivCl:
  Power UnivCl = UnivCl.
Proof.
  apply ext. intro x. split.
  * intro h. apply comp in h. apply proj1 in h.
    apply -> comp. exact (conj h I).
  * intro h. apply comp in h. apply proj1 in h.
    apply -> comp. split.
    - exact h.
    - unfold Subclass. intros u hu.
      apply -> comp. exact (conj (set_intro hu) I).
Qed.

(* Basic results about singletons, pair sets and pairs *)
(* =================================================== *)

Theorem intersection_sg x:
  set x → ⋂(SgSet x) = x.
Proof.
  intro hsx. apply ext. intro u. split.
  * intro h. apply comp in h. apply proj2 in h.
    apply (h x). clear h u. apply -> comp. split.
    - exact hsx.
    - intros _. reflexivity.
  * intro h. apply -> comp. split.
    - exact (set_intro h).
    - intros x' hx'. apply comp in hx'.
      apply proj2 in hx'.
      rewrite (hx' hsx). exact h.
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

Lemma pair_set_intro u x y:
  set x → set y → u = x ∨ u = y → u ∈ PairSet x y.
Proof.
  intros hx hy h. apply -> comp.
  destruct h as [hl | hr].
  * split.
    - rewrite hl. exact hx.
    - left. intros _. exact hl.
  * split.
    - rewrite hr. exact hy.
    - right. intros _. exact hr.
Qed.

Lemma pair_set_elim u x y:
  set x → set y → u ∈ PairSet x y → u = x ∨ u = y.
Proof.
  intros hx hy h. apply comp in h. apply proj2 in h.
  destruct h as [hl | hr].
  * left.  exact (hl hx).
  * right. exact (hr hy).
Qed.

Lemma sg_intro u x:
  set x → u = x → u ∈ SgSet x.
Proof.
  intro hx. intro h. apply -> comp. split.
  * rewrite h. exact hx.
  * intros _. exact h.
Qed.

Lemma sg_elim u x:
  set x → u ∈ SgSet x → u = x.
Proof.
  intros hx h. apply comp in h. apply proj2 in h.
  exact (h hx).
Qed.

Theorem sg_eq_pair_set x y:
  set x → set y → SgSet x = PairSet x y → x = y.
Proof.
  intros hsx hsy h.
  assert (hy: y ∈ PairSet x y). {
    apply (pair_set_intro y x y hsx hsy).
    right. reflexivity.
  }
  rewrite <- h in hy.
  apply (sg_elim y x hsx) in hy.
  apply eq_sym in hy. exact hy.
Qed.

Theorem pair_set_diff_singleton x y: set x → set y →
  x ≠ y → (PairSet x y) \ (SgSet x) = (SgSet y).
Proof.
  intros hsx hsy hxy. apply ext. intro u. split.
  * intro h. apply (sg_intro u y hsy).
    apply difference_elim in h.
    destruct h as (hu, hun).
    apply (pair_set_elim u x y hsx hsy) in hu.
    destruct hu as [hx | hy].
    - exfalso.
      assert (h0: u ∈ SgSet x). {
        apply (sg_intro u x hsx). exact hx.
      }
      exact (hun h0).
    - exact hy.
  * intro h. apply (sg_elim u y hsy) in h.
    apply -> comp. repeat split.
    - rewrite h. exact hsy.
    - apply (pair_set_intro u x y hsx hsy).
      right. exact h.
    - intro hu. apply (sg_elim u x hsx) in hu.
      rewrite hu in h. exact (hxy h).
Qed.

Theorem union_pair x y:
  set x → set y → ⋃(x, y) = PairSet x y.
Proof.
  intros hsx hsy. apply ext. intro u.
  assert (hsxx := sg_is_set x hsx).
  assert (hsxy := pair_set x y (conj hsx hsy)).
  split.
  * intro h. apply (pair_set_intro u x y hsx hsy).
    apply comp in h. apply proj2 in h.
    destruct h as (A, (hA, hu)).
    unfold Pair in hA.
    apply (pair_set_elim A _ _ hsxx hsxy) in hA.
    destruct hA as [hx | hy].
    - rewrite hx in hu.
      apply (sg_elim u x hsx )in hu.
      left. exact hu.
    - rewrite hy in hu.
      apply (pair_set_elim u x y hsx hsy) in hu.
      exact hu.
  * intro h. apply union_intro.
    apply (pair_set_elim u x y hsx hsy) in h.
    destruct h as [hx | hy].
    - exists (SgSet x). split.
      -- unfold Pair.
         apply (pair_set_intro _ _ _ hsxx hsxy).
         left. reflexivity.
      -- apply (sg_intro u x hsx). exact hx.
    - exists (PairSet x y). split.
      -- unfold Pair.
         apply (pair_set_intro _ _ _ hsxx hsxy).
         right. reflexivity.
      -- apply (pair_set_intro u x y hsx hsy).
         right. exact hy.
Qed.

Lemma intersection_pair_set A B:
  set A → set B → ⋂(PairSet A B) = A ∩ B.
Proof.
  intros hsA hsB. apply ext. intro x. split.
  * intro h. assert (hq := intersection_elim h).
    apply intersection2_intro.
    split. 
    - apply (hq A). apply (pair_set_intro A A B hsA hsB).
      left. reflexivity.
    - apply (hq B). apply (pair_set_intro B A B hsA hsB).
      right. reflexivity.
  * intro h. apply intersection2_elim in h.
    destruct h as (hA, hB).
    apply intersection_intro.
    - exact (set_intro hA).
    - intro X. intro hX.
      apply (pair_set_elim X A B hsA hsB) in hX.
      destruct hX as [hXA | hXB].
      -- rewrite hXA. exact hA.
      -- rewrite hXB. exact hB.
Qed.

Lemma union_pair_set A B: set A → set B →
  ⋃(PairSet A B) = A ∪ B.
Proof.
  intros hsA hsB. apply ext. intro x. split.
  * intro h. apply union_elim in h.
    destruct h as (X, (hX, hx)).
    apply (pair_set_elim X A B hsA hsB) in hX.
    apply union2_intro.
    destruct hX as [hXA | hXB].
    - left.  rewrite hXA in hx. exact hx. 
    - right. rewrite hXB in hx. exact hx.
  * intro h. apply union2_elim in h.
    apply union_intro. destruct h as [hA | hB].
    - exists A. split.
      -- apply (pair_set_intro A A B hsA hsB).
         left. reflexivity.
      -- exact hA.
    - exists B. split.
      -- apply (pair_set_intro B A B hsA hsB).
         right. reflexivity.
      -- exact hB.
Qed.

Theorem intersection_pair x y: set x → set y →
  ⋂(x, y) = SgSet x.
Proof.
  intros hsx hsy.
  assert (hsxx := sg_is_set x hsx).
  assert (hsxy := pair_set x y (conj hsx hsy)).
  apply ext. intro u. unfold Pair.
  rewrite (intersection_pair_set _ _ hsxx hsxy).
  split.
  * intro h. apply intersection2_elim in h.
    destruct h as (hx, hy).
    exact hx.
  * intro h. apply (sg_elim u x hsx) in h.
    apply intersection2_intro. rewrite h.
    split.
    - apply (sg_intro x x hsx). reflexivity.
    - apply (pair_set_intro x x y hsx hsy).
      left. reflexivity.
Qed.

Theorem pair_proj1 x y: set x → set y →
  x = ⋃⋂(x, y).
Proof.
  intros hsx hsy.
  rewrite (intersection_pair x y hsx hsy).
  exact (union_sg x hsx).
Qed.

Lemma pair_set_eq_lemma {A B B': Prop}:
  (A ∧ B ↔ A ∧ B') → (A ∨ B ↔ A ∨ B') → (B ↔ B').
Proof.
  tauto.
Qed.

Theorem pair_set_eq x y y': set x → set y → set y' →
  (PairSet x y) = (PairSet x y') → y = y'.
Proof.
  intros hsx hsy hsy'. intro h. apply ext. intro u.
  assert (h1 := f_equal (fun s => ⋂s) h). simpl in h1.
  rewrite (intersection_pair_set x y hsx hsy) in h1.
  rewrite (intersection_pair_set x y' hsx hsy') in h1.
  assert (h2 := f_equal (fun s => ⋃s) h). simpl in h2.
  rewrite (union_pair_set x y hsx hsy) in h2.
  rewrite (union_pair_set x y' hsx hsy') in h2.
  clear h hsx hsy hsy'.
  assert (heq1: u ∈ x ∧ u ∈ y ↔ u ∈ x ∧ u ∈ y'). {
    split.
    * intro h. apply intersection2_elim.
      apply intersection2_intro in h.
      rewrite h1 in h. exact h.
    * intro h. apply intersection2_elim.
      apply intersection2_intro in h.
      rewrite h1. exact h.
  }
  assert (heq2: u ∈ x ∨ u ∈ y ↔ u ∈ x ∨ u ∈ y'). {
    split.
    * intro h. apply union2_elim.
      apply union2_intro in h.
      rewrite h2 in h. exact h.
    * intro h. apply union2_elim.
      apply union2_intro in h.
      rewrite h2. exact h.
  }
  exact (pair_set_eq_lemma heq1 heq2).
Qed.

Theorem pair_eq x y x' y': set x → set y →
  (x, y) = (x', y') ↔ x = x' ∧ y = y'.
Proof.
  intros hsx hsy. split.
  * intro h.
    assert (hset := pair_is_set (conj hsx hsy)).
    rewrite h in hset. apply pair_is_set_rev in hset.
    destruct hset as (hsx', hsy').
    assert (hx := h).
    apply (f_equal (fun u => ⋃⋂u)) in hx.
    rewrite <- (pair_proj1 x y hsx hsy) in hx.
    rewrite <- (pair_proj1 x' y' hsx' hsy') in hx.
    split.
    - exact hx.
    - rewrite <- hx in h. clear hx.
      apply (f_equal (fun u => ⋃u)) in h.
      rewrite (union_pair x y hsx hsy) in h.
      rewrite (union_pair x y' hsx hsy') in h.
      apply (pair_set_eq x y y' hsx hsy hsy') in h.
      exact h.
  * intros (hx, hy). rewrite hx. rewrite hy.
    reflexivity.
Qed.

Lemma prod_elim_term {A B x y}:
  (x, y) ∈ A × B → x ∈ A ∧ y ∈ B.
Proof.
  intros h. apply comp in h. apply proj2 in h.
  destruct h as (x', (y', (hx', (hy', heq)))).
  apply eq_sym in heq.
  assert (hsx' := set_intro hx').
  assert (hsy' := set_intro hy').
  apply (pair_eq x' y' x y hsx' hsy') in heq.
  destruct heq as (hxx', hyy').
  rewrite hxx' in hx'. rewrite hyy' in hy'.
  exact (conj hx' hy').
Qed.

Theorem union2_is_set A B:
  set A → set B → set (A ∪ B).
Proof.
  intros hA hB.
  assert (hAB := pair_set A B (conj hA hB)).
  apply union in hAB.
  rewrite (union_pair_set A B hA hB) in hAB.
  exact hAB.
Qed.

Theorem sg_inj {x y: set x → set y →
  SgSet x = SgSet y → x = y.
Proof.
  intros hsx hsy. intro h.
  apply (f_equal (fun u => ⋃u)) in h.
  rewrite <- (union_sg x hsx) in h.
  rewrite <- (union_sg y hsy) in h.
  exact h.
Qed.
