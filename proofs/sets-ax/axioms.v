
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

Definition subclass (A B: Class) :=
  ∀x, x ∈ A → x ∈ B.

Definition EmptySet :=
  {x | False}.

Definition SgSet a :=
  {x | set a → x = a}.

Definition PairSet a b :=
  {x | (set a → x = a) ∨ (set b → x = b)}.

Definition Pair x y :=
  (PairSet (SgSet x) (PairSet x y)).

Notation "A ⊆ B" := (subclass A B) (at level 70): class_scope.
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
Notation "⋂ M" := (Intersection M) (at level 0, M at level 30): class_scope.
Notation "⋃ M" := (Union M) (at level 0, M at level 30): class_scope.

Definition projl t := ⋃⋂t.
Definition projr t := ⋂⋃t ∪ (⋃⋃t \ ⋃⋂t).

Definition img R X :=
  {y | ∃x, x ∈ X ∧ (x, y) ∈ R}.

Definition inv_img R Y :=
  {x | ∃y, y ∈ Y ∧ (x, y) ∈ R}.

Definition inv R :=
  {t | ∃y x, t = (y, x) ∧ (x, y) ∈ R}.

Definition left_total X f :=
  ∀x, x ∈ X → ∃y, (x, y) ∈ f.

Definition right_uniq f :=
  ∀x y y', (x, y) ∈ f → (x, y') ∈ f → y = y'.

Definition mapping f X Y :=
  f ⊆ X × Y ∧ left_total X f ∧ right_uniq f.

Definition app f x :=
  ⋂{y | (x, y) ∈ f}.

Definition dom f :=
  {x | ∃y, (x, y) ∈ f}.

Definition rng f :=
  {y | ∃x, (x, y) ∈ f}.

Definition restr f A :=
  {t | t ∈ f ∧ ∃x y, x ∈ A ∧ t = (x, y)}.

Definition is_mapping f :=
  left_total (dom f) f ∧ right_uniq f.

Definition inj X f := ∀x x', x ∈ X → x' ∈ X →
  app f x = app f x' → x = x'.

Definition sur Y f :=
  ∀y, y ∈ Y → ∃x, (x, y) ∈ f.

Definition bij X Y f :=
  inj X f ∧ sur Y f.

Definition succ n := n ∪ (SgSet n).
Definition InductiveSets :=
  {A | ∅ ∈ A ∧ (∀n, n ∈ A → succ n ∈ A)}.
Definition ℕ := ⋂InductiveSets.

Axiom LEM:
  ∀(A: Prop), A ∨ ¬A.

Axiom comp: ∀P: Class → Prop,
  ∀x, x ∈ {u | P u} ↔ set x ∧ P x.

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

Axiom replacement: ∀X Y f A, mapping f X Y →
  A ⊆ X → set A → set (img f A).

Definition non_empty A := ∃x, x ∈ A.

Theorem DNE:
  ∀(A: Prop), ¬¬A → A.
Proof.
  intro A. intro h.
  destruct (LEM A) as [hl | hr].
  * exact hl.
  * exfalso. exact (h hr).
Qed.

Lemma ext_rev {A B}:
  A = B → ∀x, x ∈ A ↔ x ∈ B.
Proof.
  intro h. intro x. rewrite h. split.
  * intro hx. exact hx.
  * intro hx. exact hx.
Qed.

Lemma comp_elim {P: Class → Prop}:
  ∀x, x ∈ {u | P u} → P x.
Proof.
  intros x h. apply comp in h. exact (proj2 h).
Qed.

Lemma set_intro {x A}:
  x ∈ A → set x.
Proof.
  intro h. unfold set. exists A. exact h.
Qed.

Lemma empty_set_property {x}:
  x ∉ ∅.
Proof.
  intro h. apply comp_elim in h. exact h.
Qed.

Theorem non_empty_from_ex {A}:
  (∃x, x ∈ A) → A ≠ ∅.
Proof.
  intro h. destruct h as (x, hx).
  intro hcontra. rewrite hcontra in hx.
  apply (empty_set_property hx).
Qed.

Theorem subclass1_pair_set x y:
  (SgSet x) ⊆ (PairSet x y).
Proof.
  unfold subclass. intros u.
  intro h. apply comp. split.
  * exact (set_intro h).
  * left. apply comp_elim in h. exact h.
Qed.

Theorem subclass2_pair_set x y:
  (SgSet y) ⊆ (PairSet x y).
Proof.
  unfold subclass. intros u.
  intro h. apply comp. split.
  * exact (set_intro h).
  * right. apply comp_elim in h. exact h.
Qed.

Theorem pair_set_self x:
  set x → (PairSet x x) = (SgSet x).
Proof.
  intro hx. apply ext. intro u. split.
  * intro h. apply comp in h.
    destruct h as (hu, hux).
    apply comp. split.
    - exact hu.
    - destruct hux as [hl | hr].
      -- intros _. exact (hl hx).
      -- intros _. exact (hr hx).
  * intro h. apply comp in h.
    destruct h as (hu, hux).
    apply comp. split.
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
  unfold subclass. intro x. intro hx.
  apply comp_elim in hx. exact (proj1 hx).
Qed.

Theorem non_empty_class A:
  A ≠ ∅ → ∃x, x ∈ A.
Proof.
  intro h. apply DNE. intro hn.
  assert (hn': ∀x, x ∉ A). {
    intros x hx. apply hn. exists x. exact hx.
  }
  assert (h0: A = ∅). {
    apply ext. intro x. split.
    * intro hx. exfalso. exact (hn' x hx).
    * intro hx. exfalso. exact (empty_set_property hx).
  }
  exact (h h0).
Qed.

Theorem intersection_is_set M:
  M ≠ ∅ → set (⋂M).
Proof.
  intro hM. apply non_empty_class in hM.
  destruct hM as (A, hA).
  apply (subset _ A (set_intro hA)).
  unfold subclass. intros x hx.
  apply comp_elim in hx. exact (hx A hA).
Qed.

Theorem difference_is_set {A B}:
  set A → set (A \ B).
Proof.
  assert (h: A \ B ⊆ A). {
    unfold subclass. intros x hx.
    apply comp_elim in hx.
    exact (proj1 hx).
  }
  intro hA. exact (subset _ A hA h).
Qed.


(* Basic lemmas and theorems *)
(* ========================= *)

Theorem subclass_refl A:
  A ⊆ A.
Proof.
  unfold subclass. intro x. intro h. exact h.
Qed.

Theorem subclass_antisym {A B}:
  A ⊆ B ∧ B ⊆ A → A = B.
Proof.
  intros (hAB, hBA). apply ext. intro x. split.
  * intro h. unfold subclass in hAB. exact (hAB x h).
  * intro h. unfold subclass in hBA. exact (hBA x h).
Qed.

Theorem subclass_trans {A B C}:
  A ⊆ B ∧ B ⊆ C → A ⊆ C.
Proof.
  intros (hAB, hBC). unfold subclass.
  intro x. intro h.
  unfold subclass in hAB.
  unfold subclass in hBC.
  exact (hBC x (hAB x h)).
Qed.

Theorem subclass_from_eq {A B}:
  A = B → A ⊆ B.
Proof.
  intro heq. assert (h := subclass_refl A).
  symmetry in heq. rewrite heq. exact h.
Qed.

Lemma intersection2_intro {A B x}:
  x ∈ A ∧ x ∈ B → x ∈ A ∩ B.
Proof.
  intro h. apply comp. split.
  * unfold set. exists A. exact (proj1 h).
  * exact h.
Qed.

Lemma intersection2_elim {A B x}:
  x ∈ A ∩ B → x ∈ A ∧ x ∈ B.
Proof.
  intro h. apply comp_elim in h. exact h.
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
  intro h. apply comp. split.
  * unfold set. destruct h as [hA | hB].
    - exists A. exact hA.
    - exists B. exact hB.
  * exact h.
Qed.

Lemma union2_elim {A B x}:
  x ∈ A ∪ B → x ∈ A ∨ x ∈ B.
Proof.
  intro h. apply comp_elim in h. exact h.
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
  intro h. apply comp. split.
  * unfold set. exists A. exact (proj1 h).
  * exact h.
Qed.

Lemma difference_elim {A B x}:
  x ∈ A \ B → x ∈ A ∧ x ∉ B.
Proof.
  intro h. apply comp_elim in h. exact h.
Qed.

Lemma intersection_intro {M x}:
  set x → (∀A, A ∈ M → x ∈ A) → x ∈ ⋂M.
Proof.
  intros hx h. apply comp. split.
  * exact hx.
  * exact h.
Qed.

Lemma intersection_elim {M x}:
  x ∈ ⋂M → (∀A, A ∈ M → x ∈ A).
Proof.
  intro h. intro A. intro hA.
  apply comp_elim in h. exact (h A hA).
Qed.

Lemma union_intro {M x}:
  (∃A, A ∈ M ∧ x ∈ A) → x ∈ ⋃M.
Proof.
  intro h. destruct h as (A, (hA, hx)).
  apply comp. split.
  * exact (set_intro hx).
  * exists A. exact (conj hA hx).
Qed.

Lemma union_elim {M x}:
  x ∈ ⋃M → (∃A, A ∈ M ∧ x ∈ A).
Proof.
  intro h. apply comp_elim in h. exact h.
Qed.

Lemma prod_intro {A B t}:
  (∃x y, x ∈ A ∧ y ∈ B ∧ t = (x, y)) → t ∈ A × B.
Proof.
  intro h. apply comp. split.
  * destruct h as (x, (y, (hx, (hy, ht)))).
    rewrite ht. apply pair_is_set.
    exact (conj (set_intro hx) (set_intro hy)).
  * exact h.
Qed.

Lemma prod_elim {A B t}:
  t ∈ A × B → (∃x y, x ∈ A ∧ y ∈ B ∧ t = (x, y)).
Proof.
  intro h. apply comp_elim in h. exact h.
Qed.

Lemma prod_intro_term {A B x y}:
  x ∈ A ∧ y ∈ B → (x, y) ∈ A × B.
Proof.
  intros (hx, hy). apply comp.
  split.
  * apply pair_is_set.
    exact (conj (set_intro hx) (set_intro hy)).
  * exists x. exists y.
    exact (conj hx (conj hy (eq_refl (x, y)))).
Qed.

Theorem difference_subclass {A B}:
  A \ B ⊆ A.
Proof.
  unfold subclass. intros x hx.
  apply comp_elim in hx. exact (proj1 hx).
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
    * intro h. unfold R in h at 2.
      apply comp_elim in h. exact h.
    * intro h. unfold R at 2. apply comp.
      exact (conj hR h).
  }
  exact (iff_contra h).
Qed.

Theorem UnivCl_by_eq:
  UnivCl = {x | x = x}.
Proof.
  apply ext. intro x. split.
  * intro h. apply comp in h. destruct h as (h, _).
    apply comp. split.
    - exact h.
    - reflexivity.
  * intro h. apply comp in h. destruct h as (h, _).
    apply comp. split.
    - exact h.
    - exact I.
Qed.

Theorem in_UnivCl_iff_set x:
  x ∈ UnivCl ↔ set x.
Proof.
  split.
  * intro h. apply comp in h. exact (proj1 h).
  * intro h. apply comp. exact (conj h I).
Qed.

Theorem DiagCl_subclass_UnivCl:
  DiagCl ⊆ UnivCl.
Proof.
  unfold subclass. intro x. intro h.
  apply comp in h. apply comp.
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
    apply comp. exact (conj h I).
  * intro h. apply comp in h. apply proj1 in h.
    apply comp.
    exact (conj h (@empty_set_property x)).
Qed.

Theorem UnivCl_extremal A:
  UnivCl ∪ A = UnivCl.
Proof.
  apply ext. split.
  * intro h. apply comp.
    apply comp in h. exact ((conj (proj1 h) I)).
  * intro h. apply comp in h. apply proj1 in h.
    apply comp. split.
    - exact h.
    - left. apply comp. exact (conj h I).
Qed.

Theorem comp_subclass_UnivCl:
  ∀(P: Class → Prop), {x | P x} ⊆ UnivCl.
Proof.
  intros P. unfold subclass. intros x hx.
  apply comp in hx. apply comp.
  exact (conj (proj1 hx) I).
Qed.

Theorem SgSet_of_proper_class C:
  ¬set C → SgSet C = UnivCl.
Proof.
  intro h. apply ext. intro x. split.
  * intro hx. apply comp in hx.
    apply proj1 in hx.
    apply comp. exact (conj hx I).
  * intro hx. apply comp in hx.
    apply proj1 in hx.
    apply comp. split.
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
    exact (empty_set_property hx).
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
    apply comp. apply proj1 in h.
    exact (conj h I).
  * intro h. apply comp in h. apply proj1 in h.
    apply comp. split.
    - exact h.
    - intros A hA. exfalso.
      exact (empty_set_property hA).
Qed.

Theorem intersection_UnivCl:
  ⋂UnivCl = ∅.
Proof.
  apply ext. intro x. split.
  * intro h. apply comp_elim in h.
    assert (h0 := empty_set_is_set).
    apply (in_UnivCl_iff_set ∅) in h0.
    exact (h ∅ h0).
  * intro h. exfalso. exact (empty_set_property h).
Qed.

Theorem union_empty_set:
  ⋃∅ = ∅.
Proof.
  apply ext. intro x. split.
  * intro h. apply comp in h. exfalso.
    destruct h as (_, (A, (hA, _))).
    exact (empty_set_property hA).
  * intro hx. exfalso.
    exact (empty_set_property hx).
Qed.

Theorem union_UnivCl:
  ⋃UnivCl = UnivCl.
Proof.
  apply ext. intro x. split.
  * intro h. apply comp_elim in h.
    destruct h as (A, (hA, hx)).
    apply (in_UnivCl_iff_set x). exact (set_intro hx).
  * intro h. apply comp. split.
    - exact (set_intro h).
    - pose (Px := Power x). exists Px. split.
      -- assert (hPx := power_set x (set_intro h)).
         apply (in_UnivCl_iff_set Px).
         fold Px in hPx. exact hPx.
      -- unfold Px. unfold Power.
         apply comp. split.
         --- exact (set_intro h).
         --- exact (subclass_refl x).
Qed.

Theorem power_UnivCl:
  Power UnivCl = UnivCl.
Proof.
  apply ext. intro x. split.
  * intro h. apply comp in h. apply proj1 in h.
    apply comp. exact (conj h I).
  * intro h. apply comp in h. apply proj1 in h.
    apply comp. split.
    - exact h.
    - unfold subclass. intros u hu.
      apply comp. exact (conj (set_intro hu) I).
Qed.

(* Basic results about singletons, pair sets and pairs *)
(* =================================================== *)

Theorem intersection_sg x:
  set x → ⋂(SgSet x) = x.
Proof.
  intro hsx. apply ext. intro u. split.
  * intro h. apply comp_elim in h.
    apply (h x). clear h u. apply comp. split.
    - exact hsx.
    - intros _. reflexivity.
  * intro h. apply comp. split.
    - exact (set_intro h).
    - intros x' hx'. apply comp_elim in hx'.
      rewrite (hx' hsx). exact h.
Qed.

Theorem union_sg x:
  set x → x = ⋃(SgSet x).
Proof.
  intro hx. apply ext. intro u. split.
  * intro h. apply comp. split.
    - exact (set_intro h).
    - exists x. split.
      -- apply comp. split.
         --- exact hx.
         --- intros _. reflexivity.
      -- exact h.
  * intro h. apply comp_elim in h.
    destruct h as (x', (hx', hu)).
    apply comp_elim in hx'.
    rewrite (hx' hx) in hu. exact hu.
Qed.

Theorem pair_set_is_union_sg x y:
  (PairSet x y) = (SgSet x) ∪ (SgSet y).
Proof.
  apply ext. intro u. split.
  * intro h. apply union2_intro.
    apply comp in h. destruct h as (hu, h).
    destruct h as [hl | hr].
    - left. apply comp. exact (conj hu hl).
    - right. apply comp. exact (conj hu hr).
  * intro h.  apply comp in h.
    destruct h as (hu, h).
    apply comp. split.
    - exact hu.
    - destruct h as [hl | hr].
      -- apply comp_elim in hl. left. exact hl.
      -- apply comp_elim in hr. right. exact hr.
Qed.

Lemma pair_set_intro u x y:
  set x → set y → u = x ∨ u = y → u ∈ PairSet x y.
Proof.
  intros hx hy h. apply comp.
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
  intros hx hy h. apply comp_elim in h.
  destruct h as [hl | hr].
  * left.  exact (hl hx).
  * right. exact (hr hy).
Qed.

Lemma sg_intro u x:
  set x → u = x → u ∈ SgSet x.
Proof.
  intro hx. intro h. apply comp. split.
  * rewrite h. exact hx.
  * intros _. exact h.
Qed.

Lemma sg_elim u x:
  set x → u ∈ SgSet x → u = x.
Proof.
  intros hx h. apply comp_elim in h.
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
    apply comp. repeat split.
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
    apply comp_elim in h.
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
  x = projl (x, y).
Proof.
  intros hsx hsy. unfold projl.
  rewrite (intersection_pair x y hsx hsy).
  exact (union_sg x hsx).
Qed.

Theorem pair_proj2 x y: set x → set y →
  y = projr (x, y).
Proof.
  intros hsx hsy. unfold projr.
  rewrite (intersection_pair x y hsx hsy).
  rewrite (union_pair x y hsx hsy).
  rewrite (intersection_pair_set x y hsx hsy).
  rewrite (union_pair_set x y hsx hsy).
  rewrite <- (union_sg x hsx).
  apply ext. intro u. split.
  * intro hu. apply union2_intro.
    destruct (LEM (u ∈ x)) as [hl | hr].
    - left. apply intersection2_intro.
      exact (conj hl hu).
    - right. apply difference_intro. split.
      -- apply union2_intro. right. exact hu.
      -- exact hr.
  * intro hu. apply union2_elim in hu.
    destruct hu as [hl | hr].
    - apply intersection2_elim in hl.
      exact (proj2 hl).
    - apply difference_elim in hr.
      destruct hr as (hxy, hnx).
      apply union2_elim in hxy.
      destruct hxy as [hx | hy].
      -- exfalso. exact (hnx hx).
      -- exact hy.
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
    apply (f_equal projl) in hx.
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

Theorem pair_eq_from {X Y x y x' y'}:
  x ∈ X → y ∈ Y →
  (x, y) = (x', y') ↔ x = x' ∧ y = y'.
Proof.
  intros hx hy.
  apply pair_eq.
  * exact (set_intro hx).
  * exact (set_intro hy).
Qed.

Lemma prod_elim_term {A B x y}:
  (x, y) ∈ A × B → x ∈ A ∧ y ∈ B.
Proof.
  intros h. apply comp_elim in h.
  destruct h as (x', (y', (hx', (hy', heq)))).
  apply eq_sym in heq.
  assert (hsx' := set_intro hx').
  assert (hsy' := set_intro hy').
  apply (pair_eq x' y' x y hsx' hsy') in heq.
  destruct heq as (hxx', hyy').
  rewrite hxx' in hx'. rewrite hyy' in hy'.
  exact (conj hx' hy').
Qed.

Theorem sg_inj {x y}: set x → set y →
  SgSet x = SgSet y → x = y.
Proof.
  intros hsx hsy. intro h.
  apply (f_equal (fun u => ⋃u)) in h.
  rewrite <- (union_sg x hsx) in h.
  rewrite <- (union_sg y hsy) in h.
  exact h.
Qed.


(* Further results about set constitution *)
(* ====================================== *)

Theorem union2_is_set A B:
  set A → set B → set (A ∪ B).
Proof.
  intros hA hB.
  assert (hAB := pair_set A B (conj hA hB)).
  apply union in hAB.
  rewrite (union_pair_set A B hA hB) in hAB.
  exact hAB.
Qed.

Theorem prod_is_set {A B}:
  set A → set B → set (A × B).
Proof.
  intros hsA hsB.
  assert (hsub: A × B ⊆ Power (Power (A ∪ B))). {
    unfold subclass. intros t ht.
    apply comp. split.
    * exact (set_intro ht).
    * unfold subclass. intros s hs.
      apply comp. split.
      - exact (set_intro hs).
      - unfold subclass. intros x hx.
        apply union2_intro.
        apply comp_elim in ht.
        destruct ht as (a, (b, (ha, (hb, ht)))).
        rewrite ht in hs. clear ht t.
        unfold Pair in hs. apply comp_elim in hs.
        destruct hs as [hl | hr].
        -- left.
           assert (hl := (hl (sg_is_set a (set_intro ha)))).
           rewrite hl in hx. clear hl.
           apply (sg_elim _ _ (set_intro ha)) in hx.
           rewrite hx. exact ha.
        -- assert (hsa := set_intro ha).
           assert (hsb := set_intro hb).
           assert (hr := (hr (pair_set a b (conj hsa hsb)))).
           rewrite hr in hx. clear hr.
           apply comp_elim in hx.
           destruct hx as [hxa | hxb].
           --- assert (hxa := hxa hsa). left.
               rewrite hxa. exact ha.
           --- assert (hxb := hxb hsb). right.
               rewrite hxb. exact hb.
  }
  assert (hsPP: set (Power (Power (A ∪ B)))). {
    apply power_set. apply power_set.
    exact (union2_is_set A B hsA hsB).
  }
  apply (subset (A × B) (Power (Power (A ∪ B)))).
  * exact hsPP.
  * exact hsub.
Qed.

(* Unique existence and definite description *)
(* ========================================= *)

Definition ex_uniq (P: Class → Prop) :=
  (∃x, P x) ∧ (∀x x', P x ∧ P x' → x = x').
Notation "∃ ! x , t" := (ex_uniq (fun x => t)) (at level 200).

Definition iota P := ⋂{x | P x}.
(* See iota, description operator in
"The Notation in Principia Mathematica" in
"The Stanford Encyclopedia of Philosophy".
https://plato.stanford.edu/entries/pm-notation/
Notation "'ι' x , t" := (iota (fun x => t)) (at level 200).
*)

Theorem iota_property_set {P} x:
  (∃!x, set x ∧ P x) → x = iota P → set x ∧ P x.
Proof.
  intros hP h. unfold ex_uniq in hP.
  destruct hP as ((x0, (hsx0, hx0)), huniq).
  assert (heq: x0 = iota P). {
    apply ext. intro u. split.
    * intro hu. apply comp. split.
      - exact (set_intro hu).
      - intro x1. intro hx1.
        apply comp in hx1.
        assert (heq := huniq x0 x1 (conj (conj hsx0 hx0) hx1)).
        rewrite heq in hu. exact hu.
    * intro hu. apply comp_elim in hu.
      apply (hu x0). apply comp. split.
      - exact hsx0.
      - exact hx0.
  }
  rewrite <- heq in h.
  rewrite h. exact (conj hsx0 hx0).
Qed.

Theorem iota_property {P} x:
  (∃!x, set x ∧ P x) → x = iota P → P x.
Proof.
  intro hP. intro h.
  exact (proj2 (iota_property_set x hP h)).
Qed.

Theorem iota_property_rev {P} x:
  (∃!x, set x ∧ P x) → (set x ∧ P x) → x = iota P.
Proof.
  intros hP hx. apply ext. intro u. split.
  * intro hu. apply comp. split.
    - exact (set_intro hu).
    - intros x0 hx0. apply comp in hx0.
      unfold ex_uniq in hP. apply proj2 in hP.
      rewrite (hP x x0 (conj hx hx0)) in hu.
      exact hu.
  * intro h. apply comp_elim in h.
    apply h. apply comp. exact hx.
Qed.

Theorem comp_rewriting {P Q: Class → Prop}:
  (∀x, P x ↔ Q x) → {x | P x} = {x | Q x}.
Proof.
  intro h. apply ext. intro x. split.
  * intro hx. apply comp in hx as (hsx, hx).
    apply comp. split.
    - exact hsx.
    - exact (proj1 (h x) hx).
  * intro hx. apply comp in hx as (hsx, hx).
    apply comp. split.
    - exact hsx.
    - exact (proj2 (h x) hx).
Qed.

Theorem ex_uniq_equi1 P:
  (∃!x, P x) ↔ (∃x, ∀y, P y ↔ x = y).
Proof.
  split.
  * intro h. unfold ex_uniq in h.
    destruct h as ((x, hx), hxy).
    exists x. intros y. split.
    - intro hy.
      exact (hxy x y (conj hx hy)).
    - intro heq. rewrite heq in hx.
      exact hx.
  * intro h. destruct h as (u, h).
    unfold ex_uniq. split.
    - exists u.
      apply (proj2 (h u)). reflexivity.
    - intros x y (hx, hy).
      apply h in hx. rewrite <- hx.
      apply h in hy. rewrite <- hy.
      reflexivity.
Qed.

Theorem ex_uniq_equi2 P:
  (∃!x, P x) ↔ (∃x, P x ∧ ∀y, P y → x = y).
Proof.
  split.
  * intro h. unfold ex_uniq in h.
    destruct h as ((x, hx), hxy).
    exists x. split.
    - exact hx.
    - intros y hy. exact (hxy x y (conj hx hy)).
  * intro h. destruct h as (u, (hu, h)).
    unfold ex_uniq. split.
    - exists u. exact hu.
    - intros x y (hx, hy).
      apply h in hx. rewrite <- hx.
      apply h in hy. rewrite <- hy.
      reflexivity.
Qed.

(* Similar to what is called Lambert's law in
https://en.wikipedia.org/wiki/Karel_Lambert *)
Theorem ex_uniq_iota_equi {P x}:
  (∃!x, set x ∧ P x) ∧ x = iota P
  ↔ (set x ∧ P x) ∧ ∀y, set y ∧ P y → x = y.
Proof.
  split.
  * intros (h, hiota).
    assert (hx := iota_property_set x h hiota).
    split.
    - exact hx.
    - intros y hy. apply proj2 in h.
      exact (h x y (conj hx hy)).
  * intros (hx, h).
    assert (hex_uniq: ∃!x, set x ∧ P x). {
      split.
      * exists x. exact hx.
      * intros u y (hu, hy).
        apply h in hu. rewrite <- hu.
        apply h in hy. exact hy.
    }
    split.
    - exact hex_uniq.
    - exact (iota_property_rev x hex_uniq hx).
Qed.

Theorem ex_uniq_iota_pred {P Q}:
  (∃!x, set x ∧ P x) ∧ Q (iota P)
  ↔ ∃x, set x ∧ Q x ∧ ∀y, set y ∧ P y ↔ x = y.
Proof.
  split.
  * intros (hP, hQ). set (x := iota P).
    exists x.
    assert (h := iota_property_set x hP (eq_refl x)).
    simpl in h. destruct h as (hsx, hx).
    split; [| split].
    - exact hsx.
    - fold x in hQ. exact hQ.
    - apply proj2 in hP.
      intro y. split.
      -- intro hy.
         exact (hP x y (conj (conj hsx hx) hy)).
      -- intro hxy. rewrite <- hxy.
         exact (conj hsx hx).
  * intro h. destruct h as (x, (hsx, (hx, h))).
    assert (hex_uniq: ∃!x, set x ∧ P x). {
      apply ex_uniq_equi1. exists x. exact h.
    }
    assert (heq: x = iota P). {
      apply iota_property_rev.
      * exact hex_uniq.
      * apply h. reflexivity.
    }
    split.
    - exact hex_uniq.
    - rewrite heq in hx. exact hx.
Qed.

Theorem bounded_uq_union2 A B (P: Class → Prop):
  (∀x, x ∈ A ∪ B → P x) ↔ (∀x, x ∈ A → P x) ∧ (∀x, x ∈ B → P x).
Proof.
  split.
  * intro h. split.
    - intros x hx. apply (h x).
      apply union2_intro. left. exact hx.
    - intros x hx. apply (h x).
      apply union2_intro. right. exact hx.
  * intro h. destruct h as (hA, hB).
    intros x hx. apply union2_elim in hx.
    destruct hx as [hl | hr].
    - exact (hA x hl).
    - exact (hB x hr).
Qed.

