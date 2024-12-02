
(* Sequent natural deduction for *)
(* classical propositional calculus *)

(* Shown is soundness under classical semantics. *)

Require Import Coq.Unicode.Utf8.
Require Import Coq.Bool.Bool.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Constructive_sets.

Inductive Formula: Set :=
| var: nat → Formula
| falsum: Formula
| conj: Formula → Formula → Formula
| disj: Formula → Formula → Formula
| subj: Formula → Formula → Formula.

Definition neg A := subj A falsum.
Definition bij A B := conj (subj A B) (subj B A).

Fixpoint sat (I: nat → bool) (A: Formula): bool :=
  match A with
  | var a => I a
  | falsum => false
  | conj A B => andb (sat I A) (sat I B)
  | disj A B => orb (sat I A) (sat I B)
  | subj A B => orb (negb (sat I A)) (sat I B)
  end.

Notation "A ∈ Γ" := (In Formula Γ A) (at level 70).
Notation "Γ ⊆ Δ" := (Included Formula Γ Δ) (at level 70).
Notation "Γ ∪ Δ" := (Union Formula Γ Δ) (at level 50).
Notation "{ A ,}" := (Singleton Formula A) (at level 0).

Definition sat_all (I: nat → bool) (Γ: Ensemble Formula) :=
  ∀A, A ∈ Γ → sat I A = true.

Definition valid Γ A: Prop :=
  ∀(I: nat → bool), sat_all I Γ → sat I A = true.

Declare Scope formula_scope.
Bind Scope formula_scope with Formula.

Notation "⊥" := falsum (at level 0).
Notation "¬ A" := (neg A): formula_scope.
Notation "A ∧ B" := (conj A B): formula_scope.
Notation "A ∨ B" := (disj A B): formula_scope.
Notation "A → B" := (subj A B): formula_scope.
Notation "Γ ⊨ A" := (valid Γ A) (at level 100).

Inductive Formulas: Set :=
| nil: Formulas
| cons: Formulas → Formula → Formulas.

Inductive Prf: Formulas → Formula → Set :=
| basic_sequent: forall A, Prf (cons nil A) A
| weakening Γ A B: Prf Γ B → Prf (cons Γ A) B
| conj_intro Γ A B: Prf Γ A → Prf Γ B → Prf Γ (A ∧ B)
| conj_eliml Γ A B: Prf Γ (A ∧ B) → Prf Γ A
| conj_elimr Γ A B: Prf Γ (A ∧ B) → Prf Γ B
| disj_introl Γ A B: Prf Γ A → Prf Γ (A ∨ B)
| disj_intror Γ A B: Prf Γ B → Prf Γ (A ∨ B)
| disj_elim Γ A B C: Prf Γ (A ∨ B) →
  Prf (cons Γ A) C → Prf (cons Γ B) C → Prf Γ C
| subj_intro Γ A B: Prf (cons Γ A) B → Prf Γ (A → B)
| subj_elim Γ A B: Prf Γ (A → B) → Prf Γ A → Prf Γ B
| dne Γ A: Prf Γ (¬¬A) → Prf Γ A.

Fixpoint as_set (Γ: Formulas): Ensemble Formula :=
  match Γ with
  | nil => Empty_set Formula
  | cons Γ A => Add Formula (as_set Γ) A
  end.

Definition provable Γ A: Prop :=
  ∃Γ0, (as_set Γ0) ⊆ Γ ∧ ∃p: Prf Γ0 A, True.
Notation "Γ ⊢ A" := (provable Γ A) (at level 100).

Theorem weakening_is_valid Γ A B:
  (Γ ⊨ B) → (Γ ∪ {A,} ⊨ B).
Proof.
  intro h. unfold valid. intro I. intro hI.
  unfold valid in h. apply h. clear h.
  unfold sat_all. intro X. intro hX.
  unfold sat_all in hI. apply hI. clear hI.
  apply Union_introl. exact hX.
Qed.

Theorem conj_intro_is_valid Γ A B:
  (Γ ⊨ A) → (Γ ⊨ B) → (Γ ⊨ A ∧ B).
Proof.
  intros h1 h2. unfold valid. intro I. intro hI.
  unfold valid in h1. unfold valid in h2.
  simpl. apply andb_true_intro. split.
  * apply h1. exact hI.
  * apply h2. exact hI.
Qed.

Theorem conj_eliml_is_valid Γ A B:
  (Γ ⊨ A ∧ B) → (Γ ⊨ A).
Proof.
  intro h. unfold valid. intro I. intro hI.
  unfold valid in h.
  assert (h := h I hI). clear hI.
  simpl in h. apply andb_prop in h.
  exact (proj1 h).
Qed.

Theorem conj_elimr_is_valid Γ A B:
  (Γ ⊨ A ∧ B) → (Γ ⊨ B).
Proof.
  intro h. unfold valid. intro I. intro hI.
  unfold valid in h.
  assert (h := h I hI). clear hI.
  simpl in h. apply andb_prop in h.
  exact (proj2 h).
Qed.

Theorem disj_introl_is_valid Γ A B:
  (Γ ⊨ A) → (Γ ⊨ A ∨ B).
Proof.
  intro h. unfold valid. intro I. intro hI.
  simpl sat. apply orb_true_iff. left.
  unfold valid in h. apply h. exact hI.
Qed.

Theorem disj_intror_is_valid Γ A B:
  (Γ ⊨ B) → (Γ ⊨ A ∨ B).
Proof.
  intro h. unfold valid. intro I. intro hI.
  simpl sat. apply orb_true_iff. right.
  unfold valid in h. apply h. exact hI.
Qed.

Theorem sat_singleton I A:
  sat I A = true → sat_all I {A,}.
Proof.
  intro h. unfold sat_all. intro X. intro hX.
  apply Singleton_inv in hX. rewrite <- hX.
  exact h.
Qed.

Theorem sat_union I Γ Δ:
  sat_all I Γ → sat_all I Δ → sat_all I (Γ ∪ Δ).
Proof.
  intros h1 h2. unfold sat_all. intro A. intro hA.
  unfold sat_all in h1. unfold sat_all in h2.
  apply Union_inv in hA. destruct hA as [hl | hr].
  * apply h1. exact hl.
  * apply h2. exact hr.
Qed.

Theorem as_set_cons Γ A:
  as_set (cons Γ A) = as_set Γ ∪ {A,}.
Proof.
  revert A.
  induction Γ as [| Γ ih B].
  * intro A. simpl. unfold Add. reflexivity.
  * intro A. rewrite (ih B). simpl. unfold Add.
    reflexivity.
Qed.
 (* Alternatively:
    intro A. simpl. unfold Add. rewrite <- (ih B).
    reflexivity. *)

Theorem disj_elim_is_valid Γ A B C:
  (Γ ⊨ A ∨ B) → (Γ ∪ {A,} ⊨ C) → (Γ ∪ {B,} ⊨ C) → (Γ ⊨ C).
Proof.
  intros h1 h2 h3. unfold valid. intro I. intro hI.
  unfold valid in h1. unfold valid in h2. unfold valid in h3.
  assert (h1 := h1 I hI). simpl sat in h1.
  apply orb_true_iff in h1. destruct h1 as [hl | hr].
  * apply h2. apply sat_union.
    - exact hI.
    - apply sat_singleton. exact hl.
  * apply h3. apply sat_union.
    - exact hI.
    - apply sat_singleton. exact hr.
Qed.

Theorem impl_from_bool (a b: bool):
  (a = true → b = true) → negb a || b = true.
Proof.
  intro h. apply orb_true_iff.
  induction a.
  * right. apply h. reflexivity.
  * left. apply negb_true_iff. reflexivity.
Qed.

Theorem subj_intro_is_valid Γ A B:
  (Γ ∪ {A,} ⊨ B) → (Γ ⊨ A → B).
Proof.
  intro h. unfold valid. intro I. intro hI.
  unfold valid in h. simpl sat.
  apply impl_from_bool. intro hIA.
  apply h. clear h. apply sat_union.
  * exact hI.
  * apply sat_singleton. exact hIA.
Qed.

Theorem subj_elim_is_valid Γ A B:
  (Γ ⊨ A → B) → (Γ ⊨ A) → (Γ ⊨ B).
Proof.
  intros h1 h2. unfold valid. intro I. intro hI.
  unfold valid in h1. unfold valid in h2.
  assert (h1 := h1 I hI).
  assert (h2 := h2 I hI). clear hI.
  simpl sat in h1. apply orb_true_iff in h1.
  destruct h1 as [hl | hr].
  * apply negb_true_iff in hl.
    exfalso. exact (eq_true_false_abs _ h2 hl).
  * exact hr.
Qed.

Theorem dne_is_valid Γ A:
  (Γ ⊨ ¬¬A) → (Γ ⊨ A).
Proof.
  intro h. unfold valid. intro I. intro hI.
  unfold valid in h. assert (h := h I hI). clear hI.
  unfold neg in h. simpl sat in h.
  rewrite orb_false_r in h. rewrite orb_false_r in h.
  apply negb_true_iff in h. apply negb_false_iff in h.
  exact h.
Qed.

Theorem soundness_lemma Γ A:
  (∃p: Prf Γ A, True) → (as_set Γ ⊨ A).
Proof.
  intro h. destruct h as (p, _).
  induction p as [
  | Γ A B _ ih
  | Γ A B _ ihA _ ihB
  | Γ A B _ ih
  | Γ A B _ ih
  | Γ A B _ ihA
  | Γ A B _ ihB
  | Γ A B C _ ihAB _ ihA _ ihB
  | Γ A B _ ih
  | Γ A B _ ih1 _ ih2
  | Γ A _ ih].
  * unfold valid. intros I hI. unfold sat_all in hI.
    apply hI. simpl. unfold Add.
    apply Union_intror. apply In_singleton.
  * rewrite as_set_cons.
    exact (weakening_is_valid (as_set Γ) A B ih).
  * exact (conj_intro_is_valid (as_set Γ) A B ihA ihB).
  * exact (conj_eliml_is_valid (as_set Γ) A B ih).
  * exact (conj_elimr_is_valid (as_set Γ) A B ih).
  * exact (disj_introl_is_valid (as_set Γ) A B ihA).
  * exact (disj_intror_is_valid (as_set Γ) A B ihB).
  * rewrite as_set_cons in ihA.
    rewrite as_set_cons in ihB.
    exact (disj_elim_is_valid (as_set Γ) A B C ihAB ihA ihB).
  * rewrite as_set_cons in ih.
    exact (subj_intro_is_valid (as_set Γ) A B ih).
  * exact (subj_elim_is_valid (as_set Γ) A B ih1 ih2).
  * exact (dne_is_valid (as_set Γ) A ih).
Qed.

Theorem sat_set_lemma I Γ Δ:
  Γ ⊆ Δ → (sat_all I Δ) → (sat_all I Γ).
Proof.
  intros h hI. unfold sat_all. intros A hA.
  unfold sat_all in hI. apply hI. apply h.
  exact hA.
Qed.

Theorem natural_deduction_is_sound Γ A:
  (Γ ⊢ A) → (Γ ⊨ A).
Proof.
  intro h. unfold provable in h.
  destruct h as (Γ0, (h0, (p, _))).
  assert (h_valid: as_set Γ0 ⊨ A). {
    apply soundness_lemma. exists p. trivial.
  }
  unfold valid. intros I hI. apply h_valid.
  exact (sat_set_lemma I (as_set Γ0) Γ h0 hI).
Qed.
