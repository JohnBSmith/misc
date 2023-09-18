
(* Natural deduction for classical propositional calculus *)

(* Shown is soundness under classical semantics. *)
(* Furthermore, some admissible rules are shown. *)

Require Import Coq.Unicode.Utf8.
Require Import Coq.Sets.Constructive_sets.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Sets.Finite_sets_facts.
Require Import Coq.Sets.Powerset_facts.

(* Double negation elimination, *)
(* needed for classical semantics *)
Axiom DNE: ∀A: Prop, ¬¬A → A.

(* The type of atomic variables *)
Inductive Var := var: nat → Var.

(* Recursive definition of the type of *)
(* well-formed logical formulas *)
Inductive Formula: Set :=
| Atom: Var → Formula
| FF: Formula
| TF: Formula
| Neg: Formula → Formula
| Conj: Formula → Formula → Formula
| Disj: Formula → Formula → Formula
| Impl: Formula →  Formula → Formula.

(* Satisfaction relation *)
Fixpoint sat (I: Var → Prop) (A: Formula) :=
  match A with
  | Atom v => I v
  | FF => False
  | TF => True
  | Neg A => ¬sat I A
  | Conj A B => sat I A ∧ sat I B
  | Disj A B => sat I A ∨ sat I B
  | Impl A B => sat I A → sat I B
  end.

Notation "∅" := (Empty_set Formula) (at level 0).
Notation "A ∈ Γ" := (In Formula Γ A) (at level 70).
Notation "{ A ,}" := (Singleton Formula A) (at level 0).
Notation "Γ ∪ Δ" := (Union Formula Γ Δ) (at level 50).

Definition tautology (A: Formula) :=
  ∀I, sat I A.

Definition sat_set (I: Var → Prop) (Γ: Ensemble Formula) :=
  ∀X, X ∈ Γ → sat I X.

Definition valid Γ A :=
  ∀I, sat_set I Γ → sat I A.

Declare Scope formula_scope.
Bind Scope formula_scope with Formula.

Notation "⊥" := FF (at level 0).
Notation "¬ A" := (Neg A): formula_scope.
Notation "A ∧ B" := (Conj A B): formula_scope.
Notation "A ∨ B" := (Disj A B): formula_scope.
Notation "A → B" := (Impl A B): formula_scope.

Notation "⊨ A" := (tautology A) (at level 100).
Notation "Γ ⊨ A" := (valid Γ A) (at level 100).

Theorem sat_union_sg {I Γ A}:
  sat_set I Γ → sat I A → sat_set I (Γ ∪ {A,}).
Proof.
  intros hI hIA. unfold sat_set. intros X hX.
  apply Union_inv in hX. destruct hX as [hl | hr].
  * unfold sat_set in hI. apply hI. exact hl.
  * apply Singleton_inv in hr. subst X. exact hIA.
Qed.

Theorem valid_empty_is_tautology (A: Formula):
  (∅ ⊨ A) ↔ (⊨ A).
Proof.
  split.
  * intro h. unfold tautology. intro I.
    unfold valid in h. apply h.
    unfold sat_set. intros X hX.
    destruct hX.
  * intro h. unfold tautology in h.
    unfold valid. intro I. intro h0. clear h0.
    exact (h I).
Qed.

Lemma basic_seq_intro_is_sound A:
  {A,} ⊨ A.
Proof.
  unfold valid. intro I. intro h.
  unfold sat_set in h. apply h.
  apply Singleton_intro. reflexivity.
Qed.

Lemma weakening_is_sound Γ A B:
  (Γ ⊨ B) → (Γ ∪ {A,} ⊨ B).
Proof.
  intro h. unfold valid. intro I. intro hI.
  unfold sat_set in hI. unfold valid in h.
  apply h. unfold sat_set. intros X hX.
  apply hI. apply Union_introl. exact hX.
Qed.

Lemma conj_intro_is_sound Γ A B:
  (Γ ⊨ A) → (Γ ⊨ B) → (Γ ⊨ A ∧ B).
Proof.
  intros hA hB. unfold valid.
  intro I. intro hI. simpl sat.
  unfold valid in hA.
  unfold valid in hB.
  assert (hIA := hA I hI). clear hA.
  assert (hIB := hB I hI). clear hB.
  exact (conj hIA hIB).
Qed.

Lemma conj_eliml_is_sound Γ A B:
  (Γ ⊨ A ∧ B) → (Γ ⊨ A).
Proof.
  intro h. unfold valid. intro I. intro hI.
  unfold valid in h. apply (h I) in hI. clear h.
  simpl sat in hI. exact (proj1 hI).
Qed.

Lemma conj_elimr_is_sound Γ A B:
  (Γ ⊨ A ∧ B) → (Γ ⊨ B).
Proof.
  intro h. unfold valid. intro I. intro hI.
  unfold valid in h. apply (h I) in hI. clear h.
  simpl sat in hI. exact (proj2 hI).
Qed.

Lemma disj_introl_is_sound Γ A B:
  (Γ ⊨ A) → (Γ ⊨ A ∨ B).
Proof.
  intro h. unfold valid. intro I. intro hI.
  unfold valid in h. apply (h I) in hI. clear h.
  simpl sat. left. exact hI.
Qed.

Lemma disj_intror_is_sound Γ A B:
  (Γ ⊨ B) → (Γ ⊨ A ∨ B).
Proof.
  intro h. unfold valid. intro I. intro hI.
  unfold valid in h. apply (h I) in hI. clear h.
  simpl sat. right. exact hI.
Qed.

Lemma disj_elim_is_sound Γ A B C:
  (Γ ⊨ A ∨ B) → (Γ ∪ {A,} ⊨ C) → (Γ ∪ {B,} ⊨ C) → (Γ ⊨ C).
Proof.
  intros hAB hA hB. unfold valid. intro I. intro hI.
  unfold valid in hAB. assert (hIAB := hAB I hI). clear hAB.
  simpl sat in hIAB. destruct hIAB as [hIA | hIB].
  * unfold valid in hA. apply hA.
    exact (sat_union_sg hI hIA).
  * unfold valid in hB. apply hB.
    exact (sat_union_sg hI hIB).
Qed.

Lemma impl_intro_is_sound Γ A B:
  (Γ ∪ {A,} ⊨ B) → (Γ ⊨ A → B).
Proof.
  intro h. unfold valid. intro I. intro hI.
  simpl sat. intro hIA.
  unfold valid in h. apply h.
  exact (sat_union_sg hI hIA).
Qed.

Lemma impl_elim_is_sound Γ A B:
  (Γ ⊨ A → B) → (Γ ⊨ A) → (Γ ⊨ B).
Proof.
  intros hAB hA. unfold valid. intro I. intro hI.
  unfold valid in hAB. assert (h := hAB I hI). clear hAB.
  simpl sat in h. unfold valid in hA.
  exact (h (hA I hI)).
Qed.

Lemma neg_intro_is_sound Γ A:
  (Γ ∪ {A,} ⊨ ⊥) → (Γ ⊨ ¬A).
Proof.
  intro h. unfold valid. intro I. intro hI.
  simpl sat. intro hIA. unfold valid in h.
  simpl sat in h. apply (h I).
  exact (sat_union_sg hI hIA).
Qed.

Lemma neg_elim_is_sound Γ A:
  (Γ ⊨ ¬A) → (Γ ⊨ A) → (Γ ⊨ ⊥).
Proof.
  intros hnA hA. unfold valid. intro I. intro hI.
  simpl sat. unfold valid in hnA. unfold valid in hA.
  assert (hInA := hnA I hI). clear hnA.
  assert (hIA := hA I hI). clear hA.
  simpl sat in hInA. exact (hInA hIA).
Qed.

Lemma dne_is_sound Γ A:
  (Γ ⊨ ¬¬A) → (Γ ⊨ A).
Proof.
  intro h. unfold valid. intro I. intro hI.
  apply DNE. unfold valid in h. simpl sat in h.
  apply (h I). exact hI.
Qed.

Inductive Prf: Ensemble Formula → Formula → Prop :=
| basic_seq_intro: ∀A, Prf {A,} A
| weakening: ∀Γ A B,
    Prf Γ B → Prf (Γ ∪ {A,}) B
| conj_intro: ∀Γ A B,
    Prf Γ A → Prf Γ B → Prf Γ (A ∧ B)
| conj_eliml: ∀Γ A B,
    Prf Γ (A ∧ B) → Prf Γ A
| conj_elimr: ∀Γ A B,
    Prf Γ (A ∧ B) → Prf Γ B
| disj_introl: ∀Γ A B,
    Prf Γ A → Prf Γ (A ∨ B)
| disj_intror: ∀Γ A B,
    Prf Γ B → Prf Γ (A ∨ B)
| disj_elim: ∀Γ A B C,
    Prf Γ (A ∨ B) → Prf (Γ ∪ {A,}) C →
    Prf (Γ ∪ {B,}) C → Prf Γ C
| impl_intro: ∀Γ A B,
    Prf (Γ ∪ {A,}) B → Prf Γ (A → B)
| impl_elim: ∀Γ A B,
    Prf Γ (A → B) → Prf Γ A → Prf Γ B
| neg_intro: ∀Γ A,
    Prf (Γ ∪ {A,}) ⊥ → Prf Γ (¬A)
| neg_elim: ∀Γ A,
    Prf Γ (¬A) → Prf Γ A → Prf Γ ⊥
| dne: ∀Γ A,
    Prf Γ (¬¬A) → Prf Γ A.

Notation "Γ ⊢ A" := (Prf Γ A) (at level 100).

Theorem soundness_of_natural_deduction:
  ∀Γ A, (Γ ⊢ A) → (Γ ⊨ A).
Proof.
  intros Γ A. intro h. induction h as [A
  | Γ A B pi hpi
  | Γ A B piA hpiA piB hpiB
  | Γ A B pi hpi
  | Γ A B pi hpi
  | Γ A B pi hpi
  | Γ A B pi hpi
  | Γ A B C pi hpi piA hpiA piB hpiB
  | Γ A B pi hpi
  | Γ A B piAB hpiAB piA hpiA
  | Γ A pi hpi
  | Γ A pinA hpinA piA hpiA
  | Γ A pi hpi].
  * exact (basic_seq_intro_is_sound A).
  * exact (weakening_is_sound Γ A B hpi).
  * exact (conj_intro_is_sound Γ A B hpiA hpiB).
  * exact (conj_eliml_is_sound Γ A B hpi).
  * exact (conj_elimr_is_sound Γ A B hpi).
  * exact (disj_introl_is_sound Γ A B hpi).
  * exact (disj_intror_is_sound Γ A B hpi).
  * exact (disj_elim_is_sound Γ A B C hpi hpiA hpiB).
  * exact (impl_intro_is_sound Γ A B hpi).
  * exact (impl_elim_is_sound Γ A B hpiAB hpiA).
  * exact (neg_intro_is_sound Γ A hpi).
  * exact (neg_elim_is_sound Γ A hpinA hpiA).
  * exact (dne_is_sound Γ A hpi).
Qed.

(* Basic admissible rules *)

Theorem empty_set_neutral Γ:
  Γ ∪ ∅ = Γ.
Proof.
  exact (Empty_set_zero_right Formula Γ).
Qed.

Theorem union_add_assoc Γ Γ' B:
  Γ ∪ Add Formula Γ' B = (Γ ∪ Γ') ∪ {B,}.
Proof.
  apply Extensionality_Ensembles. unfold Same_set.
  split.
  * unfold Included. intros A hA.
    apply Union_inv in hA. destruct hA as [hl | hr].
    - apply Union_introl. apply Union_introl.
      exact hl.
    - apply Add_inv in hr. destruct hr as [hl | hr].
      -- apply Union_introl. apply Union_intror.
         exact hl.
      -- apply Union_intror. apply Singleton_intro.
         exact hr.
  * unfold Included. intros A hA.
    apply Union_inv in hA. destruct hA as [hl | hr].
    - apply Union_inv in hl. destruct hl as [hl | hr].
      -- apply Union_introl. exact hl.
      -- apply Union_intror. apply Add_intro1. exact hr.
    - apply Union_intror. apply Singleton_inv in hr.
      subst B. apply Add_intro2.
Qed.

Theorem weakening_general {Γ Γ' A}:
  Finite Formula Γ' → (Γ ⊢ A) → (Γ ∪ Γ' ⊢ A).
Proof.
  intros hfinite h.
  induction hfinite as [| Γ' hfinite ih B hB].
  * rewrite empty_set_neutral. exact h.
  * rewrite union_add_assoc.
    apply weakening. exact ih.
Qed.

Theorem finite_union {Γ Δ}:
  Finite Formula (Γ ∪ Δ) → Finite Formula Γ.
Proof.
  intro h.
  apply (Finite_downward_closed _ (Γ ∪ Δ) h).
  unfold Included. intros A hA.
  apply Union_introl. exact hA.
Qed.

Theorem context_is_finite {Γ A}:
  (Γ ⊢ A) → Finite Formula Γ.
Proof.
  intro h. induction h as [A
  | Γ A B _ ih
  | Γ A B _ ih _ _
  | Γ A B _ ih
  | Γ A B _ ih
  | Γ A B _ ih
  | Γ A B _ ih
  | Γ A B C _ ih _ _ _ _
  | Γ A B _ ih
  | Γ A B _ ih _ _
  | Γ A _ ih
  | Γ A _ ih _ _
  | Γ A _ ih].
  * apply Singleton_is_finite.
  * apply Union_preserves_Finite.
    - exact ih.
    - apply Singleton_is_finite.
  * exact ih.
  * exact ih.
  * exact ih.
  * exact ih.
  * exact ih.
  * exact ih.
  * exact (finite_union ih).
  * exact ih.
  * exact (finite_union ih).
  * exact ih.
  * exact ih.
Qed.

Theorem conj_intro_add Γ Γ' A B:
  (Γ ⊢ A) → (Γ' ⊢ B) → (Γ ∪ Γ' ⊢ A ∧ B).
Proof.
  intros hA hB.
  assert (hfinite := context_is_finite hA).
  assert (hfinite' := context_is_finite hB).
  apply (weakening_general hfinite') in hA.
  apply (weakening_general hfinite) in hB.
  rewrite Union_commutative in hB.
  exact (conj_intro _ A B hA hB).
Qed.

Theorem impl_elim_add Γ Γ' A B:
  (Γ ⊢ A → B) → (Γ' ⊢ A) → (Γ ∪ Γ' ⊢ B).
Proof.
  intros hA hB.
  assert (hfinite := context_is_finite hA).
  assert (hfinite' := context_is_finite hB).
  apply (weakening_general hfinite') in hA.
  apply (weakening_general hfinite) in hB.
  rewrite Union_commutative in hB.
  exact (impl_elim _ A B hA hB).
Qed.

Theorem neg_elim_add Γ Γ' A:
  (Γ ⊢ ¬A) → (Γ' ⊢ A) → (Γ ∪ Γ' ⊢ ⊥).
Proof.
  intros hnA hA.
  assert (hfinite := context_is_finite hnA).
  assert (hfinite' := context_is_finite hA).
  apply (weakening_general hfinite') in hnA.
  apply (weakening_general hfinite) in hA.
  rewrite Union_commutative in hA.
  exact (neg_elim _ A hnA hA).
Qed.

Theorem disj_elim_add Γ Γ' Γ'' A B C:
  (Γ ⊢ A ∨ B) → (Γ' ∪ {A,} ⊢ C) → (Γ'' ∪ {B,} ⊢ C) →
  (Γ ∪ Γ' ∪ Γ'' ⊢ C).
Proof.
  intros h hA hB.
  assert (hfinite := context_is_finite h).
  assert (hfinite' := context_is_finite hA).
  assert (hfinite'' := context_is_finite hB).
  apply finite_union in hfinite'.
  apply finite_union in hfinite''.
  apply (weakening_general hfinite') in h.
  apply (weakening_general hfinite'') in h.
  apply (weakening_general hfinite) in hA.
  apply (weakening_general hfinite'') in hA.
  apply (weakening_general hfinite) in hB.
  apply (weakening_general hfinite') in hB.
  rewrite (Union_commutative _ _ Γ) in hA.
  rewrite Union_associative in hA.
  rewrite Union_associative in hA.
  rewrite (Union_commutative _ _ Γ'') in hA.
  rewrite <- Union_associative in hA.
  rewrite <- Union_associative in hA.
  rewrite Union_commutative in hB.
  rewrite (Union_commutative _ _ Γ) in hB.
  rewrite <- Union_associative in hB.
  rewrite (Union_commutative _ Γ' Γ) in hB.
  rewrite <- Union_associative in hB.
  exact (disj_elim _ A B C h hA hB).
Qed.
