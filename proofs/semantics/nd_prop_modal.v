
(* Sequent natural deduction for *)
(* modal propositional calculus *)

(* Shown is soundness under Kripke semantics. *)

Require Import Coq.Unicode.Utf8.

(* Double negation elimination. *)
Axiom dne: ∀(A: Prop), ¬¬A → A.

(* The type of atomic variables. *)
Inductive Var := var: nat → Var.

(* Recursive definition of the type of *)
(* well-formed logical formulas. *)
Inductive Formula: Set :=
| Atom: Var → Formula
| FF: Formula
| TF: Formula
| Neg: Formula → Formula
| Conj: Formula → Formula → Formula
| Disj: Formula → Formula → Formula
| Impl: Formula → Formula → Formula
| Equi: Formula → Formula → Formula
| Nec: Formula → Formula
| Pos: Formula → Formula.

Declare Scope formula_scope.
Bind Scope formula_scope with Formula.

Notation "⊥" := FF (at level 0).
Notation "¬ A" := (Neg A): formula_scope.
Notation "A ∧ B" := (Conj A B): formula_scope.
Notation "A ∨ B" := (Disj A B): formula_scope.
Notation "A → B" := (Impl A B): formula_scope.
Notation "A ↔ B" := (Equi A B): formula_scope.
Notation "□ A" := (Nec A) (at level 75).
Notation "◇ A" := (Pos A) (at level 75).

Definition World := Type.

(* The type of Kripke models. *)
(* An w: W where W: World is a Kripke world. *)
(* R is the accessability relation. *)
(* I is the interpretation, also called valuation. *)
Record Model := {
  W: World; 
  R: W → W → Prop; 
  I: W → Var → Prop
}.

(* Satisfaction relation. *)
Fixpoint sat (M: Model) (w: M.(W)) (A: Formula) :=
  match A with
  | Atom a => M.(I) w a
  | FF => False
  | TF => True
  | Neg A => ¬(sat M w A)
  | Conj A B => (sat M w A) ∧ (sat M w B)
  | Disj A B => (sat M w A) ∨ (sat M w B)
  | Impl A B => (sat M w A) → (sat M w B)
  | Equi A B => (sat M w A) ↔ (sat M w B)
  | Nec A => ∀w', M.(R) w w' → (sat M w' A)
  | Pos A => ∃w', M.(R) w w' ∧ (sat M w' A)
  end.

Inductive List :=
| Empty
| Cons: List → Formula → List.

Fixpoint concat (Γ Γ': List) :=
  match Γ' with
  | Empty => Γ
  | Cons Γ' A => Cons (concat Γ Γ') A
  end.

(* Satisfaction relation for lists. *)
Fixpoint sat_list (M: Model) (w: M.(W)) (Γ: List) :=
  match Γ with
  | Empty => True
  | Cons Γ A => (sat M w A) /\ (sat_list M w Γ)
  end.

(* The type of sequents. *)
Inductive Seq := seq: List → Formula → Seq.

(* Logically valid sequents. *)
Definition valid '(seq Γ A) :=
  ∀M, ∀w, sat_list M w Γ → sat M w A.

Notation "Γ ⊢ A" := (seq Γ A) (at level 110).
Notation "Γ ⊨ A" := (valid (seq Γ A)) (at level 110).

Lemma basic_seq_is_sound A:
  Cons Empty A ⊨ A.
Proof.
  unfold valid. intros M w. intro h.
  simpl sat_list in h. exact (proj1 h).
Qed.

Lemma weakening_is_sound Γ A B:
  (Γ ⊨ B) → (Cons Γ A ⊨ B).
Proof.
  intro hB. unfold valid. intros M w. intro h.
  simpl sat_list in h. unfold valid in hB.
  exact (hB M w (proj2 h)).
Qed.

Lemma exchange_is_sound Γ Γ' A B C:
  (concat (Cons (Cons Γ A) B) Γ' ⊨ C)
  → (concat (Cons (Cons Γ B) A) Γ' ⊨ C).
Proof.
  intro hAB. unfold valid. intros M w.
  intro h. unfold valid in hAB.
  apply (hAB M w). clear hAB.
  induction Γ' as [| Γ' ih D].
  * simpl concat. simpl concat in h.
    simpl sat_list. simpl sat_list in h.
    destruct h as (hA, (hB, hΓ)).
    exact (conj hB (conj hA hΓ)).
  * simpl concat. simpl sat_list.
    simpl concat in h. simpl sat_list in h.
    destruct h as (hD, hBA). split.
    - exact hD.
    - apply ih. exact hBA.
Qed.

Lemma contraction_is_sound Γ Γ' A B:
  (concat (Cons (Cons Γ A) A) Γ' ⊨ B)
  → (concat (Cons Γ A) Γ' ⊨ B).
Proof.
  intro hAA. unfold valid. intros M w.
  intro h. unfold valid in hAA.
  apply (hAA M w). clear hAA.
  induction Γ' as [| Γ' ih D].
  * simpl concat. simpl sat_list.
    simpl concat in h. simpl sat_list in h.
    destruct h as (hA, hΓ).
    exact (conj hA (conj hA hΓ)).
  * simpl concat. simpl sat_list.
    simpl concat in h. simpl sat_list in h.
    destruct h as (hD, hA). split.
    - exact hD.
    - apply ih. exact hA.
Qed.

Lemma conj_intro_is_sound Γ A B:
  (Γ ⊨ A) → (Γ ⊨ B) → (Γ ⊨ A ∧ B).
Proof.
  intros hA hB. unfold valid.
  intros M w. intro h. simpl sat.
  unfold valid in hA.
  unfold valid in hB.
  assert (hMwA := hA M w h). clear hA.
  assert (hMwB := hB M w h). clear hB.
  exact (conj hMwA hMwB).
Qed.

Lemma conj_eliml_is_sound Γ A B:
  (Γ ⊨ A ∧ B) → (Γ ⊨ A).
Proof.
  intro hAB. unfold valid. intros M w. intro h.
  unfold valid in hAB. apply (hAB M w) in h.
  simpl sat in h. exact (proj1 h).
Qed.

Lemma conj_elimr_is_sound Γ A B:
  (Γ ⊨ A ∧ B) → (Γ ⊨ B).
Proof.
  intro hAB. unfold valid. intros M w. intro h.
  unfold valid in hAB. apply (hAB M w) in h.
  simpl sat in h. exact (proj2 h).
Qed.

Lemma disj_introl_is_sound Γ A B:
  (Γ ⊨ A) → (Γ ⊨ A ∨ B).
Proof.
  intro hA. unfold valid. intros M w. intro h.
  simpl sat. left. unfold valid in hA.
  exact (hA M w h).
Qed.

Lemma disj_intror_is_sound Γ A B:
  (Γ ⊨ B) → (Γ ⊨ A ∨ B).
Proof.
  intro hB. unfold valid. intros M w. intro h.
  simpl sat. right. unfold valid in hB.
  exact (hB M w h).
Qed.

Lemma disj_elim_is_sound Γ A B C:
  (Γ ⊨ A ∨ B) → (Cons Γ A ⊨ C) → (Cons Γ B ⊨ C) → (Γ ⊨ C).
Proof.
  intros hAB hA hB. unfold valid. intros M w. intro h.
  unfold valid in hAB. assert (hAB := hAB M w h).
  simpl sat in hAB. destruct hAB as [hl | hr].
  * unfold valid in hA. simpl sat_list in hA.
    exact (hA M w (conj hl h)).
  * unfold valid in hB. simpl sat_list in hB.
    exact (hB M w (conj hr h)).
Qed.

Lemma impl_intro_is_sound Γ A B:
  (Cons Γ A ⊨ B) → (Γ ⊨ A → B).
Proof.
  intro hAB. unfold valid. intros M w. intro h.
  simpl sat. intro hA. unfold valid in hAB.
  apply (hAB M w). clear hAB. simpl sat_list.
  exact (conj hA h).
Qed.

Lemma impl_elim_is_sound Γ A B:
  (Γ ⊨ A → B) → (Γ ⊨ A) → (Γ ⊨ B).
Proof.
  intro hAB. intro hA. unfold valid. intros M w.
  intro h. unfold valid in hAB. unfold valid in hA.
  assert (hAB := hAB M w h). simpl sat in hAB.
  assert (hA := hA M w h). exact (hAB hA).
Qed.

Lemma neg_intro_is_sound Γ A:
  (Cons Γ A ⊨ ⊥) → (Γ ⊨ ¬A).
Proof.
  intro hnA. unfold valid. intros M w. intro h.
  simpl sat. unfold valid in hnA.
  assert (hnA := hnA M w). simpl sat_list in hnA.
  intro hA. assert (hFalse := hnA (conj hA h)).
  simpl in hFalse. exact hFalse.
Qed.

Lemma neg_elim_is_sound Γ A:
  (Γ ⊨ ¬A) → (Γ ⊨ A) → (Γ ⊨ ⊥).
Proof.
  intro hnA. intro hA. unfold valid. intros M w.
  intro h. simpl sat.
  unfold valid in hnA. assert (hnA := hnA M w h).
  unfold valid in hA. assert (hA := hA M w h).
  simpl sat in hnA. exact (hnA hA).
Qed.

Lemma equi_intro_is_sound Γ A B:
  (Γ ⊨ A → B) → (Γ ⊨ B → A) → (Γ ⊨ A ↔ B).
Proof.
  intro hAB. intro hBA. unfold valid. intros M w.
  intro h. unfold valid in hAB. unfold valid in hBA.
  simpl sat. split.
  * simpl sat in hAB. exact (hAB M w h).
  * simpl sat in hBA. exact (hBA M w h).
Qed.

Lemma equi_eliml_is_sound Γ A B:
  (Γ ⊨ A ↔ B) → (Γ ⊨ A → B).
Proof.
  intro hAB. unfold valid. intros M w. intro h.
  simpl sat. unfold valid in hAB. simpl sat in hAB.
  exact (proj1 (hAB M w h)).
Qed.

Lemma equi_elimr_is_sound Γ A B:
  (Γ ⊨ A ↔ B) → (Γ ⊨ B → A).
Proof.
  intro hAB. unfold valid. intros M w. intro h.
  simpl sat. unfold valid in hAB. simpl sat in hAB.
  exact (proj2 (hAB M w h)).
Qed.

Lemma dne_is_sound Γ A:
  (Γ ⊨ ¬¬A) → (Γ ⊨ A).
Proof.
  intro hA. unfold valid. intros M w. intro h.
  unfold valid in hA. apply (hA M w) in h.
  simpl sat in h. apply dne. exact h.
Qed.

Lemma nec_is_sound A:
  (Empty ⊨ A) → (Empty ⊨ □A).
Proof.
  intro hA. unfold valid. intros M w. intro h.
  unfold valid in hA.
  simpl sat. intro w'. intro hww'.
  apply (hA M w'). simpl sat_list. trivial.
Qed.

Lemma axiom_K_is_sound Γ A B:
  Γ ⊨ □(A → B) → (□A → □B).
Proof.
  unfold valid. intros M w. intro h. simpl sat.
  intro hAB. intro hA. intro w'. intro hww'.
  apply (hAB w' hww'). exact (hA w' hww').
Qed.

Lemma axiom_pos_is_sound Γ A:
  Γ ⊨ □A ↔ ¬◇¬A.
Proof.
  unfold valid. intros M w. intro h0. clear h0.
  simpl sat. split.
  * intro hA. intro hnA.
    destruct hnA as (w', (hww', hnA)).
    exact (hnA (hA w' hww')).
  * intro h. intro w'. intro hww'.
    apply dne. intro hnA.
    exact (h (ex_intro _ w' (conj hww' hnA))).
Qed.

Inductive Prf: Seq → Prop :=
| BasicSeq: ∀A, Prf (Cons Empty A ⊢ A)
| Weakening: ∀Γ A B, Prf (Γ ⊢ B) → Prf (Cons Γ A ⊢ B)
| Exchange: ∀Γ Γ' A B C,
    Prf (concat (Cons (Cons Γ A) B) Γ' ⊢ C)
    → Prf (concat (Cons (Cons Γ B) A) Γ' ⊢ C)
| Contraction: ∀Γ Γ' A B,
    Prf (concat (Cons (Cons Γ A) A) Γ' ⊢ B)
    → Prf (concat (Cons Γ A) Γ' ⊢ B)
| ConjIntro: ∀Γ A B, Prf (Γ ⊢ A) → Prf (Γ ⊢ B)
    → Prf (Γ ⊢ A ∧ B)
| ConjElimL: ∀Γ A B, Prf (Γ ⊢ A ∧ B) → Prf (Γ ⊢ A)
| ConjElimR: ∀Γ A B, Prf (Γ ⊢ A ∧ B) → Prf (Γ ⊢ B)
| DisjIntroL: ∀Γ A B, Prf (Γ ⊢ A) → Prf (Γ ⊢ A ∨ B)
| DisjIntroR: ∀Γ A B, Prf (Γ ⊢ B) → Prf (Γ ⊢ A ∨ B)
| DisjElim: ∀Γ A B C, Prf (Γ ⊢ A ∨ B)
    → Prf (Cons Γ A ⊢ C) → Prf (Cons Γ B ⊢ C)
    → Prf (Γ ⊢ C)
| ImplIntro: ∀Γ A B, Prf (Cons Γ A ⊢ B) → Prf (Γ ⊢ A → B)
| ImplElim: ∀Γ A B, Prf (Γ ⊢ A → B) → Prf (Γ ⊢ A)
    → Prf (Γ ⊢ B)
| NegIntro: ∀Γ A, Prf (Cons Γ A ⊢ ⊥) → Prf (Γ ⊢ ¬A)
| NegElim: ∀Γ A, Prf (Γ ⊢ ¬A) → Prf (Γ ⊢ A) → Prf (Γ ⊢ ⊥)
| EquiIntro: ∀Γ A B, Prf (Γ ⊢ A → B) → Prf (Γ ⊢ B → A)
    → Prf (Γ ⊢ A ↔ B)
| EquiElimL: ∀Γ A B, Prf (Γ ⊢ A ↔ B) → Prf (Γ ⊢ A → B)
| EquiElimR: ∀Γ A B, Prf (Γ ⊢ A ↔ B) → Prf (Γ ⊢ B → A)
| DNE: ∀Γ A, Prf (Γ ⊢ ¬¬A) → Prf (Γ ⊢ A)
| Necessitation: ∀A, Prf (Empty ⊢ A) → Prf (Empty ⊢ □A)
| AxiomK: ∀Γ A B, Prf (Γ ⊢ □(A → B) → (□A → □B))
| AxiomPos: ∀Γ A, Prf (Γ ⊢ □A ↔ ¬◇¬A).

Theorem soundness_of_natural_deduction:
  ∀S, Prf S → valid S.
Proof.
  intro S. intro h. induction h as [A
  | Γ A B h ih
  | Γ Γ' A B C h ih
  | Γ Γ' A B h ih
  | Γ A B hA ihA hB ihB
  | Γ A B hAB ihAB
  | Γ A B hAb ihAB
  | Γ A B hA ihA
  | Γ A B hB ihB
  | Γ A B C hAB ihAB hA ihA hB ihB
  | Γ A B h ih
  | Γ A B hAB ihAB hA ihA
  | Γ A h ih
  | Γ A hnA ihnA hA ihA
  | Γ A B hAB ihAB hBA ihBA
  | Γ A B h ih
  | Γ A B h ih
  | Γ A h ih
  | A h ih
  | Γ A B
  | Γ A].
  * exact (basic_seq_is_sound A).
  * exact (weakening_is_sound Γ A B ih).
  * exact (exchange_is_sound Γ Γ' A B C ih).
  * exact (contraction_is_sound Γ Γ' A B ih).
  * exact (conj_intro_is_sound Γ A B ihA ihB).
  * exact (conj_eliml_is_sound Γ A B ihAB).
  * exact (conj_elimr_is_sound Γ A B ihAB).
  * exact (disj_introl_is_sound Γ A B ihA).
  * exact (disj_intror_is_sound Γ A B ihB).
  * exact (disj_elim_is_sound Γ A B C ihAB ihA ihB).
  * exact (impl_intro_is_sound Γ A B ih).
  * exact (impl_elim_is_sound Γ A B ihAB ihA).
  * exact (neg_intro_is_sound Γ A ih).
  * exact (neg_elim_is_sound Γ A ihnA ihA).
  * exact (equi_intro_is_sound Γ A B ihAB ihBA).
  * exact (equi_eliml_is_sound Γ A B ih).
  * exact (equi_elimr_is_sound Γ A B ih).
  * exact (dne_is_sound Γ A ih).
  * exact (nec_is_sound A ih).
  * exact (axiom_K_is_sound Γ A B).
  * exact (axiom_pos_is_sound Γ A).
Qed.
