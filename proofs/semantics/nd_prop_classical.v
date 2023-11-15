
(* Sequent natural deduction for *)
(* classical propositional calculus *)

(* Shown is soundness under classical semantics. *)
(* Furthermore, some admissible rules are shown. *)

Require Import Coq.Unicode.Utf8.

(* Double negation elimination, *)
(* needed for classical semantics *)
Axiom dne: ∀A: Prop, ¬¬A → A.

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

Definition tautology (A: Formula) :=
  ∀I, sat I A.

Inductive List :=
| Empty
| Cons: List → Formula → List.

Fixpoint concat (Γ Γ': List) :=
  match Γ' with
  | Empty => Γ
  | (Cons Γ' A) => Cons (concat Γ Γ') A
  end.

(* The type of sequents *)
Inductive Seq := seq: List → Formula → Seq.

Fixpoint sat_list (I: Var → Prop) (Γ: List) :=
  match Γ with
  | Empty => True
  | Cons Γ A => sat I A ∧ sat_list I Γ
  end.

(* Logically valid sequents *)
Definition valid '(seq Γ A) :=
  ∀I, sat_list I Γ → sat I A.

Declare Scope formula_scope.
Bind Scope formula_scope with Formula.

Notation "⊥" := FF (at level 0).
Notation "¬ A" := (Neg A): formula_scope.
Notation "A ∧ B" := (Conj A B): formula_scope.
Notation "A ∨ B" := (Disj A B): formula_scope.
Notation "A → B" := (Impl A B): formula_scope.

Notation "⊨ A" := (tautology A) (at level 100).
Notation "Γ ⊨ A" := (valid (seq Γ A)) (at level 100).

Theorem valid_empty_is_tautology (A: Formula):
  (Empty ⊨ A) ↔ (⊨ A).
Proof.
  split.
  * intro h. unfold tautology. intro I.
    unfold valid in h. simpl sat_list in h.
    apply (h I). trivial.
  * intro h. unfold tautology in h.
    unfold valid. intro I. intro h0. clear h0.
    exact (h I).
Qed.

Lemma basic_seq_intro_is_valid A:
  (Cons Empty A) ⊨ A.
Proof.
  unfold valid. intro I. intro h.
  simpl sat_list in h. exact (proj1 h).
Qed.

Lemma weakening_is_valid Γ A B:
  (Γ ⊨ B) → (Cons Γ A ⊨ B).
Proof.
  intro h. unfold valid. intro I. intro hI.
  simpl sat_list in hI. unfold valid in h.
  exact (h I (proj2 hI)).
Qed.

Lemma conj_intro_is_valid Γ A B:
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

Lemma conj_eliml_is_valid Γ A B:
  (Γ ⊨ A ∧ B) → (Γ ⊨ A).
Proof.
  intro h. unfold valid. intro I. intro hI.
  unfold valid in h. apply (h I) in hI. clear h.
  simpl sat in hI. exact (proj1 hI).
Qed.

Lemma conj_elimr_is_valid Γ A B:
  (Γ ⊨ A ∧ B) → (Γ ⊨ B).
Proof.
  intro h. unfold valid. intro I. intro hI.
  unfold valid in h. apply (h I) in hI. clear h.
  simpl sat in hI. exact (proj2 hI).
Qed.

Lemma disj_introl_is_valid Γ A B:
  (Γ ⊨ A) → (Γ ⊨ A ∨ B).
Proof.
  intro h. unfold valid. intro I. intro hI.
  unfold valid in h. apply (h I) in hI. clear h.
  simpl sat. left. exact hI.
Qed.

Lemma disj_intror_is_valid Γ A B:
  (Γ ⊨ B) → (Γ ⊨ A ∨ B).
Proof.
  intro h. unfold valid. intro I. intro hI.
  unfold valid in h. apply (h I) in hI. clear h.
  simpl sat. right. exact hI.
Qed.

Lemma disj_elim_is_valid Γ A B C:
  (Γ ⊨ A ∨ B) → (Cons Γ A ⊨ C) → (Cons Γ B ⊨ C) → (Γ ⊨ C).
Proof.
  intros hAB hA hB. unfold valid. intro I. intro hI.
  unfold valid in hAB. assert (hIAB := hAB I hI). clear hAB.
  simpl sat in hIAB. destruct hIAB as [hIA | hIB].
  * unfold valid in hA. simpl sat_list in hA.
    exact (hA I (conj hIA hI)).
  * unfold valid in hB. simpl sat_list in hB.
    exact (hB I (conj hIB hI)).
Qed.

Lemma impl_intro_is_valid Γ A B:
  (Cons Γ A ⊨ B) → (Γ ⊨ A → B).
Proof.
  intro h. unfold valid. intro I. intro hI.
  simpl sat. intro hIA.
  unfold valid in h. simpl sat_list in h.
  exact (h I (conj hIA hI)).
Qed.

Lemma impl_elim_is_valid Γ A B:
  (Γ ⊨ A → B) → (Γ ⊨ A) → (Γ ⊨ B).
Proof.
  intros hAB hA. unfold valid. intro I. intro hI.
  unfold valid in hAB. assert (h := hAB I hI). clear hAB.
  simpl sat in h. unfold valid in hA.
  exact (h (hA I hI)).
Qed.

Lemma neg_intro_is_valid Γ A:
  (Cons Γ A ⊨ ⊥) → (Γ ⊨ ¬A).
Proof.
  intro h. unfold valid. intro I. intro hI.
  simpl sat. intro hIA. unfold valid in h.
  simpl sat_list in h. simpl sat in h.
  exact (h I (conj hIA hI)).
Qed.

Lemma neg_elim_is_valid Γ A:
  (Γ ⊨ ¬A) → (Γ ⊨ A) → (Γ ⊨ ⊥).
Proof.
  intros hnA hA. unfold valid. intro I. intro hI.
  simpl sat. unfold valid in hnA. unfold valid in hA.
  assert (hInA := hnA I hI). clear hnA.
  assert (hIA := hA I hI). clear hA.
  simpl sat in hInA. exact (hInA hIA).
Qed.

Lemma contraction_is_valid Γ Γ' A B:
  (concat (Cons (Cons Γ A) A) Γ' ⊨ B)
  → (concat (Cons Γ A) Γ' ⊨ B).
Proof.
  intro h. unfold valid. intro I. intro hI.
  unfold valid in h. apply (h I). clear h.
  induction Γ' as [| Γ' ih C].
  * simpl sat_list. simpl sat_list in hI.
    destruct hI as (hIA, hIΓ).
    exact (conj hIA (conj hIA hIΓ)).
  * simpl sat_list. simpl sat_list in hI.
    destruct hI as (hI1, hI2). split.
    - exact hI1.
    - apply ih. exact hI2. 
Qed.

Lemma exchange_is_valid Γ Γ' A B C:
  (concat (Cons (Cons Γ A) B) Γ' ⊨ C)
  → (concat (Cons (Cons Γ B) A) Γ' ⊨ C).
Proof.
  intro h. unfold valid. intro I. intro hI.
  unfold valid in h. apply (h I). clear h.
  induction Γ' as [| Γ' ih D].
  * simpl sat_list. simpl sat_list in hI.
    destruct hI as (hIA, (hIB, hIΓ)).
    exact (conj hIB (conj hIA hIΓ)).
  * simpl sat_list. simpl sat_list in hI.
    destruct hI as (hI1, hI2). split.
    - exact hI1.
    - apply ih. exact hI2.
Qed.

Lemma dne_is_valid Γ A:
  (Γ ⊨ ¬¬A) → (Γ ⊨ A).
Proof.
  intro h. unfold valid. intro I. intro hI.
  apply dne. unfold valid in h. simpl sat in h.
  apply (h I). exact hI.
Qed.

Inductive Prf: Seq → Prop :=
| BasicSeqIntro: ∀A, Prf (seq (Cons Empty A) A)
| Weakening: ∀Γ A B,
    Prf (seq Γ B) → Prf (seq (Cons Γ A) B)
| Contraction: ∀Γ Γ' A B,
    Prf (seq (concat (Cons (Cons Γ A) A) Γ') B)
    → Prf (seq (concat (Cons Γ A) Γ') B)
| Exchange: ∀Γ Γ' A B C,
    Prf (seq (concat (Cons (Cons Γ A) B) Γ') C)
    → Prf (seq (concat (Cons (Cons Γ B) A) Γ') C)
| ConjIntro: ∀Γ A B,
    Prf (seq Γ A) → Prf (seq Γ B)
    → Prf (seq Γ (A ∧ B))
| ConjElimL: ∀Γ A B,
    Prf (seq Γ (A ∧ B)) → Prf (seq Γ A)
| ConjElimR: ∀Γ A B,
    Prf (seq Γ (A ∧ B)) → Prf (seq Γ B)
| DisjIntroL: ∀Γ A B,
    Prf (seq Γ A) → Prf (seq Γ (A ∨ B))
| DisjIntroR: ∀Γ A B,
    Prf (seq Γ B) → Prf (seq Γ (A ∨ B))
| DisjElim: ∀Γ A B C,
    Prf (seq Γ (A ∨ B)) → Prf (seq (Cons Γ A) C)
    → Prf (seq (Cons Γ B) C) → Prf (seq Γ C)
| ImplIntro: ∀Γ A B,
    Prf (seq (Cons Γ A) B) → Prf (seq Γ (A → B))
| ImplElim: ∀Γ A B,
    Prf (seq Γ (A → B)) → Prf (seq Γ A)
    → Prf (seq Γ B)
| NegIntro: ∀Γ A,
    Prf (seq (Cons Γ A) ⊥) → Prf (seq Γ (¬A))
| NegElim: ∀Γ A,
    Prf (seq Γ (¬A)) → Prf (seq Γ A)
    → Prf (seq Γ ⊥)
| DNE: ∀Γ A,
    Prf (seq Γ (¬¬A))
    → Prf (seq Γ A).

Theorem soundness_of_natural_deduction:
  ∀S, Prf S → valid S.
Proof.
  intro S. intro pi.
  induction pi as [A
  | Γ A B pi hpi
  | Γ Γ' A B pi hpi
  | Γ Γ' A B C pi hpi
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
  * exact (basic_seq_intro_is_valid A). 
  * exact (weakening_is_valid Γ A B hpi).
  * exact (contraction_is_valid Γ Γ' A B hpi).
  * exact (exchange_is_valid Γ Γ' A B C hpi).
  * exact (conj_intro_is_valid Γ A B hpiA hpiB).
  * exact (conj_eliml_is_valid Γ A B hpi).
  * exact (conj_elimr_is_valid Γ A B hpi).
  * exact (disj_introl_is_valid Γ A B hpi).
  * exact (disj_intror_is_valid Γ A B hpi).
  * exact (disj_elim_is_valid Γ A B C hpi hpiA hpiB).
  * exact (impl_intro_is_valid Γ A B hpi).
  * exact (impl_elim_is_valid Γ A B hpiAB hpiA).
  * exact (neg_intro_is_valid Γ A hpi).
  * exact (neg_elim_is_valid Γ A hpinA hpiA).
  * exact (dne_is_valid Γ A hpi).
Qed.

Theorem general_weakening_is_admissble Γ Γ' A:
  Prf (seq Γ A) → Prf (seq (concat Γ Γ') A).
Proof.
  intro h. induction Γ' as [| Γ' ih B].
  * simpl concat. exact h.
  * simpl concat. apply Weakening. exact ih.
Qed.

Fixpoint is_in (A: Formula) (Γ: List): Prop :=
  match Γ with
  | Empty => False
  | Cons Γ B => A = B \/ is_in A Γ
  end.

Theorem basic_seq_intro_general1_is_admissible Γ A:
  Prf (seq (Cons Γ A) A).
Proof.
  induction Γ as [| Γ ih B].
  * exact (BasicSeqIntro A).
  * pose (Γ' := (Cons (Cons Γ A) B)).
    assert (h: Prf (seq (concat Γ' Empty) A)). {
      simpl concat. unfold Γ'.
      apply Weakening. exact ih.
    }
    assert (h' := Exchange Γ Empty A B A h).
    simpl concat in h'. exact h'.
Qed.

Theorem basic_seq_intro_general2_is_admissible Γ A:
  is_in A Γ → Prf (seq Γ A).
Proof.
  intro h. induction Γ as [| Γ ih B].
  * simpl is_in in h. exfalso. exact h.
  * simpl is_in in h. destruct h as [hAB |hA].
    - rewrite <- hAB.
      exact (basic_seq_intro_general1_is_admissible Γ A).
    - apply Weakening. apply ih. exact hA.
Qed.
