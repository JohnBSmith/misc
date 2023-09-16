
(* Sequent natural deduction for *)
(* classical propositional calculus *)

(* Shown is soundness under classical semantics. *)
(* Furthermore, some admissible rules are shown. *)

Require Import Coq.Unicode.Utf8.

Inductive Bool := false | true.
Definition notb (a: Bool) := match a with
  false => true | true => false end.
Definition andb (a b: Bool) := match a with
  false => false | true => b end.
Definition orb (a b: Bool) := match a with
  true => true | false => b end.
Definition is_true (a: Bool): Prop := match a with
  false => False | true => True end.

Theorem notb_to_not {a: Bool}:
  is_true (notb a) → ~is_true a.
Proof.
  intro h. destruct a.
  * simpl. intro hFalse. exact hFalse.
  * simpl. intro hTrue. simpl in h. exact h.
Qed.

Theorem not_to_notb {a: Bool}:
  ¬is_true a → is_true (notb a).
Proof.
  intro h. destruct a.
  * simpl. trivial.
  * simpl. simpl in h. apply h. trivial.
Qed.

Theorem notb_dne {a: Bool}:
  is_true (notb (notb a)) → is_true a.
Proof.
  intro h. destruct a.
  * simpl in h. simpl. exact h.
  * simpl. trivial.
Qed.

Theorem andb_to_conj {a b: Bool}:
  is_true (andb a b) → is_true a ∧ is_true b.
Proof.
  intro h. destruct a.
  * simpl in h. destruct b.
    - simpl. exact (conj h h).
    - simpl. split.
      -- exact h.
      -- trivial.
  * simpl in h. simpl. split.
    - trivial.
    - exact h.
Qed.

Theorem conj_to_andb {a b: Bool}:
  is_true a ∧ is_true b → is_true (andb a b).
Proof.
  intro h. destruct a.
  * simpl. simpl in h. exact (proj1 h).
  * simpl. exact (proj2 h).
Qed.

Theorem andb_proj1 {a b: Bool}:
  is_true (andb a b) → is_true a.
Proof.
  intro h. destruct a.
  * simpl in h. simpl. exact h.
  * simpl. trivial. 
Qed.

Theorem andb_proj2 {a b: Bool}:
  is_true (andb a b) → is_true b.
Proof.
  intro h. destruct a.
  * simpl in h. destruct b.
    - simpl. exact h.
    - simpl. trivial.
  * simpl in h. exact h.
Qed.

Theorem andb_intro {a b: Bool}:
  is_true a → is_true b → is_true (andb a b).
Proof.
  intro ha. intro hb. destruct a.
  * simpl. simpl in ha. exact ha.
  * simpl. exact hb.
Qed.

Theorem orb_introl {a b: Bool}:
  is_true a → is_true (orb a b).
Proof.
  intro h. destruct a.
  * destruct b.
    - simpl. simpl in h. exact h.
    - simpl. trivial.
  * simpl. trivial.
Qed.

Theorem orb_intror {a b: Bool}:
  is_true b → is_true (orb a b).
Proof.
  intro h. destruct a.
  * simpl. exact h.
  * simpl. trivial.
Qed.

Theorem orb_to_or {a b: Bool}:
  is_true (orb a b) → (is_true a) ∨ (is_true b).
Proof.
  intro h. destruct a.
  * simpl in h. right. exact h.
  * left. simpl. simpl in h. exact h.
Qed.

Theorem implb_to_impl {a b: Bool}:
  is_true (orb (notb a) b) → is_true a → is_true b.
Proof.
  intro h. intro ha. destruct a.
  * destruct b.
    - simpl. simpl in ha. exact ha.
    - simpl. simpl in h. exact h.
  * simpl in h. exact h.
Qed.

Theorem impl_to_implb {a b: Bool}:
  (is_true a → is_true b) → is_true (orb (notb a) b).
Proof.
  intro h. destruct a.
  * simpl. trivial.
  * simpl. apply h. simpl. trivial.
Qed.

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
| Impl: Formula → Formula → Formula.

(* Satisfaction relation *)
Fixpoint sat (I: Var → Bool) (A: Formula) :=
  match A with
  | Atom v => I v
  | FF => false
  | TF => true
  | Neg A => notb (sat I A)
  | Conj A B => andb (sat I A) (sat I B)
  | Disj A B => orb (sat I A) (sat I B)
  | Impl A B => orb (notb (sat I A)) (sat I B)
  end.

Definition tautology (A: Formula) :=
  ∀I, is_true (sat I A).

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

Fixpoint sat_list (I: Var → Bool) (Γ: List) :=
  match Γ with
  | Empty => true
  | Cons Γ A => andb (sat I A) (sat_list I Γ)
  end.

(* Logically valid sequents *)
Definition valid '(seq Γ A) :=
  ∀I, is_true (sat_list I Γ) → is_true (sat I A).

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
    apply (h I). simpl is_true. trivial.
  * intro h. unfold tautology in h.
    unfold valid. intro I. intro h0. clear h0.
    exact (h I).
Qed.

Lemma basic_seq_intro_is_sound A:
  Cons Empty A ⊨ A.
Proof.
  unfold valid. intro I. intro h.
  simpl sat_list in h.
  exact (andb_proj1 h).
Qed.

Lemma weakening_is_sound Γ A B:
  (Γ ⊨ B) → (Cons Γ A ⊨ B).
Proof.
  intro h. unfold valid. intro I. intro hI.
  simpl sat_list in hI. unfold valid in h.
  exact (h I (andb_proj2 hI)).
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
  exact (andb_intro hIA hIB).
Qed.

Lemma conj_eliml_is_sound Γ A B:
  (Γ ⊨ A ∧ B) → (Γ ⊨ A).
Proof.
  intro h. unfold valid. intro I. intro hI.
  unfold valid in h. apply (h I) in hI. clear h.
  simpl sat in hI. exact (andb_proj1 hI).
Qed.

Lemma conj_elimr_is_sound Γ A B:
  (Γ ⊨ A ∧ B) → (Γ ⊨ B).
Proof.
  intro h. unfold valid. intro I. intro hI.
  unfold valid in h. apply (h I) in hI. clear h.
  simpl sat in hI. exact (andb_proj2 hI).
Qed.

Lemma disj_introl_is_sound Γ A B:
  (Γ ⊨ A) → (Γ ⊨ A ∨ B).
Proof.
  intro h. unfold valid. intro I. intro hI.
  unfold valid in h. apply (h I) in hI. clear h.
  simpl sat. apply orb_introl. exact hI.
Qed.

Lemma disj_intror_is_sound Γ A B:
  (Γ ⊨ B) → (Γ ⊨ A ∨ B).
Proof.
  intro h. unfold valid. intro I. intro hI.
  unfold valid in h. apply (h I) in hI. clear h.
  simpl sat. apply orb_intror. exact hI.
Qed.

Lemma disj_elim_is_sound Γ A B C:
  (Γ ⊨ A ∨ B) → (Cons Γ A ⊨ C) → (Cons Γ B ⊨ C) → (Γ ⊨ C).
Proof.
  intros hAB hA hB. unfold valid. intro I. intro hI.
  unfold valid in hAB. assert (hIAB := hAB I hI). clear hAB.
  simpl sat in hIAB. apply orb_to_or in hIAB.
  destruct hIAB as [hIA | hIB].
  * unfold valid in hA. simpl sat_list in hA.
    exact (hA I (andb_intro hIA hI)).
  * unfold valid in hB. simpl sat_list in hB.
    exact (hB I (andb_intro hIB hI)).
Qed.

Lemma impl_intro_is_sound Γ A B:
  (Cons Γ A ⊨ B) → (Γ ⊨ A → B).
Proof.
  intro h. unfold valid. intro I. intro hI.
  simpl sat. apply impl_to_implb. intro hIA.
  unfold valid in h. simpl sat_list in h.
  exact (h I (andb_intro hIA hI)).
Qed.

Lemma impl_elim_is_sound Γ A B:
  (Γ ⊨ A → B) → (Γ ⊨ A) → (Γ ⊨ B).
Proof.
  intros hAB hA. unfold valid. intro I. intro hI.
  unfold valid in hAB. assert (h := hAB I hI). clear hAB.
  simpl sat in h. unfold valid in hA.
  assert (h' := implb_to_impl h).
  exact (h' (hA I hI)).
Qed.

Lemma neg_intro_is_sound Γ A:
  (Cons Γ A ⊨ ⊥) → (Γ ⊨ ¬A).
Proof.
  intro h. unfold valid. intro I. intro hI.
  simpl sat. apply not_to_notb.
  intro hIA. unfold valid in h.
  simpl sat_list in h. simpl sat in h.
  exact (h I (andb_intro hIA hI)).
Qed.

Lemma neg_elim_is_sound Γ A:
  (Γ ⊨ ¬A) → (Γ ⊨ A) → (Γ ⊨ ⊥).
Proof.
  intros hnA hA. unfold valid. intro I. intro hI.
  simpl sat. unfold valid in hnA. unfold valid in hA.
  assert (hInA := hnA I hI). clear hnA.
  assert (hIA := hA I hI). clear hA.
  simpl sat in hInA. apply notb_to_not in hInA.
  exact (hInA hIA).
Qed.

Lemma contraction_is_sound Γ Γ' A B:
  (concat (Cons (Cons Γ A) A) Γ' ⊨ B)
  → (concat (Cons Γ A) Γ' ⊨ B).
Proof.
  intro h. unfold valid. intro I. intro hI.
  unfold valid in h. apply (h I). clear h.
  induction Γ' as [| Γ' ih C].
  * simpl sat_list. simpl sat_list in hI.
    destruct (andb_to_conj hI) as (hIA, hIΓ).
    exact (andb_intro hIA (andb_intro hIA hIΓ)).
  * simpl sat_list. simpl sat_list in hI.
    destruct (andb_to_conj hI) as (hI1, hI2).
    apply conj_to_andb. split.
    - exact hI1.
    - apply ih. exact hI2. 
Qed.

Lemma exchange_is_sound Γ Γ' A B C:
  (concat (Cons (Cons Γ A) B) Γ' ⊨ C)
  → (concat (Cons (Cons Γ B) A) Γ' ⊨ C).
Proof.
  intro h. unfold valid. intro I. intro hI.
  unfold valid in h. apply (h I). clear h.
  induction Γ' as [| Γ' ih D].
  * simpl sat_list. simpl sat_list in hI.
    apply andb_to_conj in hI.
    destruct hI as (hIA, htail).
    apply andb_to_conj in htail.
    destruct htail as (hIB, hIΓ).
    exact (andb_intro hIB (andb_intro hIA hIΓ)).
  * simpl sat_list. simpl sat_list in hI.
    destruct (andb_to_conj hI) as (hI1, hI2).
    apply conj_to_andb. split.
    - exact hI1.
    - apply ih. exact hI2.
Qed.

Lemma dne_is_sound Γ A:
  (Γ ⊨ ¬¬A) → (Γ ⊨ A).
Proof.
  intro h. unfold valid. intro I. intro hI.
  unfold valid in h. simpl sat in h.
  assert (hIA := notb_dne (h I hI)).
  exact hIA.
Qed.

Inductive Prf: Seq → Prop :=
| BasicSeqIntro: ∀A, Prf (seq (Cons Empty A) A)
| Weakening: ∀Γ A B,
    Prf (seq Γ B) → Prf (seq (Cons Γ A) B)
| Contraction: ∀Γ Γ' A B,
    Prf (seq (concat (Cons (Cons Γ A) A) Γ') B) →
    Prf (seq (concat (Cons Γ A) Γ') B)
| Exchange: ∀Γ Γ' A B C,
    Prf (seq (concat (Cons (Cons Γ A) B) Γ') C) →
    Prf (seq (concat (Cons (Cons Γ B) A) Γ') C)
| ConjIntro: ∀Γ A B,
    Prf (seq Γ A) → Prf (seq Γ B) →
    Prf (seq Γ (A ∧ B))
| ConjElimL: ∀Γ A B,
    Prf (seq Γ (A ∧ B)) → Prf (seq Γ A)
| ConjElimR: ∀Γ A B,
    Prf (seq Γ (A ∧ B)) → Prf (seq Γ B)
| DisjIntroL: ∀Γ A B,
    Prf (seq Γ A) → Prf (seq Γ (A ∨ B))
| DisjIntroR: ∀Γ A B,
    Prf (seq Γ B) → Prf (seq Γ (A ∨ B))
| DisjElim: ∀Γ A B C,
    Prf (seq Γ (A ∨ B)) → Prf (seq (Cons Γ A) C) →
    Prf (seq (Cons Γ B) C) → Prf (seq Γ C)
| ImplIntro: ∀Γ A B,
    Prf (seq (Cons Γ A) B) → Prf (seq Γ (A → B))
| ImplElim: ∀Γ A B,
    Prf (seq Γ (A → B)) → Prf (seq Γ A) → Prf (seq Γ B)
| NegIntro: ∀Γ A,
    Prf (seq (Cons Γ A) ⊥) → Prf (seq Γ (¬A))
| NegElim: ∀Γ A,
    Prf (seq Γ (¬A)) → Prf (seq Γ A) → Prf (seq Γ ⊥)
| DNE: ∀Γ A,
    Prf (seq Γ (¬¬A)) → Prf (seq Γ A).

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
  * exact (basic_seq_intro_is_sound A). 
  * exact (weakening_is_sound Γ A B hpi).
  * exact (contraction_is_sound Γ Γ' A B hpi).
  * exact (exchange_is_sound Γ Γ' A B C hpi).
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

Theorem general_weakening_is_admissble Γ Γ' A:
  Prf (seq Γ A)
  → Prf (seq (concat Γ Γ') A).
Proof.
  intro h. induction Γ' as [| Γ' ih B].
  * simpl concat. exact h.
  * simpl concat. apply Weakening. exact ih.
Qed.

Fixpoint is_in (A: Formula) (Γ: List): Prop :=
  match Γ with
  | Empty => False
  | (Cons Γ B) => A = B \/ is_in A Γ
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
