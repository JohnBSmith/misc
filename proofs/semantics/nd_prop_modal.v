
(* Sequent natural deduction for *)
(* modal propositional calculus *)

(* Shown is soundness under Kripke semantics. *)

Require Import Coq.Unicode.Utf8.

(* The type of atomic variables. *)
Inductive Var := var: nat -> Var.

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
| Nec: Formula → Formula
| Pos: Formula → Formula.

Declare Scope formula_scope.
Bind Scope formula_scope with Formula.

Notation "¬ A" := (Neg A): formula_scope.
Notation "A ∧ B" := (Conj A B): formula_scope.
Notation "A ∨ B" := (Disj A B): formula_scope.
Notation "A → B" := (Impl A B): formula_scope.
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
  | Nec A => ∀w', M.(R) w w' → (sat M w' A)
  | Pos A => ∃w', M.(R) w w' ∧ (sat M w' A)
  end.

Inductive List :=
| Empty
| Cons: List → Formula → List.

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
  ∀M, ∀w, sat_list M w Γ -> sat M w A.

Notation "Γ ⊢ A" := (seq Γ A) (at level 110).
Notation "Γ ⊨ A" := (valid (seq Γ A)) (at level 110).

Lemma weakening_is_sound Γ A B:
  (Γ ⊨ B) -> ((Cons Γ A) ⊨ B).
Proof.
  intro h. unfold valid. intros M w. intro hMw.
  simpl sat_list in hMw. unfold valid in h.
  exact (h M w (proj2 hMw)).
Qed.

Lemma conj_intro_is_sound Γ A B:
  (Γ ⊨ A) → (Γ ⊨ B) → (Γ ⊨ A ∧ B).
Proof.
  intros hA hB. unfold valid.
  intros M w. intro hMw. simpl sat.
  unfold valid in hA.
  unfold valid in hB.
  assert (hMwA := hA M w hMw). clear hA.
  assert (hMwB := hB M w hMw). clear hB.
  exact (conj hMwA hMwB).
Qed.

