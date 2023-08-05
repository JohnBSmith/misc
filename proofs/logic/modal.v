
Require Import Coq.Unicode.Utf8.

Inductive Var := var: nat → Var.
Parameter World: Type.
Parameter P: Var → World → Prop.
Parameter R: World → World → Prop.
Parameter DNE: forall (A: Prop), ¬¬A → A.

Inductive Formula :=
| Atom: Var → Formula
| FF: Formula
| TF: Formula
| Neg: Formula → Formula
| Conj: Formula → Formula →   Formula
| Disj: Formula → Formula → Formula
| Impl: Formula → Formula → Formula
| Bij: Formula → Formula → Formula
| Nec: Formula → Formula
| Pos: Formula → Formula.

(* Standard translation *)
Fixpoint st (x: World) (A: Formula) :=
  match A with
  | Atom v => P v x
  | FF => False
  | TF => True
  | Neg A => ¬st x A
  | Conj A B => st x A ∧ st x B
  | Disj A B => st x A ∨ st x B
  | Impl A B => st x A → st x B
  | Bij A B => st x A ↔ st x B
  | Nec A => ∀y, R x y → st y A
  | Pos A => ∃y, R x y ∧ st y A
  end.

Definition is_theorem (A: Formula) :=
  ∀x, st x A.

Declare Scope modal_scope.
Bind Scope modal_scope with Formula.
Delimit Scope modal_scope with Formula.

Notation "⊢ A" := (is_theorem A) (at level 110).
Notation "⊥" := FF (at level 0).
Notation "□ A" := (Nec A) (at level 75).
Notation "◇ A" := (Pos A) (at level 75).
Notation "¬ A" := (Neg A): modal_scope.
Notation "A ∧ B" := (Conj A B): modal_scope.
Notation "A ∨ B" := (Disj A B): modal_scope.
Notation "A → B" := (Impl A B): modal_scope.
Notation "A ↔ B" := (Bij A B): modal_scope.

Goal ∀A B, ⊢ □(A → B) → (□A → □B).
Proof.
  intros A B. unfold is_theorem. intro x. simpl st.
  intro h. intro hA. intro y. intro hR.
  apply (h y hR). clear h. exact (hA y hR). 
Qed.

Goal ∀A B, ⊢ □(A ∧ B) → □A ∧ □B.
Proof.
  intros A B. unfold is_theorem. intro x. simpl st.
  intro hAB. split.
  * intro y. intro hxy. exact (proj1 (hAB y hxy)).
  * intro y. intro hxy. exact (proj2 (hAB y hxy)).
Qed.

Goal ∀A, ⊢ □A ↔ ¬◇¬A.
Proof.
  intro A. unfold is_theorem. intro x. simpl st.
  split.
  * intro h. intro hn. destruct hn as (y, (hR, hnA)).
    apply hnA. exact (h y hR).
  * intro hn. intro y. intro hR. apply DNE.
    intro hnA.
    set (P := fun y => R x y ∧ ¬st y A).
    assert (h := ex_intro P y (conj hR hnA)).
    exact (hn h). 
Qed.

