
Require Import Coq.Unicode.Utf8.

Inductive Var := var: nat → Var.
Parameter World: Type.
Parameter P: Var → World → Prop.
Parameter R: World → World → Prop.
Axiom DNE: forall (A: Prop), ¬¬A → A.

Definition Rrefl := ∀x, R x x.
Definition Rsym := ∀x y, R x y → R y x.
Definition Rser := ∀x, ∃y, R x y.
Definition Rtrans := ∀x y z, R x y → R y z → R x z.
Definition Reuc := ∀x y z, R x y → R x z → R y z.

Definition KT := Rrefl.
Definition KTB := Rrefl ∧ Rsym.
Definition KD := Rser.
Definition S4 := Rrefl ∧ Rtrans.
Definition S5 := Rrefl ∧ Reuc.

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
Notation "Sys ⊢ A" := (Sys → is_theorem A) (at level 110).
Notation "⊥" := FF (at level 0).
Notation "□ A" := (Nec A) (at level 75).
Notation "◇ A" := (Pos A) (at level 75).
Notation "¬ A" := (Neg A): modal_scope.
Notation "A ∧ B" := (Conj A B): modal_scope.
Notation "A ∨ B" := (Disj A B): modal_scope.
Notation "A → B" := (Impl A B): modal_scope.
Notation "A ↔ B" := (Bij A B): modal_scope.

(* Necessitation rule *)
Theorem nec: ∀A, (⊢ A) → (⊢ □A).
Proof.
  intro A. intro h. unfold is_theorem in h.
  unfold is_theorem. intro x. simpl st.
  intro y. intro hxy. exact (h y).
Qed.

(* Axiom schema K *)
Theorem ax_K: ∀A B, ⊢ □(A → B) → (□A → □B).
Proof.
  intros A B. unfold is_theorem. intro x. simpl st.
  intro h. intro hA. intro y. intro hxy.
  apply (h y hxy). clear h. exact (hA y hxy). 
Qed.

(* Axiom schema T *)
Theorem ax_T: ∀A, KT ⊢ □A → A.
Proof.
  intro A. intro hrefl. unfold is_theorem. intro x.
  simpl st. intro h. apply (h x). exact (hrefl x).
Qed.

(* Axiom schema 4 *)
Theorem ax_4: ∀A, S4 ⊢ □A → □□A.
Proof.
  intro A. intro hS4. destruct hS4 as (hrefl, htrans).
  unfold is_theorem. intro x. simpl st. intro h.
  intro y. intro hxy. intro z. intro hyz.
  apply (h z). clear h. unfold Rtrans in htrans.
  exact (htrans x y z hxy hyz).
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
  * intro h. intro hn. destruct hn as (y, (hxy, hnA)).
    apply hnA. exact (h y hxy).
  * intro hn. intro y. intro hxy. apply DNE.
    intro hnA.
    set (P := fun y => R x y ∧ ¬st y A).
    assert (h := ex_intro P y (conj hxy hnA)).
    exact (hn h). 
Qed.

