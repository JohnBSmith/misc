
(* Sequent natural deduction for *)
(* classical first-order predicate logic *)

(* Shown is soundness under classical semantics. *)

Require Import Coq.Unicode.Utf8.
Require Import Coq.Sets.Constructive_sets.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.FunctionalExtensionality.

(* Syntax *)
(* ====== *)

Record Signature := {
  SigConst: Type;
  SigFun: Type;
  SigPred: Type
}.

Parameter sig: Signature.

(* The type of individual variables *)
Definition Var := nat.

Inductive Term: Type :=
| Va: Var → Term
| Const: SigConst sig → Term
| App: SigFun sig → Term → Term.

Inductive Formula: Type :=
| Atom: SigPred sig → Term → Formula
| FF: Formula
| TF: Formula
| Neg: Formula → Formula
| Conj: Formula → Formula → Formula
| Disj: Formula → Formula → Formula
| Impl: Formula →  Formula → Formula
| EQ: Var → Formula → Formula
| UQ: Var → Formula → Formula.

(* Semantics *)
(* ========= *)

(* Double negation elimination, *)
(* needed for classical semantics *)
Axiom DNE: ∀A: Prop, ¬¬A → A.

Record Structure := {
  Univ: Type;
  sconst: SigConst sig → Univ;
  sfun: SigFun sig → Univ → Univ;
  spred: SigPred sig → Univ → Prop
}.

Fixpoint eval M s t: Univ M :=
  match t with
  | Va x => s x
  | Const c => sconst M c
  | App f t => sfun M f (eval M s t)
  end.

Definition reassign M s (x: Var) (u: Univ M): Var → Univ M
  := fun v =>
  match Nat.eqb x v with
  | false => s v
  | true => u
  end.

(* Interpretation (M, s) satisfies the formula A. *)
(* M is a structure, *)
(* s assigns values to free variables. *)
Fixpoint sat M s (A: Formula) :=
  match A with
  | Atom P t => spred M P (eval M s t)
  | FF => False
  | TF => True
  | Neg A => ¬sat M s A
  | Conj A B => sat M s A ∧ sat M s B
  | Disj A B => sat M s A ∨ sat M s B
  | Impl A B => sat M s A → sat M s B
  | EQ x A => ∃u, sat M (reassign M s x u) A
  | UQ x A => ∀u, sat M (reassign M s x u) A
  end.

Notation "∅" := (Empty_set _) (at level 0).
Notation "A ∈ Γ" := (In _ Γ A) (at level 70).
Notation "A ∉ Γ" := (¬In _ Γ A) (at level 70).
Notation "{ A ,}" := (Singleton _ A) (at level 0).
Notation "A ∪ B" := (Union _ A B) (at level 50).
Notation "A \ B" := (Setminus _ A B) (at level 50).

(* Interpretation (M, s) satisfies the set Γ *)
Definition sat_set M s Γ :=
  ∀X, X ∈ Γ → sat M s X.

(* Logical consequence *)
Definition valid Γ A :=
  ∀M s, sat_set M s Γ → sat M s A.

Declare Scope formula_scope.
Bind Scope formula_scope with Formula.

Notation "⊥" := FF (at level 0).
Notation "¬ A" := (Neg A): formula_scope.
Notation "A ∧ B" := (Conj A B): formula_scope.
Notation "A ∨ B" := (Disj A B): formula_scope.
Notation "A → B" := (Impl A B): formula_scope.
Notation "Γ ⊨ A" := (valid Γ A) (at level 100).

(* Utilities *)
(* ========= *)

(* The set of free variables of a term *)
Fixpoint FV_term (t: Term): Ensemble Var :=
  match t with
  | Va x => {x,}
  | Const _ => ∅
  | App f t => FV_term t
  end.

(* The set of free variables of a formula *)
Fixpoint FV (A: Formula): Ensemble Var :=
  match A with
  | Atom P t => FV_term t
  | FF => ∅
  | TF => ∅
  | Neg A => FV A
  | Conj A B => FV A ∪ FV B
  | Disj A B => FV A ∪ FV B
  | Impl A B => FV A ∪ FV B
  | EQ x A => FV A \ {x,}
  | UQ x A => FV A \ {x,}
  end.

(* The set of bound variables of a formula *)
Fixpoint BV (A: Formula): Ensemble Var :=
  match A with
  | Atom P t => ∅
  | FF => ∅
  | TF => ∅
  | Neg A => BV A
  | Conj A B => BV A ∪ BV B
  | Disj A B => BV A ∪ BV B
  | Impl A B => BV A ∪ BV B
  | EQ x A => BV A ∪ {x,}
  | UQ x A => BV A ∪ {x,}
  end.

(* The free variables of term t are certainly *)
(* not shadowed by any quantification in A *)
Definition unshadowed t A :=
  ∀x, x ∈ FV_term(t) → x ∉ BV(A).

Definition not_in_FV x Γ :=
  ∀X, X ∈ Γ → x ∉ FV X.

(* Substitution of every occurrence of x *)
(* in term t0 by term t *)
Fixpoint subst_in_term t0 (x: Var) (t: Term) :=
  match t0 with
  | Va y => (if Nat.eqb x y then t else Va y)
  | Const c => Const c 
  | App f t1 => App f (subst_in_term t1 x t)
  end.

(* Substitution of every occurrence of x *)
(* in formula A by term t *)
Fixpoint subst A (x: Var) (t: Term) :=
  match A with
  | Atom P t0 => Atom P (subst_in_term t0 x t)
  | FF => FF
  | TF => TF
  | Neg A => Neg (subst A x t)
  | Conj A B => Conj (subst A x t) (subst B x t)
  | Disj A B => Disj (subst A x t) (subst B x t)
  | Impl A B => Impl (subst A x t) (subst B x t)
  | EQ y A => EQ y (if Nat.eqb x y then A else subst A x t)
  | UQ y A => UQ y (if Nat.eqb x y then A else subst A x t)
  end.

Theorem shadowed_reassign M s x u u0:
  reassign M (reassign M s x u0) x u
  = reassign M s x u.
Proof.
  apply functional_extensionality. intro y.
  unfold reassign.
  destruct (Nat.eq_dec x y) as [hl | hr].
  * apply Nat.eqb_eq in hl. rewrite hl. reflexivity.
  * apply Nat.eqb_neq in hr. rewrite hr. reflexivity.
Qed.

Theorem subst_in_term_eq M s t0 x t:
  eval M (reassign M s x (eval M s t)) t0
  = eval M s (subst_in_term t0 x t).
Proof.
  induction t0 as [y | c | f t0 ih].
  * simpl. unfold reassign.
    destruct (Nat.eq_dec x y) as [hl | hr].
    - apply Nat.eqb_eq in hl. rewrite hl.
      reflexivity.
    - apply Nat.eqb_neq in hr. rewrite hr.
      simpl eval. reflexivity.
  * simpl eval. reflexivity.
  * simpl eval. rewrite ih. reflexivity.
Qed.

Theorem notin_sg_elim {x y: Var}:
  x ∉ {y,} → x ≠ y.
Proof.
  intro h. intro heq. contradiction h.
  rewrite heq. apply Singleton_intro.
  reflexivity.
Qed.

Theorem eval_eq_reassign M s t y u:
  y ∉ FV_term(t) →
  eval M s t = eval M (reassign M s y u) t.
Proof.
  intro h. induction t as [x | | f t ih].
  * simpl eval. unfold reassign.
    simpl FV_term in h.
    apply notin_sg_elim in h.
    apply Nat.eqb_neq in h.
    rewrite h. reflexivity.
  * simpl eval. reflexivity.
  * simpl eval. simpl FV_term in h.
    apply ih in h. rewrite <- h.
    reflexivity.
Qed.

Theorem notin_union_bv {x A B}:
  x ∉ BV A ∪ BV B → x ∉ BV A ∧ x ∉ BV B.
Proof.
  intro h. split.
  * intro hl. contradiction h.
    apply Union_introl. exact hl.
  * intro hr. contradiction h.
    apply Union_intror. exact hr.
Qed.

Theorem unshadowed_neg t A:
  unshadowed t (¬ A) → unshadowed t A.
Proof.
  unfold unshadowed. intro h.
  simpl BV in h. exact h.
Qed.

Theorem unshadowed_conj t A B:
  unshadowed t (A ∧ B) → unshadowed t A ∧ unshadowed t B.
Proof.
  unfold unshadowed. intro h.
  simpl BV in h. split.
  * intros x hx. apply h in hx.
    apply notin_union_bv in hx.
    exact (proj1 hx).
  * intros x hx. apply h in hx.
    apply notin_union_bv in hx.
    exact (proj2 hx).
Qed.

Theorem unshadowed_disj t A B:
  unshadowed t (A ∨ B) → unshadowed t A ∧ unshadowed t B.
Proof.
  unfold unshadowed. intro h.
  simpl BV in h. split.
  * intros x hx. apply h in hx.
    apply notin_union_bv in hx.
    exact (proj1 hx).
  * intros x hx. apply h in hx.
    apply notin_union_bv in hx.
    exact (proj2 hx).
Qed.

Theorem unshadowed_impl t A B:
  unshadowed t (A → B) → unshadowed t A ∧ unshadowed t B.
Proof.
  unfold unshadowed. intro h.
  simpl BV in h. split.
  * intros x hx. apply h in hx.
    apply notin_union_bv in hx.
    exact (proj1 hx).
  * intros x hx. apply h in hx.
    apply notin_union_bv in hx.
    exact (proj2 hx).
Qed.

Theorem unshadowed_eq t y A:
  unshadowed t (EQ y A) → y ∉ FV_term(t) ∧ unshadowed t A.
Proof.
  intro h. unfold unshadowed in h.
  simpl BV in h.
  split.
  * intro hy. apply h in hy. contradiction hy.
    apply Union_intror. apply Singleton_intro.
    reflexivity.
  * unfold unshadowed. intros x hx.
    apply h in hx. intro hcontra.
    contradiction hx. apply Union_introl.
    exact hcontra.
Qed.

Theorem unshadowed_uq t y A:
  unshadowed t (UQ y A) → y ∉ FV_term(t) ∧ unshadowed t A.
Proof.
  intro h. unfold unshadowed in h.
  simpl BV in h.
  split.
  * intro hy. apply h in hy. contradiction hy.
    apply Union_intror. apply Singleton_intro.
    reflexivity.
  * unfold unshadowed. intros x hx.
    apply h in hx. intro hcontra.
    contradiction hx. apply Union_introl.
    exact hcontra.
Qed.

Theorem reassign_commutes M s x u y v: x ≠ y →
  reassign M (reassign M s x u) y v
  = reassign M (reassign M s y v) x u.
Proof.
  intro h.
  apply functional_extensionality.
  intro a.
  unfold reassign.
  destruct (Nat.eq_dec y a) as [hyl | hyr].
  * assert (hylb := hyl).
    apply Nat.eqb_eq in hylb. rewrite hylb.
    destruct (Nat.eq_dec x a) as [hxl | hxr].
    - contradiction h. rewrite hxl. rewrite hyl.
      reflexivity.
    - apply Nat.eqb_neq in hxr. rewrite hxr.
      reflexivity.
  * apply Nat.eqb_neq in hyr. rewrite hyr.
    reflexivity.
Qed.

Theorem subst_equi M A x t: unshadowed t A → 
  ∀s, sat M (reassign M s x (eval M s t)) A
  ↔ sat M s (subst A x t).
Proof.
  intro ht.
  induction A as [P | |
  | A ih
  | A ihA B ihB
  | A ihA B ihB
  | A ihA B ihB
  | y A ihA
  | y A ihA].
  * intros s. simpl sat.
    rewrite subst_in_term_eq. reflexivity.
  * intros s. simpl sat. reflexivity.
  * intros s. simpl sat. reflexivity.
  * intro s. simpl sat.  simpl BV in ht.
    apply unshadowed_neg in ht.
    rewrite ih. reflexivity. exact ht.
  * intro s. simpl sat.
    apply unshadowed_conj in ht.
    rewrite ihA. rewrite ihB. reflexivity.
    exact (proj2 ht).
    exact (proj1 ht).
  * intro s. simpl sat.
    apply unshadowed_disj in ht.
    rewrite ihA. rewrite ihB. reflexivity.
    exact (proj2 ht).
    exact (proj1 ht).
  * intro s. simpl sat.
    apply unshadowed_impl in ht.
    rewrite ihA. rewrite ihB. reflexivity.
    exact (proj2 ht).
    exact (proj1 ht).
  * intro s. simpl sat. split.
    - intros (u, hu). exists u.
      destruct (Nat.eq_dec x y) as [hl | hr].
      -- rewrite <- hl in hu.
         rewrite (shadowed_reassign M s x u) in hu.
         rewrite hl in hu.
         apply Nat.eqb_eq in hl. rewrite hl.
         exact hu.
      -- assert (hrb := hr).
         apply Nat.eqb_neq in hrb. rewrite hrb.
         apply unshadowed_eq in ht as (hyt, ht).
         apply ihA.
         --- clear ihA. exact ht.
         --- clear ihA ht.
             rewrite <- (eval_eq_reassign M s t y u hyt).
             rewrite <- reassign_commutes.
             ---- exact hu. 
             ---- exact hr.
    - intros (u, hu). exists u.
      destruct (Nat.eq_dec x y) as [hl | hr].
      -- clear ihA ht.
         rewrite hl. apply Nat.eqb_eq in hl.
         rewrite hl in hu.
         rewrite (shadowed_reassign M s y u).
         exact hu.
      -- assert (hrb := hr).
         apply Nat.eqb_neq in hrb. rewrite hrb in hu.
         apply unshadowed_eq in ht as (hyt, ht).
         apply ihA in hu.
         --- clear ihA ht.
             rewrite <- (eval_eq_reassign M s t y u hyt) in hu.
             rewrite <- reassign_commutes in hu.
             ---- exact hu.
             ---- exact hr.
         --- exact ht.
  * simpl sat. intros s. split.
    - intros h u. assert (h := h u).
      destruct (Nat.eq_dec x y) as [hl | hr].
      -- clear ihA. rewrite hl in h.
         apply Nat.eqb_eq in hl. rewrite hl.
         rewrite (shadowed_reassign M s y u) in h.
         exact h.
      -- assert (hrb := hr).
         apply Nat.eqb_neq in hrb. rewrite hrb.
         apply unshadowed_uq in ht as (hyt, ht).
         apply (ihA ht). clear ihA.
         rewrite <- (eval_eq_reassign M s t y u hyt).
         rewrite <- reassign_commutes.
         --- exact h.
         --- exact hr.
    - intros h u. assert (h := h u).
      destruct (Nat.eq_dec x y) as [hl | hr].
      -- clear ihA. rewrite hl.
         apply Nat.eqb_eq in hl. rewrite hl in h.
         rewrite (shadowed_reassign M s y u).
         exact h.
      -- assert (hrb := hr).
         apply Nat.eqb_neq in hrb. rewrite hrb in h.
         apply unshadowed_uq in ht as (hyt, ht).
         apply (ihA ht) in h. clear ihA.
         rewrite <- (eval_eq_reassign M s t y u hyt) in h.
         rewrite <- reassign_commutes in h.
         --- exact h.
         --- exact hr.
Qed.

Theorem uneq_reassign M s x u y:
  x ≠ y → s y = reassign M s x u y.
Proof.
  intro h. unfold reassign.
  apply Nat.eqb_neq in h. rewrite h.
  reflexivity.
Qed.

Theorem notin_union_elim {x A B}:
  x ∉ FV A ∪ FV B → x ∉ FV A ∧ x ∉ FV B.
Proof.
  intro h. split.
  * intro hx. contradiction h.
    apply Union_introl. exact hx.
  * intro hx. contradiction h.
    apply Union_intror. exact hx.
Qed.

Theorem notin_diff_elim {x A y}:
  x ∉ FV A \ {y,} → (x ∉ FV A ∧ x ≠ y) ∨ x = y.
Proof.
  intro h. destruct (Nat.eq_dec x y) as [hl | hr].
  * right. exact hl.
  * left. split.
    - intro hx. contradiction h. clear h.
      apply Setminus_intro.
      -- exact hx.
      -- intro h. apply Singleton_inv in h.
         symmetry in h. exact (hr h).
    - exact hr.
Qed.

Theorem reassign_non_free_term {M s x t}:
  x ∉ FV_term t → ∀u, eval M s t = eval M (reassign M s x u) t.
Proof.
  intro hx. intro u.
  induction t as [y | | f t ih].
  * simpl eval. simpl FV_term in hx.
    apply notin_sg_elim in hx.
    unfold reassign. apply Nat.eqb_neq in hx.
    rewrite hx. reflexivity.
  * simpl eval. reflexivity.
  * simpl eval. simpl FV_term in hx.
    apply ih in hx. clear ih.
    rewrite hx. reflexivity.
Qed.

Theorem reassign_non_free {M x A}:
  x ∉ FV A → ∀s u, sat M s A ↔ sat M (reassign M s x u) A.
Proof.
  intros hx.
  induction A as [P |  |
  | A ih
  | A ihA B ihB
  | A ihA B ihB
  | A ihA B ihB
  | y A ih
  | y A ih].
  * intros s u. simpl sat. induction t as [y | y | y t ih].
    - simpl eval. simpl FV in hx.
      apply notin_sg_elim in hx.
      rewrite (uneq_reassign M s x u y hx).
      reflexivity.
    - simpl eval. reflexivity.
    - clear ih. simpl FV in hx. simpl eval.
      rewrite <- (reassign_non_free_term hx).
      reflexivity.
  * intros s u. simpl sat. reflexivity.
  * intros s u. simpl sat. reflexivity.
  * intros s u. simpl FV in hx.
    simpl sat. rewrite <- (ih hx s u). reflexivity.
  * intros s u. simpl FV in hx. simpl sat.
    apply notin_union_elim in hx as (hxA, hxB).
    rewrite <- (ihA hxA s u). rewrite <- (ihB hxB s u).
    reflexivity.
  * intros s u. simpl FV in hx. simpl sat.
    apply notin_union_elim in hx as (hxA, hxB).
    rewrite <- (ihA hxA s u). rewrite <- (ihB hxB s u).
    reflexivity.
  * intros s u. simpl FV in hx. simpl sat.
    apply notin_union_elim in hx as (hxA, hxB).
    rewrite <- (ihA hxA s u). rewrite <- (ihB hxB s u).
    reflexivity.
  * intros s u. simpl FV in hx. simpl sat.
    split.
    - intro h. destruct h as (u0, hu0).
      destruct (notin_diff_elim hx) as [hl | hr].
      -- exists u0.
         assert (hequi := ih (proj1 hl) (reassign M s y u0) u).
         apply hequi in hu0. clear hequi ih.
         apply proj2 in hl.
         rewrite reassign_commutes.
         --- exact hu0.
         --- exact hl.
      -- exists u0. rewrite hr.
         rewrite shadowed_reassign. exact hu0.
    - intro h. destruct h as (u0, hu0).
      destruct (notin_diff_elim hx) as [hl | hr].
      -- exists u0.
         assert (hequi := ih (proj1 hl) (reassign M s y u0) u).
         rewrite hequi. clear hequi ih.
         apply proj2 in hl.
         rewrite reassign_commutes in hu0.
         --- exact hu0.
         --- exact hl.
      -- exists u0. rewrite hr in hu0.
         rewrite shadowed_reassign in hu0. exact hu0.
   * intros s u. simpl FV in hx. simpl sat.
     split.
     - intro h. intro u0. assert (h := h u0).
       destruct (notin_diff_elim hx) as [hl | hr].
       -- assert (hequi := ih (proj1 hl) (reassign M s y u0) u).
          apply hequi in h. clear ih hequi.
          apply proj2 in hl.
          rewrite reassign_commutes.
          --- exact h.
          --- exact hl.
       -- rewrite hr. rewrite shadowed_reassign.
          exact h.
     - intro h. intro u0. assert (h := h u0).
       destruct (notin_diff_elim hx) as [hl | hr].
       -- assert (hequi := ih (proj1 hl) (reassign M s y u0) u).
          apply hequi. clear ih hequi.
          apply proj2 in hl.
          rewrite reassign_commutes in h.
          --- exact h.
          --- exact hl.
       -- rewrite hr in h. rewrite shadowed_reassign in h.
          exact h.
Qed.

Theorem reassign_non_free_set {M s x u Γ}:
  not_in_FV x Γ →
  (sat_set M s Γ ↔ sat_set M (reassign M s x u) Γ).
Proof.
  intros hx. split.
  * intro h. unfold sat_set. intros X hX.
    unfold not_in_FV in hx. 
    assert (hx := hx X hX).
    apply (reassign_non_free hx).
    unfold sat_set in h. apply h. exact hX.
  * intro h. unfold sat_set. intros X hX.
    unfold not_in_FV in hx.
    assert (hx := hx X hX).
    unfold sat_set in h. assert (h := h X hX).
    apply (reassign_non_free hx) in h. exact h.
Qed.

(* Soundness of each inference rule *)
(* ================================ *)

Theorem uq_elim_is_sound Γ A x t:
  unshadowed t A →
  (Γ ⊨ UQ x A) → (Γ ⊨ (subst A x t)).
Proof.
  intros ht h. unfold valid. intros M s hM.
  unfold valid in h. apply h in hM. clear h.
  simpl sat in hM.
  assert (hM := hM (eval M s t)).
  apply subst_equi in hM.
  * exact hM.
  * exact ht.
Qed.

Theorem eq_intro_is_sound Γ A x t:
  unshadowed t A →
  (Γ ⊨ (subst A x t)) → (Γ ⊨ EQ x A).
Proof.
  intros ht h. unfold valid. intros M s hM.
  simpl sat. exists (eval M s t).
  unfold valid in h.
  apply subst_equi.
  * exact ht.
  * exact (h M s hM).
Qed.

Theorem uq_intro_is_sound Γ A x:
  not_in_FV x Γ → (Γ ⊨ A) → (Γ ⊨ UQ x A).
Proof.
  intros hx h. unfold valid. intros M s hM.
  simpl sat. intro u. unfold valid in h.
  apply h.
  assert (hequi := @reassign_non_free_set M s x u Γ hx).
  apply hequi. exact hM.
Qed.

Theorem eq_elim_is_sound Γ A B x:
  not_in_FV x Γ → x ∉ FV B →
  (Γ ⊨ EQ x A) → (Γ ∪ {A,} ⊨ B) → (Γ ⊨ B).
Proof.
  intros hx hxB. intros h hB.
  unfold valid. intros M s hM.
  unfold valid in h. unfold valid in hB.
  assert (h := h M s hM). simpl sat in h.
  destruct h as (u, hu).
  assert (h0 := @reassign_non_free_set M s x u Γ hx).
  assert (h1 := @reassign_non_free M x B hxB s u).
  assert (hB := hB M (reassign M s x u)).
  rewrite h1. clear h1. apply hB. clear hB.
  unfold sat_set. intros X hX.
  apply Union_inv in hX.
  destruct hX as [hl | hr].
  * rewrite h0 in hM. unfold sat_set in hM.
    apply hM. exact hl.
  * apply Singleton_inv in hr. rewrite <- hr.
    exact hu.
Qed.

Theorem basic_seq_intro_is_sound A:
  {A,} ⊨ A.
Proof.
  unfold valid. intros M s hM.
  unfold sat_set in hM. apply hM.
  apply Singleton_intro. reflexivity.
Qed.

Theorem weakening_is_sound Γ A B:
  (Γ ⊨ B) → (Γ ∪ {A,} ⊨ B).
Proof.
  intro h. unfold valid. intros M s hM.
  unfold valid in h. apply h.
  unfold sat_set. intros X hX.
  unfold sat_set in hM. apply hM.
  apply Union_introl. exact hX.
Qed.

Theorem conj_intro_is_sound Γ A B:
  (Γ ⊨ A) → (Γ ⊨ B) → (Γ ⊨ A ∧ B).
Proof.
  intros hA hB. unfold valid. intros M s. intros hM.
  unfold valid in hA. unfold valid in hB.
  assert (hA := hA M s hM).
  assert (hB := hB M s hM).
  simpl sat. exact (conj hA hB).
Qed.

Theorem conj_eliml_is_sound Γ A B:
  (Γ ⊨ A ∧ B) → (Γ ⊨ A).
Proof.
  intro h. unfold valid. intros M s. intros hM.
  unfold valid in h. apply h in hM.
  simpl sat in hM. exact (proj1 hM).
Qed.

Theorem conj_elimr_is_sound Γ A B:
  (Γ ⊨ A ∧ B) → (Γ ⊨ B).
Proof.
  intro h. unfold valid. intros M s. intros hM.
  unfold valid in h. apply h in hM.
  simpl sat in hM. exact (proj2 hM).
Qed.

Theorem disj_introl_is_sound Γ A B:
  (Γ ⊨ A) → (Γ ⊨ A ∨ B).
Proof.
  intro h. unfold valid. intros M s. intro hM.
  simpl sat. left. unfold valid in h.
  apply h. exact hM.
Qed.

Theorem disj_intror_is_sound Γ A B:
  (Γ ⊨ B) → (Γ ⊨ A ∨ B).
Proof.
  intro h. unfold valid. intros M s. intro hM.
  simpl sat. right. unfold valid in h.
  apply h. exact hM.
Qed.

Theorem sat_union {M s Γ A}:
  sat_set M s Γ → sat M s A → sat_set M s (Γ ∪ {A,}).
Proof.
  intros h1 h2. unfold sat_set. intros X hX.
  apply Union_inv in hX. destruct hX as [hl | hr].
  * unfold sat_set in h1. apply h1. exact hl.
  * apply Singleton_inv in hr. rewrite <- hr. exact h2.
Qed.

Theorem disj_elim_is_sound Γ A B C:
  (Γ ⊨ A ∨ B) → (Γ ∪ {A,} ⊨ C) → (Γ ∪ {B,} ⊨ C) → (Γ ⊨ C).
Proof.
  intros hAB hA hB. unfold valid. intros M s. intro hM.
  unfold valid in hAB. assert (h := hAB M s hM).
  simpl sat in h. destruct h as [hl | hr].
  * unfold valid in hA. apply hA.
    exact (sat_union hM hl).
  * unfold valid in hB. apply hB.
    exact (sat_union hM hr).
Qed.

Theorem impl_intro_is_sound Γ A B:
  (Γ ∪ {A,} ⊨ B) → (Γ ⊨ A → B).
Proof.
  intro h. unfold valid. intros M s hM.
  simpl sat. intro hMA.
  unfold valid in h. apply h. clear h.
  exact (sat_union hM hMA).
Qed.

Theorem impl_elim_is_sound Γ A B:
  (Γ ⊨ A → B) → (Γ ⊨ A) → (Γ ⊨ B).
Proof.
  intros hAB hA. unfold valid. intros M s hM.
  unfold valid in hAB.
  assert (hAB := hAB M s hM). simpl sat in hAB.
  apply hAB. clear hAB. unfold valid in hA.
  apply hA. exact hM.
Qed.

Theorem neg_intro_is_sound Γ A:
  (Γ ∪ {A,} ⊨ ⊥) → (Γ ⊨ ¬A).
Proof.
  intro h. unfold valid. intros M s hM.
  simpl sat. intro hA. unfold valid in h.
  simpl sat in h. apply (h M s).
  exact (sat_union hM hA).
Qed.

Theorem neg_elim_is_sound Γ A:
  (Γ ⊨ ¬A) → (Γ ⊨ A) → (Γ ⊨ ⊥).
Proof.
  intros hnA hA. unfold valid. intros M s hM.
  simpl sat. unfold valid in hnA.
  assert (hnA := hnA M s hM). simpl sat in hnA.
  unfold valid in hA.
  assert (hA := hA M s hM).
  exact (hnA hA).
Qed.

Theorem dne_is_sound Γ A:
  (Γ ⊨ ¬¬A) → (Γ ⊨ A).
Proof.
  intro h. unfold valid. intros M s. intro hM.
  apply DNE. unfold valid in h. simpl sat in h.
  apply (h M s). exact hM.
Qed.

(* Soundness of the full calculus *)
(* ============================== *)

(* The type of proofs *)
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
    Prf Γ (A ∨ B) → Prf (Γ ∪ {A,}) C → Prf (Γ ∪ {B,}) C →
    Prf Γ C
| impl_intro: ∀Γ A B,
    Prf (Γ ∪ {A,}) B → Prf Γ (A → B)
| impl_elim: ∀Γ A B,
    Prf Γ (A → B) → Prf Γ A → Prf Γ B
| neg_intro: ∀Γ A,
    Prf (Γ ∪ {A,}) ⊥ → Prf Γ (¬A)
| neg_elim: ∀Γ A,
    Prf Γ (¬A) → Prf Γ A → Prf Γ ⊥
| dne: ∀Γ A,
    Prf Γ (¬¬A) → Prf Γ A
| uq_intro: ∀Γ A x, not_in_FV x Γ →
    Prf Γ A → Prf Γ (UQ x A)
| uq_elim: ∀Γ A x t, unshadowed t A →
    Prf Γ (UQ x A) → Prf Γ (subst A x t)
| eq_intro: ∀Γ A x t, unshadowed t A →
    Prf Γ (subst A x t) → Prf Γ (EQ x A)
| eq_elim: ∀Γ A B x, not_in_FV x Γ → x ∉ FV B →
    Prf Γ (EQ x A) → Prf (Γ ∪ {A,}) B → Prf Γ B.

Notation "Γ ⊢ A" := (Prf Γ A) (at level 100).

Theorem soundness_of_natural_deduction:
  ∀Γ A, (Γ ⊢ A) → (Γ ⊨ A).
Proof.
  intros Γ A. intro h.
  induction h as [A
  | Γ A B _ ih
  | Γ A B _ ihA _ ihB
  | Γ A B _ ih
  | Γ A B _ ih
  | Γ A B _ ih
  | Γ A B _ ih
  | Γ A B C _ ih _ ihA _ ihB
  | Γ A B _ ih
  | Γ A B _ ihAB _ ihA
  | Γ A _ ih
  | Γ A _ ihnA _ ihA
  | Γ A _ ih
  | Γ A x hx _ ih
  | Γ A x t ht _ ih
  | Γ A x t ht _ ih
  | Γ A B x hx hxB _ ih1 _ ih2
  ].
  * exact (basic_seq_intro_is_sound A).
  * exact (weakening_is_sound Γ A B ih).
  * exact (conj_intro_is_sound Γ A B ihA ihB).
  * exact (conj_eliml_is_sound Γ A B ih).
  * exact (conj_elimr_is_sound Γ A B ih).
  * exact (disj_introl_is_sound Γ A B ih).
  * exact (disj_intror_is_sound Γ A B ih).
  * exact (disj_elim_is_sound Γ A B C ih ihA ihB).
  * exact (impl_intro_is_sound Γ A B ih).
  * exact (impl_elim_is_sound Γ A B ihAB ihA).
  * exact (neg_intro_is_sound Γ A ih).
  * exact (neg_elim_is_sound Γ A ihnA ihA).
  * exact (dne_is_sound Γ A ih).
  * exact (uq_intro_is_sound Γ A x hx ih).
  * exact (uq_elim_is_sound Γ A x t ht ih).
  * exact (eq_intro_is_sound Γ A x t ht ih).
  * exact (eq_elim_is_sound Γ A B x hx hxB ih1 ih2).
Qed.
