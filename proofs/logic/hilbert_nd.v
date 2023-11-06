
(* An embedding of natural deduction *)
(* in Hilbert calculus *)

Require Import Coq.Unicode.Utf8.

Inductive Var := var: nat → Var.

Inductive Formula: Set :=
| Atom: Var → Formula
| FF: Formula
| TF: Formula
| Neg: Formula → Formula
| Conj: Formula → Formula → Formula
| Disj: Formula → Formula → Formula
| Impl: Formula → Formula → Formula
| Equi: Formula → Formula → Formula.

Declare Scope formula_scope.
Bind Scope formula_scope with Formula.

Notation "⊥" := FF (at level 0): formula_scope.
Notation "¬ A" := (Neg A): formula_scope.
Notation "A ∧ B" := (Conj A B): formula_scope.
Notation "A ∨ B" := (Disj A B): formula_scope.
Notation "A → B" := (Impl A B): formula_scope.
Notation "A ↔ B" := (Equi A B): formula_scope.

Inductive Th: Formula → Prop :=
| mp: ∀{A B}, Th (A → B) → Th A → Th B
| ax_basic: ∀A, Th (A → A)
| ax_th_wk: ∀H A, Th (A → H → A)
| ax_impl_intro: ∀H A B, Th ((H ∧ A → B) → (H → A → B))
| ax_impl_elim: ∀H A B, Th ((H → A → B) → (H → A) → (H → B))
| ax_neg_intro: ∀A, Th ((A → ⊥) → ¬A)
| ax_neg_elim: ∀A, Th (¬A → A → ⊥)
| ax_conj_intro: ∀A B, Th (A → B → A ∧ B)
| ax_conj_eliml: ∀A B, Th (A ∧ B → A)
| ax_conj_elimr: ∀A B, Th (A ∧ B → B)
| ax_disj_introl: ∀A B, Th (A → A ∨ B)
| ax_disj_intror: ∀A B, Th (B → A ∨ B)
| ax_disj_elim: ∀A B C, Th (A ∨ B → (A → C) → (B → C) → C)
| ax_equi_intro: ∀A B, Th ((A → B) → (B → A) → (A ↔ B))
| ax_equi_eliml: ∀A B, Th ((A ↔ B) → (A → B))
| ax_equi_elimr: ∀A B, Th ((A ↔ B) → (B → A))
| ax_dne: ∀A, Th(¬¬A → A).

Notation "⊢ A" := (Th A) (at level 100).

Theorem theorem_weakening H {A}:
  (⊢ A) → (⊢ H → A).
Proof.
  intro h1. assert (h2 := ax_th_wk H A).
  exact (mp h2 h1).
Qed.

Theorem impl_intro {H A B}:
  (⊢ H ∧ A → B) → (⊢ H → (A → B)).
Proof.
  intro h1.
  assert (h2 := ax_impl_intro H A B).
  exact (mp h2 h1).
Qed.

Theorem impl_elim {H A B}:
  (⊢ H → A → B) → (⊢ H → A) → (⊢ H → B).
Proof.
  intros h1 h2.
  assert (h3 := ax_impl_elim H A B).
  assert (h4 := mp h3 h1).
  exact (mp h4 h2).
Qed.

Theorem lift1 {H A B}:
  (⊢ A → B) → (⊢ H → A) → (⊢ H → B).
Proof.
  intros h1 h2.
  assert (h3 := theorem_weakening H h1).
  exact (impl_elim h3 h2).
Qed.

Theorem lift2 {H A B C}:
  (⊢ A → B → C) → (⊢ H → A) → (⊢ H → B) → (⊢ H → C).
Proof.
  intros h1 h2 h3.
  assert (h4 := theorem_weakening H h1).
  assert (h5 := impl_elim h4 h2).
  exact (impl_elim h5 h3).
Qed.

Theorem neg_intro {H A}:
  (⊢ H ∧ A → ⊥) → (⊢ H → ¬A).
Proof.
  intro h1.
  assert (h2 := impl_intro h1).
  exact (lift1 (ax_neg_intro A) h2).
Qed.

Theorem neg_elim {H A}:
  (⊢ H → ¬A) → (⊢ H → A) → (⊢ H → ⊥).
Proof.
  exact (lift2 (ax_neg_elim A)).
Qed.

Theorem conj_intro {H A B}:
  (⊢ H → A) → (⊢ H → B) → (⊢ H → A ∧ B).
Proof.
  exact (lift2 (ax_conj_intro A B)).
Qed.

Theorem conj_eliml {H A B}:
  (⊢ H → A ∧ B) → (⊢ H → A).
Proof.
  exact (lift1 (ax_conj_eliml A B)).
Qed.

Theorem conj_elimr {H A B}:
  (⊢ H → A ∧ B) → (⊢ H → B).
Proof.
  exact (lift1 (ax_conj_elimr A B)).
Qed.

Theorem disj_introl {H A B}:
  (⊢ H → A) → (⊢ H → A ∨ B).
Proof.
  exact (lift1 (ax_disj_introl A B)).
Qed.

Theorem disj_intror {H A B}:
  (⊢ H → B) → (⊢ H → A ∨ B).
Proof.
  exact (lift1 (ax_disj_intror A B)).
Qed.

Theorem disj_elim {H A B C}:
 (⊢ H → A ∨ B) → (⊢ H ∧ A → C) → (⊢ H ∧ B → C) → (⊢ H → C).
Proof.
  intros h1 h2 h3.
  assert (h4 := impl_intro h2).
  assert (h5 := impl_intro h3).
  assert (h6 := ax_disj_elim A B C).
  assert (h7 := theorem_weakening H h6).
  clear h2 h3 h6.
  assert (h8 := impl_elim h7 h1).
  assert (h9 := impl_elim h8 h4).
  exact (impl_elim h9 h5).
Qed.

Theorem equi_intro {H A B}:
  (⊢ H → A → B) → (⊢ H → B → A) → (⊢ H → (A ↔ B)).
Proof.
  exact (lift2 (ax_equi_intro A B)).
Qed.

Theorem equi_eliml {H A B}:
  (⊢ H → (A ↔ B)) → (⊢ H → A → B).
Proof.
  exact (lift1 (ax_equi_eliml A B)).
Qed.

Theorem equi_elimr {H A B}:
  (⊢ H → (A ↔ B)) → (⊢ H → B → A).
Proof.
  exact (lift1 (ax_equi_elimr A B)).
Qed.

Theorem dne {H A}:
  (⊢ H → ¬¬A) → (⊢ H → A).
Proof.
  exact (lift1 (ax_dne A)).
Qed.

(* Example proof *)
Theorem contraposition A B:
  ⊢ (A → B) → (¬B → ¬A).
Proof.
  apply impl_intro.
  apply neg_intro.
  assert (h := ax_basic (((A → B) ∧ ¬ B) ∧ A)).
  assert (hA := conj_elimr h).
  assert (hAB := (conj_eliml (conj_eliml h))).
  assert (hB := (impl_elim hAB hA)).
  assert (hnB := conj_elimr (conj_eliml h)).
  exact (neg_elim hnB hB).
Qed.
