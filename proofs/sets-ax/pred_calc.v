
Require Import Coq.Unicode.Utf8.
Require Import axioms.

Theorem neg_ex {A: Class → Prop}:
  ¬(∃x, A x) → ∀x, ¬A x.
Proof.
  intro h. intro x. intro hx.
  apply h. exists x. exact hx.
Qed.
