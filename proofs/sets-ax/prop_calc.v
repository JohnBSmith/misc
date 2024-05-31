
Require Import Coq.Unicode.Utf8.
Require Import axioms.

Theorem contraposition {A B: Prop}:
  (A → B) → (¬B → ¬A).
Proof.
  intro h. intro hnB. intro hA.
  apply hnB. apply h. exact hA.
Qed.

Theorem neg_disj {A B: Prop}:
  ¬(A ∨ B) → ¬A ∧ ¬B.
Proof.
  intro h. split.
  * intro hA. apply h. left. exact hA.
  * intro hB. apply h. right. exact hB.
Qed.

Theorem neg_conj {A B: Prop}:
  ¬(A ∧ B) → ¬A ∨ ¬B.
Proof.
  intro h. apply DNE. intro hcontra.
  apply h. split.
  * apply DNE. intro hnA. apply hcontra.
    left. exact hnA.
  * apply DNE. intro hnB. apply hcontra.
    right. exact hnB.
Qed.
