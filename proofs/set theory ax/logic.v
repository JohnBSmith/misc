
Require Import Coq.Unicode.Utf8.
Require Import Coq.Logic.Classical.

Definition dne_axiom := NNPP.

(* The law of excluded middle, *)
(* lat. tertium non datur, *)
(* called 'classic' in the standard library. *)
Theorem lem (A: Prop):
  A ∨ ¬A.
Proof.
  apply dne_axiom. intro hn.
  apply hn. right. intro hA.
  apply hn. left. exact hA.
Qed.

(* Ex falso quodlibet *)
Theorem efq {A: Prop}:
  False → A.
Proof.
  intro h. apply dne_axiom.
  intro h0. exact h.
Qed.

Theorem contraposition {A B: Prop}:
  (A → B) → (¬B → ¬A).
Proof.
  intro h. intro hnB. intro hA.
  exact (hnB (h hA)).
Qed.

Theorem contraposition_reverse {A B: Prop}:
  (¬B → ¬A) → (A → B).
Proof.
  intro h. intro hA.
  apply dne_axiom. intro hnB.
  exact (h hnB hA).
Qed.

Theorem contraposition_eq {A B: Prop}:
  (A → B) ↔ (¬B → ¬A).
Proof.
  split.
  * exact contraposition.
  * exact contraposition_reverse.
Qed.

(* Alternative proof by applying the *)
(* law of excluded middle and *)
(* ex falso quodlibet *)
Goal ∀(A B: Prop), (¬B → ¬A) → (A → B).
Proof.
  intros A B. intro h. intro hA.
  destruct (lem B) as [hB | hnB].
  * exact hB. 
  * apply efq. exact ((h hnB) hA).
Qed.

Theorem conj_de_Morgan {A B: Prop}:
  ¬(A ∧ B) ↔ ¬A ∨ ¬B.
Proof.
  split.
  * intro h. destruct (lem A) as [hA | hnA].
    - destruct (lem B) as [hB | hnB].
      -- apply efq. exact (h (conj hA hB)).
      -- right. exact hnB.
    - left. exact hnA.
  * intro h. intro hAB. destruct hAB as (hA, hB).
    destruct h as [hnA | hnB].
    - exact (hnA hA).
    - exact (hnB hB).
Qed.

Theorem disj_de_Morgan {A B: Prop}:
  ¬(A ∨ B) ↔ ¬A ∧ ¬B.
Proof.
  split.
  * intro h. split.
    - intro hA. apply h. left.  exact hA.
    - intro hB. apply h. right. exact hB.
  * intro h. destruct h as (hnA, hnB).
    intro hAB. destruct hAB as [hA | hB].
    - exact (hnA hA).
    - exact (hnB hB).
Qed.

Theorem disj_idem {A: Prop}:
  A ∨ A → A.
Proof.
  intro h. destruct h as [hl | hr].
  * exact hl.
  * exact hr.
Qed.

Theorem disj_idem_eq {A: Prop}:
  A ∨ A ↔ A.
Proof.
  split.
  * intro h. destruct h as [hl | hr].
    - exact hl.
    - exact hr.
  * intro h. left. exact h.
Qed.
