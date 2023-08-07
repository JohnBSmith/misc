
(* Proof of the deduction theorem for the *)
(* Hilbert system of minimal logic. *)

Require Import Coq.Unicode.Utf8.
Require Import Coq.Sets.Constructive_sets.

(* Type of atomic variables, one variable *)
(* for each natural number. *)
Inductive Var := var: nat → Var.
 
(* Recursive definition of the type of *)
(* well-formed logical formulas. *)
Inductive Formula :=
| Atom: Var → Formula
| Impl: Formula → Formula → Formula.
 
Notation "A → B" := (Impl A B).
Notation "A ∈ Γ" := (In Formula Γ A) (at level 70).
Notation "Γ ∪ Δ" := (Union Formula Γ Δ) (at level 60).
Notation "{ A ,}" := (Singleton Formula A).

(* Recursive definition of what is understood as a proof. *)
(* The axiom schemas S, K correspond to the combinators *)
(* from combinatory logic. Rule mp is the modus ponens. *)
Inductive Provable (Γ: Ensemble Formula): Formula → Prop :=
| basic: ∀A, A ∈ Γ → Provable Γ A
| S: ∀A B C, Provable Γ ((A → B → C) → (A → B) → A → C)
| K: ∀A B, Provable Γ (A → B → A)
| mp: ∀{A B}, Provable Γ (A → B) → Provable Γ A → Provable Γ B.
 
Notation "Γ ⊢ A" := (Provable Γ A) (at level 110).
 
Theorem impl_self Γ A:
  Γ ⊢ A → A.
Proof.
  pose (B := A).
  assert (h1 := S Γ A (B → A) A).
  assert (h2 := K Γ A (B → A)).
  assert (h3 := mp Γ h1 h2).
  clear h1. clear h2.
  assert (h4 := K Γ A B).
  assert (h5 := mp Γ h3 h4).
  exact h5.
Qed.

(* Proof by structural induction on proof h. *)
Theorem deduction_theorem Γ A B:
  (Γ ∪ {A,} ⊢ B) → (Γ ⊢ A → B).
Proof.
  intro h. induction h as
  [B hB | B C D | B C | B C _ ih1 _ ih2].
  * apply Union_inv in hB.
    destruct hB as [hl | hr].
    - assert (h0 := K Γ B A).
      assert (h1 := basic Γ B hl).
      exact (mp Γ h0 h1).
    - apply Singleton_inv in hr.
      rewrite <- hr. exact (impl_self Γ A).
  * set (B' := (B → C → D) → (B → C) → B → D).
    assert (h0 := K Γ B' A).
    assert (h1 := S Γ B C D). fold B' in h1.
    exact (mp Γ h0 h1).
  * set (B' := B → C → B).
    assert (h0 := K Γ B C). fold B' in h0.
    assert (h1 := K Γ B' A).
    exact (mp Γ h1 h0).
  * assert (h0 := S Γ A B C).
    assert (h1 := mp Γ h0 ih1).
    assert (h2 := mp Γ h1 ih2).
    exact h2.
Qed.
