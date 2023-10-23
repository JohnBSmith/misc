
Require Import Coq.Unicode.Utf8.
Require Import axioms.
Require Import basic.
Require Import mappings.

Definition closure_system U S :=
  U ∈ S ∧ ∀T, T ⊆ S → T ≠ ∅ → ⋂T ∈ S.

Definition closure S B :=
  ⋂{A | B ⊆ A ∧ A ∈ S}.

Definition closure_op U H :=
  (∀B, B ⊆ U → B ⊆ H B) ∧
  (∀B1 B2, B1 ⊆ U → B2 ⊆ U → B1 ⊆ B2 → H B1 ⊆ H B2) ∧
  (∀B, B ⊆ U → H (H B) ⊆ H B).

Definition sys U cl :=
  {A | ∃B, B ⊆ U ∧ A = cl B}.

Theorem extensivity S:
  let cl := closure S in
    ∀B, B ⊆ cl B.
Proof.
  intro cl. intro B.
  unfold subclass. intros x hx.
  unfold cl. unfold closure. apply comp. split.
  * exact (set_intro hx).
  * intros A hA. apply comp_elim in hA as (hA, _).
    apply hA. exact hx.
Qed.

Theorem monotonicity S:
  let cl := closure S in
    ∀B1 B2, B1 ⊆ B2 → cl B1 ⊆ cl B2.
Proof.
  intro cl. intros B1 B2 h.
  unfold subclass. intros x hx.
  unfold cl. unfold closure. apply comp. split.
  * exact (set_intro hx).
  * intros A hA. apply comp in hA as (hsA, (hB2, hA)).
    unfold cl in hx. unfold closure in hx.
    apply comp_elim in hx. apply hx. clear hx.
    apply comp. split; [| split].
    - exact hsA.
    - unfold subclass. intros u hu.
      apply hB2. apply h. exact hu.
    - exact hA.
Qed.

Theorem closedness S U:
  let cl := closure S in
    closure_system U S → ∀B, B ⊆ U → cl (cl B) ⊆ cl B.
Proof.
  intro cl. intros (hU, hS). intros B hB.
  assert (h: cl B ∈ S). {
    unfold closure_system in hS.
    unfold cl. unfold closure.
    apply hS.
    * unfold subclass. intros x hx.
      apply comp_elim in hx. exact (proj2 hx).
    * intro heq.
      assert (hcontra: U ∈ {A | B ⊆ A ∧ A ∈ S}). {
        apply comp. split; [| split].
        - exact (set_intro hU).
        - exact hB.
        - exact hU.
      }
      rewrite heq in hcontra.
      exact (empty_set_property hcontra).
  }
  unfold cl at 1. unfold closure.
  apply intersection_is_lower_bound.
  apply comp. split; [| split].
  * exact (set_intro h).
  * exact (subclass_refl (cl B)).
  * exact h.
Qed.

Theorem idempotence S U:
  let cl := closure S in
    closure_system U S → ∀B, B ⊆ U → cl (cl B) = cl B.
Proof.
  intro cl. intro hS. intros B hB.
  apply subclass_antisym. split.
  * exact (closedness S U hS B hB).
  * apply monotonicity. apply extensivity.
Qed.

Theorem closure_op_from_system S U:
  let cl := closure S in
    closure_system U S → closure_op U cl.
Proof.
  intro cl. intro hS. unfold closure_op.
  split; [| split].
  * intros B _. exact (extensivity S B).
  * intros B1 B2 _ _. exact (monotonicity S B1 B2).
  * exact (closedness S U hS).
Qed.

Theorem closure_op_equi U cl:
  (∀X, X ⊆ U → cl X ⊆ U) →
    (closure_op U cl ↔
    (∀A B, A ⊆ U → B ⊆ U → (A ⊆ cl B ↔ cl A ⊆ cl B))).
Proof.
  intro hcod. split.
  * intro h. intros A B hAU hBU. split.
    - intro hA. unfold closure_op in h.
      destruct h as (h1, (h2, h3)).
      apply (h2 A _ hAU (hcod B hBU)) in hA.
      exact (subclass_trans (conj hA (h3 B hBU))).
    - intro h1. unfold closure_op in h.
      destruct h as (h, _).
      assert (h0 := h A hAU).
      exact (subclass_trans (conj h0 h1)).
  * intro h. unfold closure_op.
    split; [| split].
    - intros B hBU. apply (h B B hBU hBU).
      exact (subclass_refl (cl B)).
    - intros B1 B2 h1 h2 h12.
      apply -> h.
      -- assert (hsub: B2 ⊆ cl B2). {
           apply (h B2 B2 h2 h2).
           exact (subclass_refl (cl B2)).
         }
         exact (subclass_trans (conj h12 hsub)).
      -- exact h2.
      -- exact h1.
    - intros B hBU. apply -> h.
      -- exact (subclass_refl (cl B)).
      -- exact hBU.
      -- apply hcod. exact hBU.
Qed.
