
Require Import Coq.Unicode.Utf8.
Require Import axioms.
Require Import basic.
Require Import mappings.

Definition closure_system U S :=
  U ∈ S ∧ ∀T, T ⊆ S → T ≠ ∅ → ⋂T ∈ S.

Definition closure S B :=
  ⋂{A | B ⊆ A ∧ A ∈ S}.

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
