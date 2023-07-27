
Load "axioms.v".

Theorem subset_refl (A: set):
  A ⊆ A.
Proof.
  unfold Subset. intro x. intro hx. exact hx.
Qed.

Theorem subset_antisymm (A B: set):
  A ⊆ B ∧ B ⊆ A → A = B.
Proof.
  unfold Subset. intros (hAB, hBA).
  apply set_ext. intro x.
  exact (conj (hAB x) (hBA x)).
Qed.

Theorem subset_trans (A B C: set):
  A ⊆ B ∧ B ⊆ C → A ⊆ C.
Proof.
  unfold Subset. intros (hAB, hBC).
  intro x. intro hx.
  exact (hBC x (hAB x hx)). 
Qed.

Theorem emtpy_set_is_unique (A: set):
  (∀x, x ∉ A) → A = ∅.
Proof.
  intro h. apply set_ext. intro x.
  assert (hx := h x).
  split.
  * intro hA. exfalso. exact (hx hA).
  * intro hx_empty. exfalso.
    apply (empty_set_axiom x).
    exact hx_empty.
Qed.

Theorem empty_set_subset_all:
  ∀A, ∅ ⊆ A.
Proof.
  intro A. unfold Subset. intro x. intro hx.
  exfalso. apply (empty_set_axiom x). exact hx.
Qed.

Theorem subset_empty_iff_empty (A: set):
  A ⊆ ∅ ↔ A = ∅.
Proof.
  split.
  * intro h. apply set_ext. intro x. split.
    - intro hx. unfold Subset in h.
      exact (h x hx).
    - intro hx. exfalso.
      apply (empty_set_axiom x). exact hx.
  * intro h. replace A with ∅ by h.
    unfold Subset. intro x. intro hx. exact hx.
Qed.

Theorem intersection_comm (A B: set):
  A ∩ B = B ∩ A.
Proof.
  apply set_ext. intro x. split.
  * unfold Intersection. intro h.
    apply sep in h. apply sep.
    destruct h as (hA, hB).
    exact (conj hB hA).
  * intro h. apply sep in h. apply sep.
    destruct h as (hB, hA).
    exact (conj hA hB).
Qed.

Theorem intersection_assoc (A B C: set):
  A ∩ (B ∩ C) = (A ∩ B) ∩ C.
Proof.
  apply set_ext. intro x. split.
  * intro h. apply sep in h. destruct h as (hA, hBC).
    apply sep in hBC. destruct hBC as (hB, hC).
    apply sep. split.
    - apply sep. exact (conj hA hB).
    - exact hC.
  * intro h. apply sep in h. destruct h as (hAB, hC).
    apply sep in hAB. destruct hAB as (hA, hB).
    apply sep. split.
    - exact hA.
    - apply sep. exact (conj hB hC).
Qed.

Theorem subset_as_intersection_eq (A B: set):
  A ⊆ B ↔ A ∩ B = A.
Proof.
  split.
  * intro h. apply set_ext. intro x.
    split.
    - intro hx. apply sep in hx.
      destruct hx as (hA, hB). exact hA.
    - intro hx. apply sep. unfold Subset in h.
      exact (conj hx (h x hx)).
  * intro h. unfold Subset. intro x.
    replace A with (A ∩ B) by h.
    intro hx. apply sep in hx.
    destruct hx as (hA, hB). exact hB.
Qed.

