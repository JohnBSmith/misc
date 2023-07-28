
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
  * intro h.
    destruct (intersection_elim h) as (hA, hB).
    apply intersection_intro.
    exact (conj hB hA).
  * intro h.
    destruct (intersection_elim h) as (hB, hA).
    apply intersection_intro.
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

Theorem union_comm (A B: set):
  A ∪ B = B ∪ A.
Proof.
  apply set_ext. intro x. split.
  * intro h. apply union_elim in h. apply union_intro.
    destruct h as [hA | hB].
    - right. exact hA.
    - left. exact hB.
  * intro h. apply union_elim in h. apply union_intro.
    destruct h as [hB | hA].
    - right. exact hB.
    - left. exact hA.
Qed.

Theorem union_assoc (A B C: set):
  A ∪ (B ∪ C) = (A ∪ B) ∪ C.
Proof.
  apply set_ext. intro x. split.
  * intro h. apply union_elim in h. apply union_intro.
    destruct h as [hA | hBC].
    - left. apply union_intro. left. exact hA.
    - apply union_elim in hBC.
      destruct hBC as [hB | hC].
      -- left. apply union_intro. right. exact hB.
      -- right. exact hC.
  * intro h. apply union_elim in h. apply union_intro.
    destruct h as [hAB | hC].
    - apply union_elim in hAB.
      destruct hAB as [hA | hB].
      -- left. exact hA.
      -- right. apply union_intro. left. exact hB.
    - right. apply union_intro. right. exact hC.
Qed.

Theorem intersection_is_subset (A B: set):
  A ∩ B ⊆ A.
Proof.
  unfold Subset. intro x. intro h. apply sep in h.
  exact (proj1 h).
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

Theorem subset_of_union (A B: set):
  A ⊆ A ∪ B.
Proof.
  unfold Subset. intro x. intro h.
  apply union_intro. left. exact h.
Qed.

Theorem subset_as_union_eq (A B: set):
  A ⊆ B ↔ A ∪ B = B.
Proof.
  split.
  * intro h. apply set_ext. intro x. split.
    - intro hAB. apply union_elim in hAB.
      destruct hAB as [hA | hB].
      -- unfold Subset in h. exact (h x hA).
      -- exact hB.
    - intro hB. apply union_intro. right. exact hB.
  * intro h. unfold Subset. intro x. intro hA.
    rewrite <- h. apply union_intro. left. exact hA.
Qed.

Theorem diff_self_is_empty (A: set):
  A \ A = ∅.
Proof.
  apply set_ext. intro x. split.
  * intro h. apply sep in h. destruct h as (hA, hnA).
    exfalso. exact (hnA hA).
  * intro h. exfalso. apply (empty_set_axiom x).
    exact h.
Qed.

Theorem diff_empty_set (A: set):
  A \ ∅ = A.
Proof.
  apply set_ext. intro x. split.
  * intro h. apply sep in h. exact (proj1 h).
  * intro h. apply sep. split.
    - exact h.
    - exact (empty_set_axiom x).
Qed.

Theorem empty_set_diff (A: set):
  ∅ \ A = ∅.
Proof.
  apply set_ext. intro x. split.
  * intro h. apply sep in h. exact (proj1 h).
  * intro h. apply sep. split.
    - exact h.
    - intro hn. apply (empty_set_axiom x).
      exact h.
Qed.

Theorem contraposition {A B: Prop}:
  (A → B) → (¬B → ¬A).
Proof.
  intro h. intro hnB. intro hA.
  exact (hnB (h hA)).
Qed.

Theorem subset_contra (U A B: set):
  A ⊆ U ∧ B ⊆ U → (A ⊆ B ↔ U \ B ⊆ U \ A).
Proof.
  intros (hAU, hBU).
  split.
  * unfold Subset. intro h. intro x. intro hx.
    apply sep. apply sep in hx. split.
    - exact (proj1 hx).
    - destruct hx as (hxU, hxnB).
      apply (contraposition (h x)). exact hxnB.
  * unfold Subset. intro h. intro x. intro hx.
    apply NNPP. intro hnB. assert (hU := hAU x hx).
    assert (hUnB := (conj hU hnB)).
    assert (hUnB' := diff_intro hUnB).
    assert (hUnA := h x hUnB').
    apply diff_elim in hUnA.
    apply (proj2 hUnA). exact hx.
Qed.

Theorem intersection_diff (A B C: set):
  (A ∩ B) \ C = (A \ C) ∩ (B \ C).
Proof.
  apply set_ext. intro x. split.
  * intro h. apply diff_elim in h. destruct h as (hAB, hnC).
    apply intersection_elim in hAB. destruct hAB as (hA, hB).
    apply intersection_intro. split.
    - apply diff_intro. exact (conj hA hnC).
    - apply diff_intro. exact (conj hB hnC).
  * intro h. apply intersection_elim in h.
    destruct h as (hAnC, hBnC).
    destruct (diff_elim hAnC) as (hA, hnC).
    destruct (diff_elim hBnC) as (hB, _).
    apply diff_intro. split.
    - apply intersection_intro. exact (conj hA hB).
    - exact hnC.
Qed.

Theorem subset_diff (A B C: set):
  A ⊆ B -> A \ C ⊆ B \ C.
Proof.
  unfold Subset. intro h. intro x. intro hx.
  destruct (diff_elim hx) as (hA, hnC).
  apply diff_intro. split.
  * exact (h x hA).
  * exact hnC.
Qed.

