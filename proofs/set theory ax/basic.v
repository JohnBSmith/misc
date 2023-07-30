
Load "logic.v".
Load "axioms.v".

(* Subset relation is a partial order *)

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

(* Properties of the subset relation *)

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
  apply union2_intro. left. exact h.
Qed.

Theorem subset_as_union_eq (A B: set):
  A ⊆ B ↔ A ∪ B = B.
Proof.
  split.
  * intro h. apply set_ext. intro x. split.
    - intro hAB. apply union2_elim in hAB.
      destruct hAB as [hA | hB].
      -- unfold Subset in h. exact (h x hA).
      -- exact hB.
    - intro hB. apply union2_intro. right. exact hB.
  * intro h. unfold Subset. intro x. intro hA.
    rewrite <- h. apply union2_intro. left. exact hA.
Qed.

(* Properties of the empty set *)

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

(* Boolean algebra *)

Theorem intersection2_idem (A: set):
  A ∩ A = A.
Proof.
  apply set_ext. intro x. split.
  * intro h. apply intersection2_elim in h.
    exact (proj1 h).
  * intro h. apply intersection2_intro.
    exact (conj h h).
Qed.

Theorem union2_idem (A: set):
  A ∪ A = A.
Proof.
  apply set_ext. intro x. split.
  * intro h. apply union2_elim in h.
    destruct h as [hA | hA].
    - exact hA.
    - exact hA.
  * intro h. apply union2_intro.
    left. exact h.
Qed.

Theorem intersection2_extremal (A: set):
  A ∩ ∅ = ∅.
Proof.
  apply set_ext. intro x. split.
  * intro h. apply intersection2_elim in h.
    exact (proj2 h).
  * intro h. exfalso.
    exact (empty_set_axiom x h).
Qed.

Theorem union2_extremal (A U: set):
  A ⊆ U → A ∪ U = U.
Proof.
  intro hAU. apply set_ext. intro x. split.
  * intro h. apply union2_elim in h.
    destruct h as [hA | hU].
    - unfold Subset in hAU. exact (hAU x hA).
    - exact hU.
  * intro h. apply union2_intro.
    right. exact h.
Qed.

Theorem intersection2_neutral (A U: set):
  A ⊆ U → A ∩ U = A.
Proof.
  intro hAU. apply set_ext. intro x. split.
  * intro h. apply intersection2_elim in h.
    exact (proj1 h).
  * intro h. apply intersection2_intro.
    unfold Subset in hAU.
    exact (conj h (hAU x h)).
Qed.

Theorem union2_neutral (A: set):
  A ∪ ∅ = A.
Proof.
  apply set_ext. intro x. split.
  * intro h. apply union2_elim in h.
    destruct h as [hA | hempty].
    - exact hA.
    - exfalso.
      exact (empty_set_axiom x hempty).
  * intro h. apply union2_intro.
    left. exact h.
Qed.

Theorem intersection2_compl (A U: set):
  A ∩ (U \ A) = ∅.
Proof.
  apply set_ext. intro x. split.
  * intro h. apply intersection2_elim in h.
    destruct h as (hA, hUA).
    apply diff_elim in hUA.
    destruct hUA as (hU, hnA).
    exfalso. exact (hnA hA).
  * intro h. exfalso.
    exact (empty_set_axiom x h).
Qed.

Theorem union2_compl (A U: set):
  A ⊆ U → A ∪ (U \ A) = U.
Proof.
  intro hAU. apply set_ext. intro x. split.
  * intro h. apply union2_elim in h.
    destruct h as [hA | hUA].
    - unfold Subset in hAU.
      exact (hAU x hA).
    - apply diff_elim in hUA.
      exact (proj1 hUA).
  * intro h. apply union2_intro.
    destruct (classic (x ∈ A)) as [hA | hnA].
    - left. exact hA.
    - right. apply diff_intro.
      exact (conj h hnA).
Qed.

Theorem intersection2_comm (A B: set):
  A ∩ B = B ∩ A.
Proof.
  apply set_ext. intro x. split.
  * intro h.
    destruct (intersection2_elim h) as (hA, hB).
    apply intersection2_intro.
    exact (conj hB hA).
  * intro h.
    destruct (intersection2_elim h) as (hB, hA).
    apply intersection2_intro.
    exact (conj hA hB).
Qed.

Theorem intersection2_assoc (A B C: set):
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

Theorem union2_comm (A B: set):
  A ∪ B = B ∪ A.
Proof.
  apply set_ext. intro x. split.
  * intro h. apply union2_elim in h. apply union2_intro.
    destruct h as [hA | hB].
    - right. exact hA.
    - left. exact hB.
  * intro h. apply union2_elim in h. apply union2_intro.
    destruct h as [hB | hA].
    - right. exact hB.
    - left. exact hA.
Qed.

Theorem union2_assoc (A B C: set):
  A ∪ (B ∪ C) = (A ∪ B) ∪ C.
Proof.
  apply set_ext. intro x. split.
  * intro h. apply union2_elim in h. apply union2_intro.
    destruct h as [hA | hBC].
    - left. apply union2_intro. left. exact hA.
    - apply union2_elim in hBC.
      destruct hBC as [hB | hC].
      -- left. apply union2_intro. right. exact hB.
      -- right. exact hC.
  * intro h. apply union2_elim in h. apply union2_intro.
    destruct h as [hAB | hC].
    - apply union2_elim in hAB.
      destruct hAB as [hA | hB].
      -- left. exact hA.
      -- right. apply union2_intro. left. exact hB.
    - right. apply union2_intro. right. exact hC.
Qed.

Theorem intersection2_de_Morgan (U A B: set):
  U \ (A ∩ B) = (U \ A) ∪ (U \ B).
Proof.
  apply set_ext. intro x. split.
  * intro h. apply diff_elim in h.
    destruct h as (hU, hAB). apply union2_intro.
    apply (contraposition (@intersection2_intro A B x)) in hAB.
    apply conj_de_Morgan in hAB.
    destruct hAB as [hA | hB].
    - left.  apply diff_intro. exact (conj hU hA).
    - right. apply diff_intro. exact (conj hU hB).
  * intro h. apply union2_elim in h.
    apply diff_intro.
    destruct h as [hUA | hUB].
    - apply diff_elim in hUA.
      destruct hUA as (hU, hnA).
      split.
      -- exact hU.
      -- intro hAB. apply intersection2_elim in hAB.
         exact (hnA (proj1 hAB)).
    - apply diff_elim in hUB.
      destruct hUB as (hU, hnB).
      split.
      -- exact hU.
      -- intro hAB. apply intersection2_elim in hAB.
         exact (hnB (proj2 hAB)).
Qed.

Theorem union2_de_Morgan (U A B: set):
  U \ (A ∪ B) = (U \ A) ∩ (U \ B).
Proof.
  apply set_ext. intro x. split.
  * intro h. apply diff_elim in h.
    destruct h as (hU, hAB).
    apply (contraposition (@union2_intro A B x)) in hAB.
    apply disj_de_Morgan in hAB.
    destruct hAB as (hnA, hnB).
    apply intersection2_intro. split.
    - apply diff_intro. exact (conj hU hnA).
    - apply diff_intro. exact (conj hU hnB).
  * intro h. apply intersection2_elim in h.
    destruct h as (hUA, hUB).
    apply diff_elim in hUA. destruct hUA as (hU, hnA).
    apply diff_elim in hUB. destruct hUB as (_,  hnB).
    apply diff_intro. split.
    - exact hU.
    - intro hAB. apply union2_elim in hAB.
      destruct hAB as [hA | hB].
      -- exact (hnA hA).
      -- exact (hnB hB).
Qed.

Theorem intersection2_dl (A B C: set):
  A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C).
Proof.
  apply set_ext. intro x. split.
  * intro h. apply intersection2_elim in h.
    destruct h as (hA, hBC).
    apply union2_elim in hBC.
    apply union2_intro. destruct hBC as [hB | hC].
    - left. apply intersection2_intro.
      exact (conj hA hB).
    - right. apply intersection2_intro.
      exact (conj hA hC).
  * intro h. apply union2_elim in h.
    apply intersection2_intro.
    destruct h as [hAB | hAC].
    - apply intersection2_elim in hAB. split.
      -- exact (proj1 hAB).
      -- apply union2_intro. left.
         exact (proj2 hAB).
    - apply intersection2_elim in hAC. split.
      -- exact (proj1 hAC).
      -- apply union2_intro. right.
         exact (proj2 hAC).
Qed.

Theorem union2_dl (A B C: set):
  A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C).
Proof.
  apply set_ext. intro x. split.
  * intro h. apply union2_elim in h.
    apply intersection2_intro.
    destruct h as [hA | hBC].
    - split.
      -- apply union2_intro. left. exact hA.
      -- apply union2_intro. left. exact hA.
    - apply intersection2_elim in hBC.
      destruct hBC as (hB, hC).
      split.
      -- apply union2_intro. right. exact hB.
      -- apply union2_intro. right. exact hC.
  * intro h. apply intersection2_elim in h.
    destruct h as (hAB, hAC).
    apply union2_elim in hAB.
    apply union2_elim in hAC.
    apply union2_intro.
    destruct hAB as [hA | hB].
    - left. exact hA.
    - destruct hAC as [hA | hC].
      -- left. exact hA.
      -- right. apply intersection2_intro.
         exact (conj hB hC).
Qed.

(* Properties of the difference operation *)
(* and complement operation *)

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
    apply intersection2_elim in hAB. destruct hAB as (hA, hB).
    apply intersection2_intro. split.
    - apply diff_intro. exact (conj hA hnC).
    - apply diff_intro. exact (conj hB hnC).
  * intro h. apply intersection2_elim in h.
    destruct h as (hAnC, hBnC).
    destruct (diff_elim hAnC) as (hA, hnC).
    destruct (diff_elim hBnC) as (hB, _).
    apply diff_intro. split.
    - apply intersection2_intro. exact (conj hA hB).
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

