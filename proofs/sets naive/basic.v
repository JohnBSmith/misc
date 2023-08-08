
Load "axioms.v".

Theorem subset_refl A:
  A ⊆ A.
Proof.
  unfold Subset. intro x. intro h. exact h.
Qed.

Theorem subset_antisym A B:
  A ⊆ B ∧ B ⊆ A → A = B.
Proof.
  intros (hAB, hBA).
  unfold Subset in hAB.
  unfold Subset in hBA.
  apply set_ext. intro x.
  split.
  * intro h. exact (hAB x h).
  * intro h. exact (hBA x h).
Qed.

Theorem subset_trans A B C:
  A ⊆ B ∧ B ⊆ C → A ⊆ C.
Proof.
  intros (hAB, hBC). unfold Subset.
  unfold Subset in hAB.
  unfold Subset in hBC.
  intro x. intro h.
  apply (hBC x).
  apply (hAB x).
  exact h.
Qed.

Theorem intersection2_com A B:
  A ∩ B = B ∩ A.
Proof.
  apply set_ext. intro x. split.
  * intro h. apply intersection2_intro.
    apply intersection2_elim in h.
    exact (conj (proj2 h) (proj1 h)).
  * intro h. apply intersection2_intro.
    apply intersection2_elim in h.
    exact (conj (proj2 h) (proj1 h)).
Qed.

Theorem intersection2_idem A:
  A ∩ A = A.
Proof.
  apply set_ext. intro x. split.
  * intro h. apply intersection2_elim in h.
    exact (proj1 h).
  * intro h. apply intersection2_intro.
    exact (conj h h).
Qed.

Theorem intersection2_extremal A:
  A ∩ ∅ = ∅.
Proof.
  apply set_ext. intro x. split.
  * intro h. apply intersection2_elim in h.
    exact (proj2 h).
  * intro h. exfalso.
    exact (empty_set_axiom x h).
Qed.

Theorem intersection2_neutral U A:
  A ⊆ U → A ∩ U = A.
Proof.
  intro hAU. apply set_ext. intro x. split.
  * intro h. apply intersection2_elim in h.
    exact (proj1 h).  
  * intro h. apply intersection2_intro.
    unfold Subset in hAU.
    exact (conj h (hAU x h)).
Qed.

Theorem intersection2_compl (A U: set):
  A ∩ (U \ A) = ∅.
Proof.
  apply set_ext. intro x. split.
  * intro h. apply intersection2_elim in h.
    destruct h as (hA, hUA).
    apply set_diff_elim in hUA.
    destruct hUA as (hU, hnA).
    exfalso. exact (hnA hA).
  * intro h. exfalso.
    exact (empty_set_axiom x h).
Qed.

Theorem intersection2_assoc A B C:
  A ∩ (B ∩ C) = (A ∩ B) ∩ C.
Proof.
  apply set_ext. intro x. split.
  * intro h. apply intersection2_elim in h.
    destruct h as (hA, hBC).
    apply intersection2_elim in hBC.
    destruct hBC as (hB, hC).
    apply intersection2_intro. split.
    - apply intersection2_intro.
      exact (conj hA hB).
    - exact hC.
  * intro h. apply intersection2_elim in h.
    destruct h as (hAB, hC).
    apply intersection2_elim in hAB.
    destruct hAB as (hA, hB).
    apply intersection2_intro. split.
    - exact hA.
    - apply intersection2_intro.
      exact (conj hB hC).
Qed.

Theorem intersection2_intersection M N:
  ⋂ M ∩ ⋂ N ⊆ ⋂ (M ∩ N).
Proof.
  unfold Subset. intro x.
  intro h. apply intersection2_elim in h.
  destruct h as (hM, _).
  apply intersection_intro. intro A.
  intro hA. apply intersection2_elim in hA.
  destruct hA as (hAM, _).
  exact (intersection_elim M x hM A hAM).
Qed.

Theorem intersection2_set_intersection A M:
  A ∩ ⋂ M ⊆ ⋂ (A ∩ M).
Proof.
  unfold Subset. intro x.
  intro h. apply intersection2_elim in h.
  destruct h as (hA, hM).
  apply intersection_intro. intro B. intro hB.
  apply intersection2_elim in hB.
  destruct hB as (hBA, hBM).
  exact (intersection_elim M x hM B hBM).
Qed.

