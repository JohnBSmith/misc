
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

Theorem union2_idem A:
  A ∪ A = A.
Proof.
  apply set_ext. intro x. split.
  * intro h. apply union2_elim in h.
    destruct h as [hl | hr].
    - exact hl.
    - exact hr.
  * intro h. apply union2_intro.
    left. exact h.
Qed.

Theorem union2_com A B:
  A ∪ B = B ∪ A.
Proof.
  apply set_ext. intro x. split.
  * intro h. apply union2_elim in h.
    apply union2_intro.
    destruct h as [hA | hB].
    - right. exact hA.
    - left. exact hB.
  * intro h. apply union2_elim in h.
    apply union2_intro.
    destruct h as [hB | hA].
    - right. exact hB.
    - left. exact hA.
Qed.

Theorem union2_neutral A:
  A ∪ ∅ = A.
Proof.
  apply set_ext. intro x. split.
  * intro h. apply union2_elim in h.
    destruct h as [hA | hF].
    - exact hA.
    - exfalso. apply empty_set_axiom in hF.
      exact hF.
  * intro h. apply union2_intro.
    left. exact h.
Qed.

Theorem union2_extremal U A:
  A ⊆ U → A ∪ U = U.
Proof.
  intro hAU. apply set_ext. intro x. split.
  * intro h. apply union2_elim in h.
    destruct h as [hA | hU].
    - unfold Subset in hAU.
      exact (hAU x hA).
    - exact hU.
  * intro h. apply union2_intro.
    right. exact h.
Qed.

Theorem union2_compl (A U: set):
  LEM → A ⊆ U → A ∪ (U \ A) = U.
Proof.
  intro lem. intro hAU. apply set_ext.
  intro x. split.
  * intro h. apply union2_elim in h.
    destruct h as [hl | hr].
    - unfold Subset in hAU. exact (hAU x hl).
    - apply set_diff_elim in hr.
      exact (proj1 hr).
  * intro h. apply union2_intro.
    destruct (lem (x ∈ A)) as [hA | hnA].
    - left. exact hA.
    - right. apply set_diff_intro.
      exact (conj h hnA).
Qed.

Theorem union2_assoc (A B C: set):
  A ∪ (B ∪ C) = (A ∪ B) ∪ C.
Proof.
  apply set_ext. intro x. split.
  * intro h. apply union2_elim in h.
    apply union2_intro.
    destruct h as [hl | hr].
    - left. apply union2_intro. left. exact hl.
    - apply union2_elim in hr.
      destruct hr as [hB | hC].
      -- left. apply union2_intro. right. exact hB.
      -- right. exact hC.
  * intro h. apply union2_elim in h.
    apply union2_intro.
    destruct h as [hl | hr].
    - apply union2_elim in hl.
      destruct hl as [hA | hB].
      -- left. exact hA.
      -- right. apply union2_intro. left. exact hB.
    - right. apply union2_intro. right. exact hr.
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

Theorem prod_left_empty Y:
  ∅ × Y = ∅.
Proof.
  apply set_ext. intro t. split.
  * intro h. apply prod_elim in h.
    destruct h as (u, (v, (hu, (hv, huv)))).
    apply (empty_set_axiom u) in hu.
    exfalso. exact hu.
  * intro h. apply (empty_set_axiom t) in h.
    exfalso. exact h.
Qed.

Theorem prod_right_empty X:
  X × ∅ = ∅.
Proof.
  apply set_ext. intro t. split.
  * intro h. apply prod_elim in h.
    destruct h as (u, (v, (hu, (hv, huv)))).
    apply (empty_set_axiom v) in hv.
    exfalso. exact hv.
  * intro h. apply (empty_set_axiom t) in h.
    exfalso. exact h.
Qed.

Theorem prod_subset_prod A B X Y:
  A ⊆ X → B ⊆ Y → A × B ⊆ X × Y.
Proof.
  intros hAX hBY. unfold Subset. intro t. intro ht.
  apply prod_intro. apply prod_elim in ht.
  destruct ht as (x, (y, (hx, (hy, ht)))).
  exists x. exists y. repeat split.
  * unfold Subset in hAX. exact (hAX x hx).
  * unfold Subset in hBY. exact (hBY y hy).
  * exact ht.
Qed.

Theorem prod_intersection2 X A B:
  X × (A ∩ B) = (X × A) ∩ (X × B).
Proof.
  apply set_ext. intro t. split.
  * intro ht. apply intersection2_intro.
    apply prod_elim in ht.
    destruct ht as (x, (y, (hx, (hy, ht)))).
    apply intersection2_elim in hy.
    destruct hy as (hyA, hyB).
    split.
    - apply prod_intro. exists x. exists y.
      exact (conj hx (conj hyA ht)).
    - apply prod_intro. exists x. exists y.
      exact (conj hx (conj hyB ht)).
  * intro ht. apply intersection2_elim in ht.
    destruct ht as (htA, htB).
    apply prod_elim in htA. apply prod_elim in htB.
    destruct htA as (x, (y, (hx, (hy, ht)))).
    destruct htB as (x', (y', (hx', (hy', ht')))).
    rewrite ht in ht'. apply pair_eq in ht'.
    destruct ht' as (_, hyy'). clear hx'. clear x'.
    rewrite <- hyy' in hy'. clear hyy'.
    apply prod_intro.
    exists x. exists y. repeat split.
    - exact hx.
    - apply intersection2_intro.
      exact (conj hy hy').
    - exact ht.
Qed.

Theorem prod_union2 X A B:
  X × (A ∪ B) = (X × A) ∪ (X × B).
Proof.
  apply set_ext. intro t. split.
  * intro ht. apply union2_intro.
    apply prod_elim in ht.
    destruct ht as (x, (y, (hx, (hy, ht)))).
    apply union2_elim in hy.
    destruct hy as [hyA | hyB].
    - left. apply prod_intro.
      exists x. exists y.
      exact (conj hx (conj hyA ht)).
    - right. apply prod_intro.
      exists x. exists y.
      exact (conj hx (conj hyB ht)).
  * intro ht. apply union2_elim in ht.
    apply prod_intro.
    destruct ht as [htA | htB].
    - apply prod_elim in htA.
      destruct htA as (x, (y, (hx, (hy, ht)))).
      exists x. exists y. repeat split.
      -- exact hx.
      -- apply union2_intro. left. exact hy.
      -- exact ht.
    - apply prod_elim in htB.
      destruct htB as (x, (y, (hx, (hy, ht)))).
      exists x. exists y. repeat split.
      -- exact hx.
      -- apply union2_intro. right. exact hy.
      -- exact ht.
Qed.
