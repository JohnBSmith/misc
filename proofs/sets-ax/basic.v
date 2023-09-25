
Require Import Coq.Unicode.Utf8.
Require Import axioms.

Theorem intersection2_com A B:
  A ∩ B = B ∩ A.
Proof.
  apply ext. intro x. split.
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
  apply ext. intro x. split.
  * intro h. apply intersection2_elim in h.
    exact (proj1 h).
  * intro h. apply intersection2_intro.
    exact (conj h h).
Qed.

Theorem intersection2_extremal A:
  A ∩ ∅ = ∅.
Proof.
  apply ext. intro x. split.
  * intro h. apply intersection2_elim in h.
    exact (proj2 h).
  * intro h. exfalso.
    exact (empty_set_property h).
Qed.

Theorem intersection2_neutral U A:
  A ⊆ U → A ∩ U = A.
Proof.
  intro hAU. apply ext. intro x. split.
  * intro h. apply intersection2_elim in h.
    exact (proj1 h).  
  * intro h. apply intersection2_intro.
    unfold subclass in hAU.
    exact (conj h (hAU x h)).
Qed.

Theorem intersection2_compl A U:
  A ∩ (U \ A) = ∅.
Proof.
  apply ext. intro x. split.
  * intro h. apply intersection2_elim in h.
    destruct h as (hA, hUA).
    apply difference_elim in hUA.
    destruct hUA as (hU, hnA).
    exfalso. exact (hnA hA).
  * intro h. exfalso.
    exact (empty_set_property h).
Qed.

Theorem intersection2_assoc A B C:
  A ∩ (B ∩ C) = (A ∩ B) ∩ C.
Proof.
  apply ext. intro x. split.
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
  apply ext. intro x. split.
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
  apply ext. intro x. split.
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
  apply ext. intro x. split.
  * intro h. apply union2_elim in h.
    destruct h as [hA | hF].
    - exact hA.
    - exfalso. apply empty_set_property in hF.
      exact hF.
  * intro h. apply union2_intro.
    left. exact h.
Qed.

Theorem union2_extremal U A:
  A ⊆ U → A ∪ U = U.
Proof.
  intro hAU. apply ext. intro x. split.
  * intro h. apply union2_elim in h.
    destruct h as [hA | hU].
    - unfold subclass in hAU.
      exact (hAU x hA).
    - exact hU.
  * intro h. apply union2_intro.
    right. exact h.
Qed.

Theorem union2_compl A U:
  A ⊆ U → A ∪ (U \ A) = U.
Proof.
  intro hAU. apply ext.
  intro x. split.
  * intro h. apply union2_elim in h.
    destruct h as [hl | hr].
    - unfold subclass in hAU. exact (hAU x hl).
    - apply difference_elim in hr.
      exact (proj1 hr).
  * intro h. apply union2_intro.
    destruct (LEM (x ∈ A)) as [hA | hnA].
    - left. exact hA.
    - right. apply difference_intro.
      exact (conj h hnA).
Qed.

Theorem union2_assoc A B C:
  A ∪ (B ∪ C) = (A ∪ B) ∪ C.
Proof.
  apply ext. intro x. split.
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
  unfold subclass. intro x.
  intro h. apply intersection2_elim in h.
  destruct h as (hM, _).
  apply (intersection_intro (set_intro hM)).
  intro A. intro hA. apply intersection2_elim in hA.
  destruct hA as (hAM, _).
  exact (intersection_elim hM A hAM).
Qed.

Theorem intersection_subclass_union M:
  M ≠ ∅ → ⋂M ⊆ ⋃M.
Proof.
  intro hM. unfold subclass. intros x. intro hx.
  apply comp. apply comp in hx.
  destruct hx as (hsx, hx). split.
  * exact hsx.
  * apply non_empty_class in hM.
    destruct hM as (A, hA). exists A. split.
    - exact hA.
    - exact (hx A hA).
Qed.

Theorem prod_left_empty Y:
  ∅ × Y = ∅.
Proof.
  apply ext. intro t. split.
  * intro h. apply comp_elim in h.
    destruct h as (u, (v, (hu, (hv, huv)))).
    exfalso. exact (empty_set_property hu).
  * intro h. exfalso. exact (empty_set_property h).
Qed.

Theorem prod_right_empty X:
  X × ∅ = ∅.
Proof.
  apply ext. intro t. split.
  * intro h. apply comp_elim in h.
    destruct h as (u, (v, (hu, (hv, huv)))).
    exfalso. exact (empty_set_property hv).
  * intro h. exfalso. exact (empty_set_property h).
Qed.

Theorem prod_subclass_prod {A B X Y}:
  A ⊆ X → B ⊆ Y → A × B ⊆ X × Y.
Proof.
  intros hAX hBY. unfold subclass. intro t. intro ht.
  apply prod_intro. apply prod_elim in ht.
  destruct ht as (x, (y, (hx, (hy, ht)))).
  exists x. exists y. repeat split.
  * unfold subclass in hAX. exact (hAX x hx).
  * unfold subclass in hBY. exact (hBY y hy).
  * exact ht.
Qed.

Theorem prod_intersection2 X A B:
  X × (A ∩ B) = (X × A) ∩ (X × B).
Proof.
  apply ext. intro t. split.
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
    rewrite ht in ht'.
    assert (hsx := set_intro hx).
    assert (hsy := set_intro hy).
    assert (hsx' := set_intro hx').
    assert (hsy' := set_intro hy').
    apply (pair_eq x y x' y' hsx hsy) in ht'.
    clear hsx hsy hsx' hsy'.
    destruct ht' as (_, hyy'). clear hx' x'.
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
  apply ext. intro t. split.
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

Theorem union_union2 M N:
  ⋃(M ∪ N) = (⋃M) ∪ (⋃N).
Proof.
  apply ext. intro x. split.
  * intro h. apply union2_intro.
    apply comp in h.
    destruct h as (hsx, (A, (hA, hx))).
    apply union2_elim in hA.
    destruct hA as [hl | hr].
    - left. apply comp. split.
      -- exact hsx.
      -- exists A. exact (conj hl hx).
    - right. apply comp. split.
      -- exact hsx.
      -- exists A. exact (conj hr hx).
  * intro h. apply union2_elim in h.
    apply comp. destruct h as [hl | hr].
    - apply comp in hl.
      destruct hl as (hsx, (A, (hA, hx))).
      split.
      -- exact hsx.
      -- exists A. split.
         --- apply union2_intro. left. exact hA.
         --- exact hx.
    - apply comp in hr.
      destruct hr as (hsx, (A, (hA, hx))).
      split.
      -- exact hsx.
      -- exists A. split.
         --- apply union2_intro. right. exact hA.
         --- exact hx.
Qed.

Theorem intersection_anti_monotone {M N}:
  M ⊆ N → ⋂N ⊆ ⋂M.
Proof.
  intros h. unfold subclass.
  intros x hx. apply intersection_intro.
  * exact (set_intro hx).
  * intros A hA. apply h in hA. clear h.
    apply comp_elim in hx. exact (hx A hA).
Qed.

Theorem union_monotone {M N}:
  M ⊆ N → ⋃M ⊆ ⋃N.
Proof.
  intros h. unfold subclass.
  intros x hx. apply union_intro.
  apply comp_elim in hx.
  destruct hx as (A, (hA, hx)).
  exists A. split.
  * exact (h A hA).
  * exact hx.
Qed.

Theorem intersection_is_lower_bound {A M}:
  A ∈ M → ⋂M ⊆ A.
Proof.
  intro h. unfold subclass. intro x. intro hx.
  apply comp_elim in hx. exact (hx A h).
Qed.
