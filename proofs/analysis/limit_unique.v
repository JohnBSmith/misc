Require Import Reals.Reals.
Require Import Classical.
Open Scope R_scope.

Theorem positive_from_nonnegative (x: R):
  (0 <= x) -> (x <> 0) -> 0 < x.
Proof.
  intros h1 h2. unfold "<=" in h1.
  destruct h1 as [hl | hr].
  * exact hl.
  * exfalso. symmetry in hr.
    exact (h2 hr).
Qed.

Theorem half_positive (x: R):
  0 < x -> 0 < x / 2.
Proof.
  intros h. apply Rdiv_lt_0_compat.
  * apply h.
  * apply Rlt_0_2.
Qed.

Definition metric_space (X: Type) (d: X -> X -> R) :=
  (forall x y: X, d x y = 0 <-> x = y) /\
  (forall x y: X, d x y = d y x) /\
  (forall x y z: X, d x y <= d x z + d z y).

Section MetricSpace.
  Variable X: Type.
  Variable d: X -> X -> R.
  Hypothesis hmsXd: metric_space X d.

  Definition converges (xs: nat -> X) (x: X) :=
    forall eps: R, 0 < eps -> exists n0: nat,
      forall n: nat, Nat.le n0 n -> d (xs n) x < eps.

  Theorem metric_non_negative:
    metric_space X d -> forall x y: X, 0 <= d x y.
  Proof.
    intro h. destruct h as (h1, (h2, h3)).
    intros x y.
    assert (h4 := h3 x x y). clear h3.
    rewrite (h2 y x) in h4. clear h2.
    assert (h5 := eq_refl x).
    apply h1 in h5. clear h1.
    rewrite h5 in h4. clear h5.
    rewrite Rplus_diag in h4.
    assert (h6 := Rmult_le_compat_l (/2) 0 (2 * d x y)).
    assert (h7 := Rlt_0_2). assert (h8 := Rlt_not_eq 0 2 h7).
    apply Rinv_0_lt_compat in h7. apply Rlt_le in h7.
    assert (h9 := h6 h7 h4). clear h4 h6 h7.
    rewrite Rmult_0_r in h9. rewrite <- Rmult_assoc in h9.
    assert (h10 := Rmult_inv_l 2 (not_eq_sym h8)).
    rewrite h10 in h9. clear h8 h10.
    rewrite Rmult_1_l in h9. exact h9.
  Qed.

  Theorem disjoint_epsilon_balls_exist (x y: X):
    x <> y -> exists eps: R, 0 < eps /\
      forall z: X, ~(d z x < eps /\ d z y < eps).
  Proof.
    intro h.
    assert (h1 := proj1 hmsXd x y).
    apply not_iff_compat in h1.
    apply h1 in h. clear h1.
    assert (h2 := metric_non_negative hmsXd x y).
    assert (h3 := positive_from_nonnegative _ h2 h).
    clear h h2.
    pose (eps := (d x y)/2).
    exists eps. split.
    * exact (half_positive _ h3).
    * intro z. intros (h4, h5).
      destruct hmsXd as (_, (h6, h7)).
      assert (h6 := h6 z x). assert (h7 := h7 x y z).
      rewrite h6 in h4. clear h3 h6.
      assert (h9 := Rplus_lt_compat _ _ _ _ h4 h5).
      assert (h10 := Rle_lt_trans _ _ _ h7 h9).
      clear h4 h5 h7 h9.
      rewrite Rplus_diag in h10.
      unfold eps in h10.
      rewrite Rmult_div_assoc in h10.
      assert (h11 := Rlt_0_2). apply Rlt_not_eq in h11.
      apply not_eq_sym in h11.
      assert (h12 := Rmult_div_r 2 (d x y) h11).
      rewrite h12 in h10. clear h11 h12.
      apply Rlt_irrefl in h10. exact h10.
  Qed.

  Theorem limit_unique (x y: X) (xs: nat -> X):
    converges xs x /\ converges xs y -> x = y.
  Proof.
    intros (hx, hy). apply NNPP. intro h.
    destruct (disjoint_epsilon_balls_exist x y h)
      as (eps, (heps, hballs)).
    destruct (hx eps heps) as (n1, hn1). clear hx.
    destruct (hy eps heps) as (n2, hn2). clear hy.
    pose (n := Nat.max n1 n2).
    assert (h1 := hn1 n (Nat.le_max_l n1 n2)).
    assert (h2 := hn2 n (Nat.le_max_r n1 n2)).
    exact (hballs (xs n) (conj h1 h2)).
  Qed.
End MetricSpace.

Theorem metric_space_R:
  metric_space R (fun x y => Rabs (x - y)).
Proof.
  unfold metric_space. split; [| split].
  * intros x y. split.
    - intro h. Search (Rabs (_ - _)).
      apply cond_eq. intros eps heps.
      rewrite h. exact heps.
    - intro h. rewrite <- h.
      rewrite Rminus_diag.
      exact Rabs_R0.
  * exact Rabs_minus_sym.
  * intros x y z.
    assert (h := Rabs_triang (x - z) (z - y)).
    rewrite Rplus_minus_assoc in h.
    rewrite <- Rplus_minus_swap in h.
    rewrite Rplus_minus_r in h.
    exact h.
Qed.
