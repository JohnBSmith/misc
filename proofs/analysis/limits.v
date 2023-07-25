
Require Import Reals.
Local Open Scope R_scope.

Definition lim_is (a: nat -> R) (L: R) :=
  forall (eps: R), 0 < eps -> exists (n0: nat),
  forall (n: nat), (n0 <= n)%nat -> Rabs(a n - L) < eps.

Theorem lim_const_is_const (c: R):
  lim_is (fun n => c) c.
Proof.
  unfold lim_is.
  intros eps eps_pos.
  exists 0%nat.
  intros n n_cond.
  rewrite (Rminus_diag_eq c c (eq_refl c)).
  rewrite Rabs_R0.
  exact eps_pos.
Qed.

Theorem lim_mult_const_nonzero (a: nat -> R) (L: R) (r: R):
  r <> 0 -> lim_is a L -> lim_is (fun n => r*a n) (r*L).
Proof.
  intros r_nonzero hyp0.
  unfold lim_is.
  intros eps eps_pos.
  set (eps' := eps/Rabs(r)).
  assert (eps'_pos: 0 < eps'). {
    unfold eps'.
    apply Rmult_lt_0_compat.
    * exact eps_pos. 
    * apply Rinv_0_lt_compat.
      exact (Rabs_pos_lt r r_nonzero).
  }
  destruct (hyp0 eps' eps'_pos) as (n0, hyp1).
  exists n0. intros n cond_n.
  assert (rel0 := hyp1 n cond_n).
  unfold eps' in rel0.
  assert (rel1 := Rmult_lt_compat_l (Rabs r)
     _ _ (Rabs_pos_lt r r_nonzero) rel0).
  unfold Rdiv in rel1.
  rewrite <- Rmult_assoc in rel1.
  rewrite (Rmult_comm _ eps) in rel1.
  rewrite Rmult_assoc in rel1.
  rewrite Rinv_r in rel1 by exact (Rabs_no_R0 r r_nonzero).
  rewrite Rmult_1_r in rel1.
  field_simplify in rel1.
  rewrite <- Rabs_mult in rel1.
  rewrite Rmult_minus_distr_l in rel1.
  exact rel1.
Qed.

Theorem lim_mult_const (a: nat -> R) (L: R) (r: R):
  lim_is a L -> lim_is (fun n => r*a n) (r*L).
Proof.
  intro hyp.
  destruct (Req_dec r 0) as [r_zero | r_nonzero].
  * rewrite r_zero. rewrite Rmult_0_l.
    unfold lim_is. setoid_rewrite Rmult_0_l.
    exact (lim_const_is_const 0).
  * exact (lim_mult_const_nonzero a L r r_nonzero hyp).
Qed.

