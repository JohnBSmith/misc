
Require Import Reals.
Local Open Scope R_scope.

Theorem lt_add (a b a' b': R):
  a < b -> a' < b' -> a + a' < b + b'.
Proof.
  intro h1. intro h2.
  assert (h3 := Rplus_lt_compat_r a' a b h1).
  assert (h4 := Rplus_lt_compat_l b a' b' h2).
  exact (Rlt_trans _ _ _ h3 h4).
Qed.

Theorem lt_mul (a b a' b': R):
  0 < a' -> 0 < b -> a < b -> a' < b' -> a*a' < b*b'.
Proof.
  intros h1 h2 h3 h4.
  assert (h5 := Rmult_lt_compat_r a' a b h1 h3).
  assert (h6 := Rmult_lt_compat_l b a' b' h2 h4).
  exact (Rlt_trans _ _ _ h5 h6).
Qed.

Theorem lt_sq (a b: R): 0 < a -> a < b -> a*a < b*b.
Proof.
  intro h1. intro h2.
  assert (h3 := Rlt_trans _ _ _ h1 h2).
  assert (h4 := Rmult_lt_compat_r a a b h1 h2).
  assert (h5 := Rmult_lt_compat_l b a b h3 h2).
  exact (Rlt_trans _ _ _ h4 h5).
Qed.

