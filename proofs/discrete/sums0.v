
Require Import Coq.Arith.PeanoNat.

Fixpoint sum (n: nat) (a: nat -> nat)
  := match n with
     | 0 => 0
     | S n => a (S n) + sum n a
     end.

Theorem homogenity (c n: nat) (a: nat -> nat):
  c*(sum n a) = sum n (fun k => c*(a k)).
Proof.
  induction n.
  * simpl. exact (Nat.mul_0_r c).
  * simpl.
    rewrite Nat.mul_add_distr_l.
    rewrite IHn.
    reflexivity.
Qed.

Theorem homogenity_v2 (c n: nat) (a: nat -> nat):
  c*(sum n a) = sum n (fun k => c*(a k)).
Proof.
  induction n.
  * simpl. exact (Nat.mul_0_r c).
  * simpl.
    assert (e1 := Nat.mul_add_distr_l c (a (S n)) (sum n a)).
    assert (e2 := f_equal (fun x => c * a (S n) + x) IHn).
    simpl in e2.
    assert (e3 := eq_trans e1 e2).
    exact e3.
Qed.

Theorem additivity (n: nat) (a b: nat -> nat):
  sum n (fun k => a k + b k) = sum n a + sum n b.
Proof.
  induction n.
  * simpl. exact (eq_refl 0).
  * simpl. rewrite IHn.
    rewrite <- Nat.add_assoc.
    rewrite <- Nat.add_assoc.
    f_equal.
    rewrite Nat.add_assoc.
    rewrite Nat.add_comm.
    rewrite Nat.add_assoc.
    rewrite Nat.add_comm.
    f_equal.
    rewrite Nat.add_comm.
    reflexivity.
Qed.

Theorem sum_of_integers (n: nat):
  2*sum n (fun k => k) = n*(n + 1).
Proof.
  induction n.
  * simpl. exact (eq_refl 0).
  * simpl sum.
    rewrite Nat.mul_succ_r.
    rewrite Nat.mul_add_distr_l.
    rewrite IHn.
    replace (S n) with (n + 1) by apply (Nat.add_1_r).
    rewrite <- (Nat.add_assoc n 1 1).
    simpl (1 + 1).
    rewrite (Nat.mul_comm n (n + 1)).
    rewrite <- Nat.add_assoc.
    rewrite (Nat.add_comm).
    rewrite <- Nat.add_assoc.
    rewrite (Nat.mul_comm 2 n).
    replace 2 with (1*2) at 1 by reflexivity.
    rewrite <- Nat.mul_add_distr_r.
    rewrite (Nat.add_comm 1 n).
    rewrite <- Nat.mul_add_distr_l.
    reflexivity.
Qed.

