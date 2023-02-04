
Require Import Arith.
Require Import Ring.

Fixpoint sum (n: nat) (a: nat -> nat)
  := match n with
     | 0 => a 0
     | S n => a (S n) + sum n a
     end.

Theorem homogenity (c n: nat) (a: nat -> nat):
  c*(sum n a) = sum n (fun k => c*(a k)).
Proof.
  induction n.
  * simpl. trivial.
  * simpl. ring [IHn]. 
Qed.

Theorem additivity (n: nat) (a b: nat -> nat):
  sum n (fun k => a k + b k) = (sum n a) + (sum n b).
Proof.
  induction n.
  * simpl. trivial.
  * simpl. ring [IHn].
Qed.

Theorem sum_of_integers (n: nat) (a b: nat -> nat):
  2*sum n (fun k => k) = n*(n + 1).
Proof.
  induction n.
  * simpl. trivial.
  * simpl sum. ring [IHn].
Qed.

