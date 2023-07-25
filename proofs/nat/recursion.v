
Require Import Coq.Logic.FunctionalExtensionality.

Parameter X: Type.
Parameter x0: X.
Parameter phi: X -> X.

Definition A (f: nat -> X) :=
  f 0 = x0 /\ (forall n, f (S n) = phi (f n)).

Theorem uniq (f g: nat -> X): A f /\ A g -> f = g.
Proof.
  intro h. unfold A in h.
  destruct h as ((hf0, hfn), (hg0, hgn)).
  extensionality n.
  induction n.
  * rewrite hf0. rewrite hg0.
    reflexivity.
  * rewrite hfn. rewrite hgn. rewrite IHn.
    reflexivity.
Qed.

