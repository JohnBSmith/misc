
Theorem lt_succ (n: nat): n < S n.
Proof.
  unfold lt.
  exact (le_n (S n)).
Qed.

Goal forall (A: nat -> Prop),
  (forall m n, n < m -> A n) -> (forall n, A n).
Proof.
  intro A. intro h.
  intro u.
  assert (h0 := h (S u) u).
  assert (h1 := lt_succ u).
  exact (h0 h1).
Qed.


Goal forall A B: nat -> Prop,
  A 0 /\ (forall n, A n -> B (S n)) /\ (forall n, B n -> A (S n))
  -> (forall n, A n \/ B n).
Proof.
  intros A B. intro h. destruct h as (a0, (ab, ba)).
  intro n. induction n.
  * left. exact a0.
  * destruct IHn as [ha | hb].
    - right. exact (ab n ha).
    - left. exact (ba n hb).
Qed.
