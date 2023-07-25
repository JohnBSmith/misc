
(* a = b ⇔ ∀x.(x = a ⇔ x = b) *)
Theorem eq_char (X: Type) (a b: X):
  a = b <-> forall x, x = a <-> x = b.
Proof.
  split.
  * intro eqab. intro x.
    split.
    - intro eqxa.
      exact (eq_trans eqxa eqab).
    - intro eqxb.
      exact (eq_trans eqxb (eq_sym eqab)).
  * intro h.
    assert (f := proj1 (h a)).
    exact (f (eq_refl a)).
Qed.

(* P(x) ⇔ ∀y.(x = y ⇒ P(y)) *)
Theorem pred_app_iff_uq (X: Type) (P: X -> Prop) (x: X):
  (P x) <-> forall y, x = y -> (P y).
Proof.
  split.
  * intro h. intro y. intro eqxy.
    exact (eq_ind x P h y eqxy).
  * intro h. assert (f := h x).
    exact (f (eq_refl x)).
Qed.

(* P(x) ⇔ ∃y.(x = y ∧ P(y)) *)
Theorem pred_app_iff_ex (X: Type) (P: X -> Prop) (x: X):
  (P x) <-> exists y, x = y /\ (P y).
Proof.
  split.
  * intro h. exists x. exact (conj (eq_refl x) h).
  * intro h. destruct h as (y, (eqxy, py)).
    exact (eq_ind y P py x (eq_sym eqxy)).
Qed.

(* ∀x.∀y. x = y ⇒ (P(x) ⇔ P(y)) *)
Theorem substitution_rule (X: Type) (P: X -> Prop):
  forall x y, x = y -> ((P x) <-> (P y)).
Proof.
  intro x. intro y. intro eqxy.
  split.
  * intro px. exact (eq_ind x P px y eqxy).
  * intro py. exact (eq_ind y P py x (eq_sym eqxy)).
Qed.

(* (∃!x. A(x)) :⇔ (∃x. A(x) ∧ ∀y. A(y) ⇒ x = y) *)
(* (∃!x. A(x)) ⇔ (∃x. A(x)) ∧ (∀x. ∀y. A(x) ∧ A(y) ⇒ x = y) *)
Goal forall (X: Type) (A: X -> Prop),
  (exists x, A x /\ forall y, A y -> x = y)
  <-> (exists x, A x) /\ (forall x y, A x /\ A y -> x = y).
Proof.
  intros X A.
  split.
  * intro h. split.
    - destruct h as (u, (p, _)). exists u. exact p.
    - destruct h as (u, (p, f)).
      intros x y. intros (hx, hy).
      assert (hux := f x hx).
      assert (huy := f y hy).
      exact (eq_trans (eq_sym hux) huy).
  * intro h. destruct h as (hex, huniq).
    destruct hex as (u, p).
    exists u. split.
    - exact p.
    - intro y. intro hy.
      exact (huniq u y (conj p hy)).
Qed.

(* (∀x. ∀y. A(x) ∧ A(y) ⇒ x = y) ⇔ (∀x. A(x) ⇒ ∀y. A(y) ⇒ x = y) *)
Goal forall (X: Type) (A: X -> Prop),
  (forall x y, A x /\ A y -> x = y) <->
  (forall x, A x -> forall y, A y -> x = y).
Proof.
  intros X A. split.
  * intro h. intros x hx y hy.
    exact (h x y (conj hx hy)).
  * intro h. intros x y (hx, hy).
    exact (h x hx y hy).
Qed.
