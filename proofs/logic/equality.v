
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

