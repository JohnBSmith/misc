
(* (∀x.∀y.P(x, y)) ⇔ (∀y.∀x.P(x, y)) *)
Theorem uq_commutes (X Y: Type) (P: X -> Y -> Prop):
  (forall x, forall y, P x y) -> (forall y, forall x, P x y).
Proof.
  intro h. intro y. intro x.
  assert (p := h x y).
  exact p.
Qed.

(* (∃x.∃y.P(x, y)) ⇔ (∃y.∃x.P(x, y)) *)
Theorem ex_commutes (X Y: Type) (P: X -> Y -> Prop):
  (exists x, exists y, P x y) -> (exists y, exists x, P x y).
Proof.
  intro h. destruct h as (x, (y, p)).
  exists y. exists x. exact p.
Qed.

(* A ∧ (∀x.P(x)) ⇒ (∀x. A ∧ P(x)) *)
Theorem const_factor (A: Prop) (X: Type) (P: X -> Prop):
  A /\ (forall x, P x) -> (forall x, A /\ P x).
Proof.
  intros h x.
  destruct h as (a, f).
  split.
  - exact a.
  - apply (f x).
Qed.

Theorem const_factor_term (A: Prop) (X: Type) (P: X -> Prop):
  A /\ (forall x, P x) -> (forall x, A /\ P x).
Proof.
  exact (fun '(conj a f) => fun x => conj a (f x)).
Qed.

Theorem const_factor_term_types (A X: Type) (P: X -> Type):
  A*(forall x, P x) -> (forall x, A*(P x)).
Proof.
  exact (fun '(a, f) => fun x => (a, f x)).
Qed.

Theorem const_factor_ind (A: Prop) (X: Type) (P: X -> Prop):
  A /\ (forall x, P x) -> (forall x, A /\ P x).
Proof.
  exact (fun h => and_ind (fun a f => fun x => conj a (f x)) h).
Qed.

(* A ∧ (∃x.P(x)) ⇔ (∃x. A ∧ P(x)) *)
Theorem conj_distributes_over_ex (A: Prop) (X: Type) (P: X -> Prop):
  A /\ (exists x, P x) <-> (exists x, A /\ P x).
Proof.
  split.
  * intro h.
    destruct h as (a, t).
    destruct t as (x, p).
    exists x.
    split.
    - exact a.
    - exact p.
  * intro h.
    destruct h as (x, (a, p)).
    split.
    - exact a.
    - exists x. exact p.
Qed.

Theorem conj_distributes_over_ex_term (A: Prop) (X: Type) (P: X -> Prop):
  A /\ (exists x, P x) <-> (exists x, A /\ P x).
Proof.
  exact (conj
    (fun '(conj a t) =>
      match t with ex_intro _ x p =>
        ex_intro _ x (conj a p)
      end)
    (fun h =>
      match h with ex_intro _ x (conj a p) =>
        conj a (ex_intro _ x p)
      end)).
Qed.

Theorem conj_distributes_over_ex_term_types (A X: Type) (P: X -> Type):
  prod A {x & P x} -> {x & prod A (P x)}.
Proof.
  exact (fun '(a, t) =>
    match t with existT _ x p =>
      existT _ x (a, p)
    end).
Qed.

(* (∀x.P(x) ∧ Q(x)) ⇔ (∀x.P(x)) ∧ (∀x.Q(x)) *)
Theorem uq_factor (X: Type) (P Q: X -> Prop):
  (forall x, P x /\ Q x) <-> (forall x, P x) /\ (forall x, Q x).
Proof.
  split.
  * intro h.
    split.
    - intro x. apply (h x).
    - intro x. apply (h x).
  * intros h x.
    destruct h as (fp, fq).
    split.
    - apply fp.
    - apply fq.
Qed.

Theorem uq_factor_term (X: Type) (P Q: X -> Prop):
  (forall x, P x /\ Q x) <-> (forall x, P x) /\ (forall x, Q x).
Proof.
  exact (conj
    (fun h => conj
      (fun x => proj1 (h x))
      (fun x => proj2 (h x)))
    (fun '(conj f g) =>
      fun x => conj (f x) (g x))).
Qed.

(* (∃x.P(x) ∧ Q(x)) ⇒ (∃x.P(x)) ∧ (∃x.Q(x)) *)
Theorem ex_factor_sum (X: Type) (P Q: X -> Prop):
  (exists x, P x /\ Q x) -> (exists x, P x) /\ (exists x, Q x).
Proof.
  intro h.
  destruct h as (x, pq).
  destruct pq as (p, q).
  split.
  - exists x. exact p.
  - exists x. exact q.
Qed.

Theorem ex_factor_sum_term (X: Type) (P Q: X -> Prop):
  (exists x, P x /\ Q x) -> (exists x, P x) /\ (exists x, Q x).
Proof.
  exact (fun h =>
    match h with ex_intro _ x (conj p q) => conj
      (ex_intro _ x p)
      (ex_intro _ x q)
    end).
Qed.

(* (∃x.P(x) ∨ Q(x)) ⇔ (∃x.P(x)) ∨ (∃x.Q(x)) *)
Theorem ex_factor_split (X: Type) (P Q: X -> Prop):
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  split.
  * intro h.
    destruct h as (x, pq).
    destruct pq as [p | q].
    - left.  exists x. exact p.
    - right. exists x. exact q.
  * intro h.
    destruct h as [ep | eq].
    - destruct ep as (x, p). exists x. left.  exact p.
    - destruct eq as (x, q). exists x. right. exact q.
Qed.

(* (∃x.P(x)) ∧ (∃x.Q(x)) ⇔ (∃x.∃y.P(x) ∧ Q(y)) *)
Theorem ex_expand (X: Type) (P Q: X -> Prop):
  (exists x, P x) /\ (exists x, Q x) <-> (exists x, (exists y, P x /\ Q y)).
Proof.
  split.
  * intro h. destruct h as (ep, eq).
    destruct ep as (x, p).
    destruct eq as (y, q).
    exists x. exists y.
    split.
    - exact p.
    - exact q.
  * intro h. destruct h as (x, (y, pq)).
    destruct pq as (p, q).
    split.
    - exists x. exact p.
    - exists y. exact q.
Qed.

(* (A ⇒ ∀x.P(x)) ⇔ ∀x.(A ⇒ P(x)) *)
Theorem cond_distributes_over_uq (A: Prop) (X: Type) (P: X -> Prop):
  (A -> forall x, P x) <-> (forall x, A -> P x).
Proof.
  split.
  * intro h. intro x. intro a.
    exact (h a x).
  * intro h. intro a. intro x.
    exact (h x a).
Qed.

(* (∃x.A) ⇒ A *)
Theorem ex_const (X: Type) (A: Prop):
  (exists x: X, A) -> A.
Proof.
  intro h. destruct h as (x, p). exact p.
Qed.

(* X ≠ ∅ *)
Definition NonEmpty (X: Type) := (exists x: X, True).

(* X ≠ ∅ ⇒ ((∃x∈X.A) ⇔ A) *)
Theorem ex_const_iff (X: Type) (A: Prop) (w: NonEmpty X):
  (exists x: X, A) <-> A.
Proof.
  split.
  * apply ex_const.
  * destruct w as (x, _). intro a. exists x. exact a.
Qed.

(* (∃x∈X.A) ⇔ (X ≠ ∅) ∧ A *)
Theorem ex_const_iff2 (X: Type) (A: Prop):
  (exists x: X, A) <-> (NonEmpty X) /\ A.
Proof.
  split.
  * intro h. destruct h as (x, a).
    split.
    - exists x. exact I.
    - exact a.
  * intro h. destruct h as (w, a).
    destruct w as (x, _). exists x. exact a.
Qed.

(* A ⇒ ∀x.A *)
Theorem uq_const (X: Type) (A: Prop):
  A -> (forall x: X, A).
Proof.
  intro a. intro x. exact a.
Qed.

(* X ≠ ∅ ⇒ ((∀x∈X.A) ⇔ A) *)
Theorem uq_const_iff (X: Type) (A: Prop) (w: NonEmpty X):
  (forall x: X, A) <-> A.
Proof.
  split.
  * intro h. destruct w as (x, _). exact (h x).
  * apply uq_const.
Qed.
