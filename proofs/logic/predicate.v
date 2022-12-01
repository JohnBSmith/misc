
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
Theorem conj_distributes_ex (A: Prop) (X: Type) (P: X -> Prop):
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

Theorem conj_distributes_ex_term (A: Prop) (X: Type) (P: X -> Prop):
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

Theorem conj_distributes_ex_term_types (A X: Type) (P: X -> Type):
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

(* (∃x.P(x)) ∧ (∃x.Q(x)) ⇒ (∃x.∃y.P(x) ∧ Q(y)) *)
Theorem ex_expand (X: Type) (P Q: X -> Prop):
  (exists x, P x) /\ (exists x, Q x) -> (exists x, (exists y, P x /\ Q y)).
Proof.
  intro h.
  destruct h as (ep, eq).
  destruct ep as (x, p).
  destruct eq as (y, q).
  exists x. exists y.
  split.
  - exact p.
  - exact q.
Qed.

