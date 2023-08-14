
Require Import Coq.Unicode.Utf8.

(* Commutative law for universal quantifier chain *)
Theorem uq_chain_cl (X Y: Type) (P: X → Y → Prop):
  (∀x, ∀y, P x y) ↔ (∀y, ∀x, P x y).
Proof.
  split.
  * intro h. intro y. intro x.
    assert (hxy := h x y). exact hxy.
  * intro h. intro x. intro y.
    assert (hyx := h y x). exact hyx.
Qed.

(* Commutative law for existential quantifier chain *)
Theorem ex_chain_cl (X Y: Type) (P: X → Y → Prop):
  (∃x, ∃y, P x y) ↔ (∃y, ∃x, P x y).
Proof.
  split.
  * intro h. destruct h as (x, (y, hxy)).
    exists y. exists x. exact hxy.
  * intro h. destruct h as (y, (x, hxy)).
    exists x. exists y. exact hxy.
Qed.

Theorem uq_conj_const (A: Prop) (X: Type) (P: X → Prop):
  A ∧ (∀x, P x) → (∀x, A ∧ P x).
Proof.
  intro h. intro x. destruct h as (a, f).
  split.
  * exact a.
  * apply (f x).
Qed.

Theorem uq_conj_const_term (A: Prop) (X: Type) (P: X → Prop):
  A ∧ (∀x, P x) → (∀x, A ∧ P x).
Proof.
  exact (fun '(conj a f) => fun x => conj a (f x)).
Qed.

Theorem uq_conj_const_term_types (A X: Type) (P: X → Type):
  A*(∀x, P x) -> (∀x, A*(P x)).
Proof.
  exact (fun '(a, f) => fun x => (a, f x)).
Qed.

Theorem uq_conj_const_ind (A: Prop) (X: Type) (P: X → Prop):
  A ∧ (∀x, P x) → (∀x, A ∧ P x).
Proof.
  exact (fun h => and_ind
    (fun a f => fun x => conj a (f x)) h).
Qed.

(* Conjunction distribution law *)
Theorem conj_dl_ex (A: Prop) (X: Type) (P: X → Prop):
  A ∧ (∃x, P x) ↔ (∃x, A ∧ P x).
Proof.
  split.
  * intro h. destruct h as (a, (x, hx)).
    exists x. split.
    - exact a.
    - exact hx.
  * intro h. destruct h as (x, (a, hx)).
    split.
    - exact a.
    - exists x. exact hx.
Qed.

Theorem conj_dl_ex_term (A: Prop) (X: Type) (P: X → Prop):
  A ∧ (∃x, P x) ↔ (∃x, A ∧ P x).
Proof.
  exact (conj
    (fun '(conj a t) =>
      match t with ex_intro _ x hx =>
        ex_intro _ x (conj a hx)
      end)
    (fun h =>
      match h with ex_intro _ x (conj a hx) =>
        conj a (ex_intro _ x hx)
      end)).
Qed.

Theorem conj_dl_ex_term_types (A X: Type) (P: X → Type):
  prod A {x & P x} → {x & prod A (P x)}.
Proof.
  exact (fun '(a, t) =>
    match t with existT _ x hx =>
      existT _ x (a, hx)
    end).
Qed.

Theorem uq_factor (X: Type) (P Q: X → Prop):
  (∀x, P x ∧ Q x) ↔ (∀x, P x) ∧ (∀x, Q x).
Proof.
  split.
  * intro h. split.
    - intro x. exact (proj1 (h x)).
    - intro x. exact (proj2 (h x)).
  * intro h. intro x.
    destruct h as (hP, hQ). split.
    - apply hP.
    - apply hQ.
Qed.

Theorem uq_factor_term (X: Type) (P Q: X → Prop):
  (∀x, P x ∧ Q x) ↔ (∀x, P x) ∧ (∀x, Q x).
Proof.
  exact (conj
    (fun h => conj
      (fun x => proj1 (h x))
      (fun x => proj2 (h x)))
    (fun '(conj f g) =>
      fun x => conj (f x) (g x))).
Qed.

Theorem ex_factor_sum (X: Type) (P Q: X → Prop):
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x).
Proof.
  intro h. destruct h as (x, hPQ).
  destruct hPQ as (hP, hQ).
  split.
  * exists x. exact hP.
  * exists x. exact hQ.
Qed.

Theorem ex_factor_sum_term (X: Type) (P Q: X → Prop):
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x).
Proof.
  exact (fun h =>
    match h with ex_intro _ x (conj hP hQ) => conj
      (ex_intro _ x hP)
      (ex_intro _ x hQ)
    end).
Qed.

Theorem ex_factor_split (X: Type) (P Q: X → Prop):
  (∃x, P x ∨ Q x) ↔ (∃x, P x) ∨ (∃x, Q x).
Proof.
  split.
  * intro h. destruct h as (x, hPQ).
    destruct hPQ as [hP | hQ].
    - left.  exists x. exact hP.
    - right. exists x. exact hQ.
  * intro h. destruct h as [heP | heQ].
    - destruct heP as (x, hP). exists x. left.  exact hP.
    - destruct heQ as (x, hQ). exists x. right. exact hQ.
Qed.

Theorem ex_expand (X: Type) (P Q: X -> Prop):
  (∃x, P x) ∧ (∃x, Q x) ↔ (∃x, (∃y, P x ∧ Q y)).
Proof.
  split.
  * intro h. destruct h as (heP, heQ).
    destruct heP as (x, hP).
    destruct heQ as (y, hQ).
    exists x. exists y. split.
    - exact hP.
    - exact hQ.
  * intro h. destruct h as (x, (y, hPQ)).
    destruct hPQ as (hP, hQ).
    split.
    - exists x. exact hP.
    - exists y. exact hQ.
Qed.

(* Subjunction distribution law *)
Theorem subj_dl_uq (A: Prop) (X: Type) (P: X → Prop):
  (A → ∀x, P x) ↔ (∀x, A → P x).
Proof.
  split.
  * intro h. intro x. intro hA.
    exact (h hA x).
  * intro h. intro hA. intro x.
    exact (h x hA).
Qed.

Theorem ex_const (X: Type) (A: Prop):
  (∃(x: X), A) → A.
Proof.
  intro h. destruct h as (x, hA). exact hA.
Qed.

(* X ≠ ∅ *)
Definition NonEmpty (X: Type) := (∃x: X, True).

(* X ≠ ∅ ⇒ ((∃x∈X.A) ⇔ A) *)
Theorem ex_const_iff (X: Type) (A: Prop) (w: NonEmpty X):
  (∃(x: X), A) ↔ A.
Proof.
  split.
  * apply ex_const.
  * destruct w as (x, _). intro hA. exists x. exact hA.
Qed.

(* (∃x∈X. A) ⇔ (X ≠ ∅) ∧ A *)
Theorem ex_const_iff2 (X: Type) (A: Prop):
  (∃(x: X), A) ↔ (NonEmpty X) ∧ A.
Proof.
  split.
  * intro h. destruct h as (x, hA).
    split.
    - exists x. exact I.
    - exact hA.
  * intro h. destruct h as (w, hA).
    destruct w as (x, _). exists x. exact hA.
Qed.

Theorem uq_const (X: Type) (A: Prop):
  A → ∀(x: X), A.
Proof.
  intro hA. intro x. exact hA.
Qed.

(* X ≠ ∅ ⇒ ((∀x∈X.A) ⇔ A) *)
Theorem uq_const_iff (X: Type) (A: Prop) (w: NonEmpty X):
  (∀(x: X), A) ↔ A.
Proof.
  split.
  * intro h. destruct w as (x, _). exact (h x).
  * apply uq_const.
Qed.
