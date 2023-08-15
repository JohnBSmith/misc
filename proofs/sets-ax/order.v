
Require Import Coq.Unicode.Utf8.
Require Import axioms.

Notation "x ≤ [ R ] y" := ((x, y) ∈ R) (at level 70).

Record partial_order R X := {
  po_refl: ∀x, x ∈ X → x ≤[R] x;
  po_antisym: ∀x y, x ∈ X → y ∈ X →
    x ≤[R] y → y ≤[R] x → x = y;
  po_trans: ∀x y z, x ∈ X → y ∈ X → z ∈ X →
    x ≤[R] y → y ≤[R] z → x ≤[R] z
}.

Definition lower_bound R s A :=
  ∀x, x ∈ A → s ≤[R] x.

Definition upper_bound R A s :=
  ∀x, x ∈ A → x ≤[R] s.

(* y = min(A) *)
Definition is_min R y A :=
  y ∈ A ∧ lower_bound R y A.

(* y = max(A) *)
Definition is_max R y A :=
  y ∈ A ∧ upper_bound R A y.

(* y = inf(A) where (X, R) is a poset *)
Definition is_inf X R y A :=
  lower_bound R y A ∧ ∀s, s ∈ X → lower_bound R s A → s ≤[R] y.

(* y = sup(A) where (X, R) is a poset *)
Definition is_sup X R y A :=
  upper_bound R A y ∧ ∀s, s ∈ X → upper_bound R A s → y ≤[R] s.

Definition is_minimal R y A :=
  y ∈ A ∧ ¬∃x, x ∈ A ∧ x ≤[R] y ∧ x ≠ y.

Definition is_maximal R y A :=
  y ∈ A ∧ ¬∃x, x ∈ A ∧ y ≤[R] x ∧ y ≠ x.

Theorem minimum_is_unique R X A y y':
  partial_order R X → y ∈ X → y' ∈ X →
  is_min R y A → is_min R y' A → y = y'.
Proof.
  intros hpo hy hy' hmy hmy'.
  unfold is_min in hmy. destruct hmy as (h, hby).
  unfold is_min in hmy'. destruct hmy' as (h', hby').
  unfold lower_bound in hby. apply hby in h'. clear hby.
  unfold lower_bound in hby'. apply hby' in h. clear hby'.
  exact (hpo.(po_antisym R X) y y' hy hy' h' h).
Qed.

Theorem maximum_is_unique R X A y y':
  partial_order R X → y ∈ X → y' ∈ X →
  is_max R y A → is_max R y' A → y = y'.
Proof.
  intros hpo hy hy' hmy hmy'.
  unfold is_min in hmy. destruct hmy as (h, hby).
  unfold is_min in hmy'. destruct hmy' as (h', hby').
  unfold lower_bound in hby. apply hby in h'. clear hby.
  unfold lower_bound in hby'. apply hby' in h. clear hby'.
  exact (hpo.(po_antisym R X) y y' hy hy' h h').
Qed.

Theorem inf_equi X R y A: y ∈ X →
  is_inf X R y A ↔ is_max R y {s | s ∈ X ∧ lower_bound R s A}.
Proof.
  intro hsy. split.
  * intro h. unfold is_max. split.
    - apply -> comp. repeat split.
      -- exact (set_intro hsy).
      -- exact hsy.
      -- unfold lower_bound. intros x hx.
         unfold is_inf in h. destruct h as (hA, h).
         unfold lower_bound in hA.
         exact (hA x hx).
    - unfold upper_bound. intro x. intro hx.
      apply comp in hx. apply proj2 in hx.
      unfold is_inf in h. apply proj2 in h.
      exact (h x (proj1 hx) (proj2 hx)).
  * intro h. unfold is_inf. split.
    - unfold lower_bound. intros x hx.
      unfold is_max in h. destruct h as (hy, _).
      apply comp in hy. destruct hy as (_, (_, hy)).
      unfold lower_bound in hy.
      exact (hy x hx).
    - intros s hs hbs. unfold is_max in h.
      destruct h as (hy, hby).
      apply comp in hy.
      unfold upper_bound in hby.
      apply (hby s). apply -> comp. repeat split.
      -- exact (set_intro hs).
      -- exact hs. 
      -- exact hbs.
Qed.

Theorem sup_equi X R y A: y ∈ X →
  is_sup X R y A ↔ is_min R y {s | s ∈ X ∧ upper_bound R A s}.
Proof.
  intro hsy. split.
  * intro h. unfold is_min. split.
    - apply -> comp. repeat split.
      -- exact (set_intro hsy).
      -- exact hsy.
      -- unfold upper_bound. intros x hx.
         unfold is_inf in h. destruct h as (hA, h).
         unfold upper_bound in hA.
         exact (hA x hx).
    - unfold lower_bound. intro x. intro hx.
      apply comp in hx. apply proj2 in hx.
      unfold is_inf in h. apply proj2 in h.
      exact (h x (proj1 hx) (proj2 hx)).
  * intro h. unfold is_sup. split.
    - unfold upper_bound. intros x hx.
      unfold is_min in h. destruct h as (hy, _).
      apply comp in hy. destruct hy as (_, (_, hy)).
      unfold upper_bound in hy.
      exact (hy x hx).
    - intros s hs hbs. unfold is_min in h.
      destruct h as (hy, hby).
      apply comp in hy.
      unfold lower_bound in hby.
      apply (hby s). apply -> comp. repeat split.
      -- exact (set_intro hs).
      -- exact hs. 
      -- exact hbs.
Qed.

Theorem minimum_is_minimal X R y A:
  partial_order R X → A ⊆ X →
  is_min R y A → is_minimal R y A.
Proof.
  intros hR hAX h.
  unfold is_min in h. destruct h as (hy, hby).
  unfold is_minimal. split.
  * exact hy.
  * intro hn. destruct hn as (x, (hx, (hxy, hn))).
    unfold lower_bound in hby.
    assert (hyx := hby x hx).
    apply (hAX x) in hx. apply (hAX y) in hy.
    assert (h := hR.(po_antisym R X) x y hx hy hxy hyx).
    exact (hn h).
Qed.

Theorem maximum_is_maximal X R y A:
  partial_order R X → A ⊆ X →
  is_max R y A → is_maximal R y A.
Proof.
  intros hR hAX h.
  unfold is_max in h. destruct h as (hy, hby).
  unfold is_maximal. split.
  * exact hy.
  * intro hn. destruct hn as (x, (hx, (hyx, hn))).
    unfold upper_bound in hby.
    assert (hxy := hby x hx).
    apply (hAX x) in hx. apply (hAX y) in hy.
    assert (h := hR.(po_antisym R X) x y hx hy hxy hyx).
    apply eq_sym in h. exact (hn h).
Qed.

