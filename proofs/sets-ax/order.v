
Require Import Coq.Unicode.Utf8.
Require Import axioms.
Require Import relations.

Definition partial_order X R :=
  refl X R ∧ antisym X R ∧ trans X R.

Definition total_order X R :=
  partial_order X R ∧ total X R.

Definition lower_bound (R: BinaryRel) s A :=
  ∀x, x ∈ A → R s x.

Definition upper_bound (R: BinaryRel) A s :=
  ∀x, x ∈ A → R x s.

(* y = min(A) *)
Definition is_min R y A :=
  y ∈ A ∧ lower_bound R y A.

(* y = max(A) *)
Definition is_max R y A :=
  y ∈ A ∧ upper_bound R A y.

(* y = inf(A) where (X, R) is a poset *)
Definition is_inf X R y A :=
  lower_bound R y A ∧ ∀s, s ∈ X → lower_bound R s A → R s y.

(* y = sup(A) where (X, R) is a poset *)
Definition is_sup X R y A :=
  upper_bound R A y ∧ ∀s, s ∈ X → upper_bound R A s → R y s.

Definition is_minimal R y A :=
  y ∈ A ∧ ¬∃x, x ∈ A ∧ R x y ∧ x ≠ y.

Definition is_maximal R y A :=
  y ∈ A ∧ ¬∃x, x ∈ A ∧ R y x ∧ y ≠ x.

Theorem subclass_is_partial_order:
  partial_order UnivCl subclass.
Proof.
  unfold partial_order. repeat split.
  * unfold refl. intros x _.
    exact (subclass_refl x).
  * unfold antisym. intros x y _ _ hxy hyx.
    exact (subclass_antisym (conj hxy hyx)).
  * unfold trans. intros x y z _ _ _ hxy hyz.
    exact (subclass_trans (conj hxy hyz)).
Qed.

Theorem minimum_is_unique X R A y y':
  partial_order X R → y ∈ X → y' ∈ X →
  is_min R y A → is_min R y' A → y = y'.
Proof.
  intros hpo hy hy' hmy hmy'.
  unfold is_min in hmy. destruct hmy as (h, hby).
  unfold is_min in hmy'. destruct hmy' as (h', hby').
  unfold lower_bound in hby. apply hby in h'. clear hby.
  unfold lower_bound in hby'. apply hby' in h. clear hby'.
  assert (hantisym := (proj1 (proj2 hpo))).
  exact (hantisym y y' hy hy' h' h).
Qed.

Theorem maximum_is_unique X R A y y':
  partial_order X R → y ∈ X → y' ∈ X →
  is_max R y A → is_max R y' A → y = y'.
Proof.
  intros hpo hy hy' hmy hmy'.
  unfold is_min in hmy. destruct hmy as (h, hby).
  unfold is_min in hmy'. destruct hmy' as (h', hby').
  unfold lower_bound in hby. apply hby in h'. clear hby.
  unfold lower_bound in hby'. apply hby' in h. clear hby'.
  assert (hantisym := (proj1 (proj2 hpo))).
  exact (hantisym y y' hy hy' h h').
Qed.

Theorem inf_equi X R y A: y ∈ X →
  is_inf X R y A ↔ is_max R y {s | s ∈ X ∧ lower_bound R s A}.
Proof.
  intro hsy. split.
  * intro h. unfold is_max. split.
    - apply comp. repeat split.
      -- exact (set_intro hsy).
      -- exact hsy.
      -- unfold lower_bound. intros x hx.
         unfold is_inf in h. destruct h as (hA, h).
         unfold lower_bound in hA.
         exact (hA x hx).
    - unfold upper_bound. intro x. intro hx.
      apply comp_elim in hx.
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
      apply (hby s). apply comp. repeat split.
      -- exact (set_intro hs).
      -- exact hs. 
      -- exact hbs.
Qed.

Theorem sup_equi X R y A: y ∈ X →
  is_sup X R y A ↔ is_min R y {s | s ∈ X ∧ upper_bound R A s}.
Proof.
  intro hsy. split.
  * intro h. unfold is_min. split.
    - apply comp. repeat split.
      -- exact (set_intro hsy).
      -- exact hsy.
      -- unfold upper_bound. intros x hx.
         unfold is_inf in h. destruct h as (hA, h).
         unfold upper_bound in hA.
         exact (hA x hx).
    - unfold lower_bound. intro x. intro hx.
      apply comp_elim in hx.
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
      apply (hby s). apply comp. repeat split.
      -- exact (set_intro hs).
      -- exact hs. 
      -- exact hbs.
Qed.

Theorem minimum_is_minimal X R y A:
  partial_order X R → A ⊆ X →
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
    assert (hantisym := (proj1 (proj2 hR))).
    assert (h := hantisym x y hx hy hxy hyx).
    exact (hn h).
Qed.

Theorem maximum_is_maximal X R y A:
  partial_order X R → A ⊆ X →
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
    assert (hantisym := (proj1 (proj2 hR))).
    assert (h := hantisym x y hx hy hxy hyx).
    apply eq_sym in h. exact (hn h).
Qed.
