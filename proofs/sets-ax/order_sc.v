
Require Import Coq.Unicode.Utf8.
Require Import axioms.

Definition lower_bound S M :=
  ∀A, A ∈ M → S ⊆ A.

Definition upper_bound M S :=
  ∀A, A ∈ M → A ⊆ S.

Definition is_inf Y M :=
  lower_bound Y M ∧ ∀S, lower_bound S M → S ⊆ Y.

Definition is_sup Y M :=
  upper_bound M Y ∧ ∀S, upper_bound M S → Y ⊆ S.

Theorem intersection_is_a_lower_bound M:
  lower_bound (⋂M) M.
Proof.
  unfold lower_bound. intros A hA.
  unfold subclass. intros x hx.
  apply comp_elim in hx.
  exact (hx A hA).
Qed.

Theorem union_is_an_upper_bound M:
  upper_bound M (⋃M).
Proof.
  unfold upper_bound. intros A hA.
  unfold subclass. intros x hx.
  apply comp. split.
  * exact (set_intro hx).
  * exists A. exact (conj hA hx).
Qed.

Theorem inf_is_intersection M Y:
  is_inf Y M ↔ Y = ⋂M.
Proof.
  split.
  * intro h. apply subclass_antisym. split.
    - unfold subclass. intros x hx. apply comp. split.
      -- exact (set_intro hx).
      -- intros A hA. unfold is_inf in h.
         apply proj1 in h. unfold lower_bound in h.
         apply h in hA. exact (hA x hx).
    - unfold is_inf in h. apply proj2 in h.
      assert (hM := intersection_is_a_lower_bound M).
      exact (h _ hM).
  * intro h. rewrite h. clear h.
    unfold is_inf. split.
    - exact (intersection_is_a_lower_bound M).
    - intros S hS. unfold subclass. intros x hx.
      apply comp. split.
      -- exact (set_intro hx).
      -- intros A hA. unfold lower_bound in hS.
         exact (hS A hA x hx).
Qed.

Theorem sup_is_union M Y:
  is_sup Y M ↔ Y = ⋃M.
Proof.
  split.
  * intro h. apply subclass_antisym. split.
    - unfold is_sup in h. apply proj2 in h.
      assert (hM := union_is_an_upper_bound M).
      exact (h _ hM).
    - unfold is_sup in h. apply proj1 in h.
      unfold upper_bound in h.
      unfold subclass. intros x hx.
      apply comp_elim in hx.
      destruct hx as (A, (hA, hx)).
      exact (h A hA x hx).
  * intro h. rewrite h. clear h.
    unfold is_sup. split.
    - exact (union_is_an_upper_bound M).
    - intros S hS. unfold subclass. intros x hx.
      apply comp_elim in hx.
      destruct hx as (A, (hA, hx)).
      unfold upper_bound in hS.
      exact (hS A hA x hx).
Qed.
