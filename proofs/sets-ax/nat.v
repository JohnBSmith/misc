
Require Import Coq.Unicode.Utf8.
Require Import axioms.

Theorem intersection_is_lower_bound {A M}:
  A ∈ M → ⋂M ⊆ A.
Proof.
  intro h. unfold Subclass. intro x. intro hx.
  apply comp in hx. destruct hx as (_, hx).
  exact (hx A h).
Qed.

Theorem nat_is_set:
  set ℕ.
Proof.
  destruct infinity as (A, hA).
  assert (h := hA). apply comp in h.
  destruct h as (hsA, _).
  apply intersection_is_lower_bound in hA.
  fold ℕ in hA.  exact (subset ℕ A hsA hA).
Qed.

Theorem empty_set_in_nat:
  ∅ ∈ ℕ.
Proof.
  unfold ℕ. apply -> comp. split.
  * exact empty_set_is_set.
  * intro A. intro hA. apply comp in hA.
    destruct hA as (_, (hA, _)).
    exact hA.
Qed.

Theorem induction_sets A:
  A ⊆ ℕ → (∅ ∈ A ∧ ∀n, n ∈ A → succ n ∈ A) → ℕ = A.
Proof.
  intros h hind. apply subclass_antisym. split.
  * unfold ℕ.
    apply intersection_is_lower_bound.
    apply (subset A ℕ nat_is_set) in h.
    apply -> comp.
    exact (conj h hind).
  * exact h.
Qed.

Theorem induction_sets_brief A:
  A ∈ Inductive → ℕ ⊆ A.
Proof.
  intro h. unfold ℕ.
  apply intersection_is_lower_bound.
  exact h.
Qed.

Theorem succ_is_set n:
  set n → set (succ n).
Proof.
  intro h. unfold succ. apply union2_is_set.
  * exact h.
  * apply sg_is_set. exact h.
Qed.

Theorem nat_is_inductive:
  ℕ ∈ Inductive.
Proof.
  apply -> comp. repeat split.
  * exact nat_is_set.
  * apply -> comp. split.
    - exact empty_set_is_set.
    - intro A. intro hA. apply comp in hA.
      destruct hA as (_, (hA, _)). exact hA.
  * intro n. intro hn. apply comp in hn.
    destruct hn as (hsn, hn). apply -> comp. split.
    - exact (succ_is_set n hsn).
    - intro A. intro hA. assert (h := hA).
      apply comp in h. destruct h as (_, (_, h)).
      apply (hn A) in hA. apply (h n) in hA.
      exact hA.
Qed.

Theorem induction (A: Class → Prop):
  (A ∅ ∧ ∀n, A n → A (succ n)) → (∀n, n ∈ ℕ → A n).
Proof.
  pose (M := {n | n ∈ ℕ ∧ A n}).
  assert (hM := induction_sets M).
  assert (hsub: M ⊆ ℕ). {
    unfold Subclass. intro n. intro hn.
    apply comp in hn. destruct hn as (_, (hn, _)).
    exact hn.
  }
  assert (hM := hM hsub). clear hsub.
  intro h.
  assert (h': ∅ ∈ M ∧ (∀ n : Class, n ∈ M → succ n ∈ M)). {
    destruct h as (h0, hind). split.
    * apply -> comp. repeat split.
      - exact empty_set_is_set.
      - exact empty_set_in_nat.
      - exact h0. 
    * intro n. intro hn. apply -> comp.
      apply comp in hn.
      destruct hn as (hsn, (hn, hA)).
      repeat split.
      - exact (succ_is_set n hsn).
      - assert (h := nat_is_inductive).
        apply comp in h. destruct h as (_, (_, h)).
        exact (h n hn). 
      - exact (hind n hA).
  }
  assert (hM := hM h'). clear h h'.
  intro n. intro hn. rewrite hM in hn.
  apply comp in hn. destruct hn as (_, (_, hn)).
  exact hn.
Qed.

