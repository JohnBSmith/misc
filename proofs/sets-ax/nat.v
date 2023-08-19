
Require Import Coq.Unicode.Utf8.
Require Import axioms.
Require Import basic.
Require Import mappings.

Theorem intersection_is_lower_bound {A M}:
  A ∈ M → ⋂M ⊆ A.
Proof.
  intro h. unfold Subclass. intro x. intro hx.
  apply comp_elim in hx. exact (hx A h).
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

Theorem succ_is_set n:
  set n → set (succ n).
Proof.
  intro h. unfold succ. apply union2_is_set.
  * exact h.
  * apply sg_is_set. exact h.
Qed.

Theorem empty_set_in_nat:
  ∅ ∈ ℕ.
Proof.
  unfold ℕ. apply comp. split.
  * exact empty_set_is_set.
  * intro A. intro hA. apply comp in hA.
    destruct hA as (_, (hA, _)).
    exact hA.
Qed.

Theorem succ_in_nat {n}:
  n ∈ ℕ → succ n ∈ ℕ.
Proof.
  intro hn. apply comp. split.
  * apply succ_is_set. exact (set_intro hn).
  * apply comp_elim in hn.
    intros A hA. assert (hn := hn A hA).
    apply comp_elim in hA. apply proj2 in hA.
    exact (hA n hn).
Qed.

Theorem induction_sets A:
  A ⊆ ℕ → (∅ ∈ A ∧ ∀n, n ∈ A → succ n ∈ A) → ℕ = A.
Proof.
  intros h hind. apply subclass_antisym. split.
  * unfold ℕ.
    apply intersection_is_lower_bound.
    apply (subset A ℕ nat_is_set) in h.
    apply comp.
    exact (conj h hind).
  * exact h.
Qed.

Theorem induction_sets_brief A:
  A ∈ InductiveSets → ℕ ⊆ A.
Proof.
  intro h. unfold ℕ.
  apply intersection_is_lower_bound.
  exact h.
Qed.

Theorem nat_is_inductive:
  ℕ ∈ InductiveSets.
Proof.
  apply comp. repeat split.
  * exact nat_is_set.
  * apply comp. split.
    - exact empty_set_is_set.
    - intro A. intro hA. apply comp in hA.
      destruct hA as (_, (hA, _)). exact hA.
  * intro n. intro hn. apply comp in hn.
    destruct hn as (hsn, hn). apply comp. split.
    - exact (succ_is_set n hsn).
    - intro A. intro hA. assert (h := hA).
      apply comp in h. destruct h as (_, (_, h)).
      apply (hn A) in hA. apply (h n) in hA.
      exact hA.
Qed.

Theorem induction (A: Class → Prop):
  A ∅ ∧ (∀n, n ∈ ℕ → A n → A (succ n)) →
  (∀n, n ∈ ℕ → A n).
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
    * apply comp. repeat split.
      - exact empty_set_is_set.
      - exact empty_set_in_nat.
      - exact h0. 
    * intro n. intro hn. apply comp.
      apply comp in hn.
      destruct hn as (hsn, (hn, hA)).
      repeat split.
      - exact (succ_is_set n hsn).
      - assert (h := nat_is_inductive).
        apply comp in h. destruct h as (_, (_, h)).
        exact (h n hn). 
      - exact (hind n hn hA).
  }
  assert (hM := hM h'). clear h h'.
  intro n. intro hn. rewrite hM in hn.
  apply comp in hn. destruct hn as (_, (_, hn)).
  exact hn.
Qed.

Local Lemma empty_union2 {A B}:
  A ∪ B = ∅ → A = ∅.
Proof.
  intro heq. apply ext. intro x. split.
  * intro hx.
    assert (h: x ∈ A ∪ B). {
      apply union2_intro. left. exact hx.
    }
    rewrite heq in h. exact h.
  * intro hx. exfalso. exact (empty_set_property hx).
Qed.

Theorem zero_is_not_a_successor:
  ∀n, n ∈ ℕ → succ n ≠ ∅.
Proof.
  apply induction. split.
  * intro h. unfold succ in h.
    rewrite union2_com in h.
    rewrite union2_neutral in h.
    assert (hcontra: ∅ ∈ (SgSet ∅)). {
      apply comp. split.
      * exact empty_set_is_set.
      * intros _. reflexivity.
    }
    rewrite h in hcontra.
    exact (empty_set_property hcontra).
  * intros n _ ih. intro h.
    unfold succ in h at 1.
    apply empty_union2 in h.
    exact (ih h).
Qed.

Theorem union_succ n:
  n ∈ ℕ → ⋃(succ n) = n.
Proof.
  revert n. apply induction. split.
  * unfold succ. rewrite union2_com.
    rewrite union2_neutral.
    rewrite <- (union_sg _ empty_set_is_set).
    reflexivity.
  * intros n hn ih. unfold succ at 1.
    rewrite union_union2.
    rewrite ih. clear ih.
    assert (hs := succ_is_set n (set_intro hn)).
    rewrite <- (union_sg _ hs).
    unfold succ at 1. rewrite union2_assoc.
    rewrite union2_idem. unfold succ.
    reflexivity.
Qed.

Theorem succ_is_inj m n:
  m ∈ ℕ → n ∈ ℕ → succ m = succ n → m = n.
Proof.
  intros hm hn h.
  apply (f_equal (fun u => ⋃u)) in h.
  rewrite (union_succ n hn) in h.
  rewrite (union_succ m hm) in h.
  exact h.
Qed.

Definition rec_eq x0 φ f :=
  app f ∅ = x0 ∧ ∀n, app f (succ n) = app φ (app f n).

Theorem rec_def_uniqueness X x0 φ: x0 ∈ ℕ → mapping φ X X →
  ∀f1 f2, mapping f1 ℕ X → mapping f2 ℕ X
  → rec_eq x0 φ f1 → rec_eq x0 φ f2 → f1 = f2.
Proof.
  intros hx0 hphi f1 f2 hf1 hf2 hr1 hr2.
  apply (mapping_ext hf1 hf2).
  apply induction. split.
  * apply proj1 in hr1. apply proj1 in hr2.
    rewrite hr1. rewrite hr2. reflexivity.
  * intros n hn ih.
    apply proj2 in hr1. apply proj2 in hr2.
    rewrite hr1. rewrite hr2. rewrite ih.
    reflexivity.
Qed.

Theorem rec_def_existence X x0 φ:
  set X → x0 ∈ X → mapping φ X X →
  ∃f, mapping f ℕ X ∧ rec_eq x0 φ f.
Proof.
  intro hsX. intro hx0. intro hphi.
  pose (M := {A | A ⊆ ℕ × X ∧ (∅, x0) ∈ A ∧
    ∀n x, (n, x) ∈ A → (succ n, app φ x) ∈ A}).
  assert (hprod: ℕ × X ∈ M). {
    apply comp. repeat split.
    * exact (prod_is_set nat_is_set hsX).
    * apply subclass_refl.
    * apply prod_intro_term. split.
      - exact empty_set_in_nat.
      - exact hx0.
    * intros n x hnx. apply prod_elim_term in hnx.
      destruct hnx as (hn, hx).
      apply prod_intro_term. split.
      - exact (succ_in_nat hn).
      - exact (app_value_in_cod hphi hx).
  }
  pose (G := ⋂M).
  assert (hG: G ∈ M). {
    apply comp. repeat split.
    * admit.
    * unfold Subclass. intros t ht.
      apply comp_elim in ht. exact (ht _ hprod).
    * apply comp. split.
      - apply pair_is_set. split.
        -- exact empty_set_is_set.
        -- exact (set_intro hx0).
      - intros A hA. apply comp_elim in hA.
        exact (proj1 (proj2 hA)).
    * intros n x hnx. apply comp. split.
      - admit.
      - intros A hA. assert (h := hA).
        apply comp_elim in h.
        apply proj2 in h. apply proj2 in h.
        apply h. clear h.
        apply comp_elim in hnx. apply hnx.
        exact hA.
  }
  (* todo *)
Admitted.
