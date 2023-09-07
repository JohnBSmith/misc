
Require Import Coq.Unicode.Utf8.
Require Import axioms.
Require Import basic.
Require Import mappings.
Require Import card.
Require Import nat.

Definition Abb X Y := {f | mapping f X Y}.

Theorem card_refl X:
  card_eq X X.
Proof.
  unfold card_eq. exists (id X). split.
  * exact (id_is_mapping X).
  * exact (id_is_bijective X).
Qed.

Theorem card_sym {X Y}:
  card_eq X Y → card_eq Y X.
Proof.
  intro h. unfold card_eq in h.
  destruct h as (f, (hf, hbf)).
  unfold card_eq. exists (inv f).
  split.
  * exact (inv_of_bij_is_mapping hf hbf).
  * exact (inv_of_bij_is_bij hf hbf).
Qed.

Theorem card_zero {X}:
  card_eq X ∅ → X = ∅.
Proof.
  intros hX.
  unfold card_eq in hX.
  destruct hX as (f, (hf, hbf)).
  apply ext. intro x. split.
  * intro hx. exfalso.
    apply (app_value_in_cod hf) in hx.
    exact (empty_set_property hx).
  * intro hx. exfalso.
    exact (empty_set_property hx).
Qed.

Theorem empty_mapping Y:
  mapping ∅ ∅ Y.
Proof.
  unfold mapping. split; [| split].
  * unfold subclass. intros t ht.
    exfalso. exact (empty_set_property ht).
  * unfold left_total. intros x hx.
    exfalso. exact (empty_set_property hx).
  * unfold right_uniq. intros x y1 y2 hy1 hy2.
    exfalso. exact (empty_set_property hy1).
Qed.

Theorem Abb_empty_mapping Y:
  Abb ∅ Y = (SgSet ∅).
Proof.
  apply ext. intros f. split.
  * intros hf. apply comp. split.
    - exact (set_intro hf).
    - intros _. apply comp_elim in hf.
      apply proj_relation in hf.
      rewrite prod_left_empty in hf.
      apply subclass_antisym. split.
      -- exact hf.
      -- unfold subclass. intros t ht.
         exfalso. exact (empty_set_property ht).
  * intros hf. apply comp_elim in hf.
    assert (hf := hf empty_set_is_set).
    rewrite hf. clear hf.
    apply comp. split.
    - exact empty_set_is_set.
    - exact (empty_mapping Y).
Qed.

Theorem card_non_empty {X k}:
  card_eq X (succ k) → X ≠ ∅.
Proof.
  intro hX. intros heq.
  rewrite heq in hX. clear heq.
  apply card_sym in hX.
  apply card_zero in hX.
  assert (h := empty_set_is_not_a_successor k).
  exact (h hX).
Qed.

Theorem diff_sg_subclass X x:
  X \ SgSet x ⊆ X.
Proof.
  unfold subclass. intros u hu.
  apply difference_elim in hu.
  exact (proj1 hu).
Qed.

Theorem rng_subclass_cod {X Y f}:
  mapping f X Y → rng f ⊆ Y.
Proof.
  intros hf. unfold subclass. intros y hy.
  apply comp_elim in hy.
  destruct hy as (x, hxy).
  apply (pair_in_mapping hf) in hxy.
  exact (proj2 hxy).
Qed.

Theorem restr_cod_to_rng {X Y f}:
  mapping f X Y → mapping f X (rng f).
Proof.
  intros hf. unfold mapping. split; [| split].
  * unfold subclass. intros t ht.
    apply prod_intro.
    assert (hprod := proj_relation hf).
    assert (h := hprod t ht).
    apply prod_elim in h.
    destruct h as (x, (y, (hx, (hy, heq)))).
    exists x. exists y. split; [| split].
    - exact hx.
    - apply comp. split.
      -- exact (set_intro hy).
      -- exists x. rewrite <- heq. exact ht.
    - exact heq. 
  * exact (proj_left_total hf).
  * exact (proj_right_uniq hf).
Qed.
