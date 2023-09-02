
Require Import Coq.Unicode.Utf8.
Require Import axioms.

Definition BinaryRel := Class → Class → Prop.

Definition graph_as_rel (G: Class): BinaryRel :=
  fun x y => (x, y) ∈ G.

Definition refl M (R: BinaryRel) :=
  ∀x, x ∈ M → R x x.

Definition sym M (R: BinaryRel) :=
  ∀x y, x ∈ M → y ∈ M → R x y → R y x.

Definition trans M (R: BinaryRel) :=
  ∀x y z, x ∈ M → y ∈ M → z ∈ M →
  R x y → R y z → R x z.

Definition antisym M (R: BinaryRel) :=
  ∀x y, x ∈ M → y ∈ M →
  R x y → R y x → x = y.

Definition total M (R: BinaryRel) :=
  ∀x y, x ∈ M → y ∈ M → R x y ∨ R y x.

Definition antirefl M (R: BinaryRel) :=
  ¬∃x, x ∈ M ∧ R x x.

Theorem pair_in_relation {X Y x y R}:
  (x, y) ∈ R → R ⊆ X × Y → x ∈ X ∧ y ∈ Y.
Proof.
  intro hxy. intro hR. unfold subclass in hR.
  assert (h := hR (x, y) hxy).
  exact (prod_elim_term h).
Qed.

Theorem inv_rel_inv_img R Y:
  inv_img R Y = img (inv R) Y.
Proof.
  apply ext. intro x. split.
  * intro h. apply comp. split.
    - exact (set_intro h).
    - apply comp in h. destruct h as (hx, h).
      destruct h as (y, (hy, hxy)).
      exists y. split.
      -- exact hy.
      -- apply comp. split.
         --- apply pair_is_set.
             exact (conj (set_intro hy) hx).
         --- exists y. exists x. split.
             ---- reflexivity.
             ---- exact hxy.
  * intro h. apply comp. split.
    - exact (set_intro h).
    - apply comp in h. destruct h as (hsx, h).
      destruct h as (y, (hy, hyx)).
      exists y. split.
      -- exact hy.
      -- apply comp_elim in hyx.
         destruct hyx as (y', (x', (hyx, hR))).
         assert (hsy := (set_intro hy)).
         apply (pair_eq y x y' x' hsy hsx) in hyx.
         destruct hyx as (hyy', hxx').
         rewrite hyy'. rewrite hxx'.
         exact hR.
Qed.

Theorem img_union2 R A B:
  img R (A ∪ B) = img R A ∪ img R B.
Proof.
  apply ext. intro y. split.
  * intro h. apply union2_intro.
    apply comp in h. destruct h as (hy, h).
    destruct h as (x, (hx, hxy)).
    apply union2_elim in hx.
    destruct hx as [hl | hr].
    - left. apply comp. split.
      -- exact hy.
      -- exists x. exact (conj hl hxy).
    - right. apply comp. split.
      -- exact hy.
      -- exists x. exact (conj hr hxy).
  * intro h. apply comp. split.
    - exact (set_intro h).
    - apply union2_elim in h.
      destruct h as [hl | hr].
      -- apply comp_elim in hl.
         destruct hl as (x, (hx, hxy)).
         exists x. split.
         --- apply union2_intro. left. exact hx.
         --- exact hxy.
      -- apply comp_elim in hr.
         destruct hr as (x, (hx, hxy)).
         exists x. split.
         --- apply union2_intro. right. exact hx.
         --- exact hxy.
Qed.

Theorem img_intersection2 R A B:
  img R (A ∩ B) ⊆ img R A ∩ img R B.
Proof.
  unfold subclass. intro y. intro h.
  apply intersection2_intro.
  apply comp in h. destruct h as (hy, h).
  destruct h as (x, (hx, hxy)).
  apply intersection2_elim in hx. split.
  * apply comp. split.
    - exact hy.
    - exists x. exact (conj (proj1 hx) hxy).
  * apply comp. split.
    - exact hy.
    - exists x. exact (conj (proj2 hx) hxy).
Qed.

Theorem inv_img_union2 R A B:
  inv_img R (A ∪ B) = inv_img R A ∪ inv_img R B.
Proof.
  repeat rewrite inv_rel_inv_img.
  apply img_union2.
Qed.

Theorem inv_img_intersection2 R A B:
  inv_img R (A ∩ B) ⊆ inv_img R A ∩ inv_img R B.
Proof.
  repeat rewrite inv_rel_inv_img.
  apply img_intersection2.
Qed.

Theorem img_difference R A B:
  (img R A) \ (img R B) ⊆ img R (A \ B).
Proof.
  unfold subclass. intro y. intro h.
  apply difference_elim in h.
  destruct h as (hA, hnB).
  apply comp. split.
  * exact (set_intro hA).
  * apply comp_elim in hA.
    destruct hA as (x, (hx, hxy)).
    exists x. split.
    - apply difference_intro. split.
      -- exact hx.
      -- intro hB. contradiction hnB.
         apply comp. split.
         --- apply set_intro in hxy.
             apply pair_is_set_rev in hxy.
             exact (proj2 hxy).
         --- exists x. exact (conj hB hxy).
    - exact hxy.
Qed.

Theorem inv_relation_subset {R X Y}:
  R ⊆ X × Y → inv R ⊆ Y × X.
Proof.
  intro h. unfold subclass. intros t ht.
  apply comp_elim in ht.
  destruct ht as (y, (x, (ht, hxy))).
  apply h in hxy. rewrite ht. clear t ht.
  apply prod_elim_term in hxy as (hx, hy).
  apply prod_intro. exists y. exists x.
  repeat split.
  * exact hy.
  * exact hx.
Qed.

Theorem inv_relation_is_set {R X Y}:
  R ⊆ X × Y → set X → set Y → set (inv R).
Proof.
  intros hR hsX hsY.
  apply inv_relation_subset in hR.
  assert (hprod := prod_is_set hsY hsX).
  exact (subset _ _ hprod hR).
Qed.

Theorem dom_subclass_left {R X Y}:
  R ⊆ X × Y → dom R ⊆ X.
Proof.
  intro h. unfold subclass. intros x hx.
  apply comp_elim in hx.
  destruct hx as (y, hxy).
  apply h in hxy.
  apply prod_elim_term in hxy.
  exact (proj1 hxy).
Qed.

Theorem rng_subclass_right {R X Y}:
  R ⊆ X × Y → rng R ⊆ Y.
Proof.
  intro h. unfold subclass. intros y hy.
  apply comp_elim in hy.
  destruct hy as (x, hxy).
  apply h in hxy.
  apply prod_elim_term in hxy.
  exact (proj2 hxy).
Qed.

Theorem rel_img_subclass_cod {X Y R A}:
  R ⊆ X × Y → A ⊆ X → img R A ⊆ Y.
Proof.
  intros hR hAX. unfold subclass. intros y hy.
  apply comp_elim in hy.
  destruct hy as (x, (hx, hxy)).
  apply hR in hxy. apply prod_elim_term in hxy.
  exact (proj2 hxy).
Qed.

Theorem rel_inv_img_subclass_src {X Y R B}:
  R ⊆ X × Y → B ⊆ Y → inv_img R B ⊆ X.
Proof.
  intros hR hBY. unfold subclass. intros x hx.
  apply comp_elim in hx.
  destruct hx as (y, (hy, hxy)).
  apply hR in hxy. apply prod_elim_term in hxy.
  exact (proj1 hxy).
Qed.
