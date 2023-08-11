
Load "axioms.v".

Definition img R X :=
  {y | ∃x, x ∈ X ∧ (x, y) ∈ R}.

Definition inv_img R Y :=
  {x | ∃y, y ∈ Y ∧ (x, y) ∈ R}.

Definition inv_rel R :=
  {t | ∃y x, t = (y, x) ∧ (x, y) ∈ R}.

Theorem pair_in_relation {X Y x y R}:
  (x, y) ∈ R → R ⊆ X × Y → x ∈ X ∧ y ∈ Y.
Proof.
  intro hxy. intro hR. unfold Subclass in hR.
  assert (h := hR (x, y) hxy).
  apply prod_elim in h.
  destruct h as (x', (y', (hx', (hy', heq)))).
  apply eq_sym in heq.
  assert (hset := (conj
    (set_intro hx') (set_intro hy'))).
  apply (pair_eq x' y' x y hset) in heq.
  destruct heq as (hx, hy).
  rewrite hx in hx'. rewrite hy in hy'.
  exact (conj hx' hy').
Qed.

Theorem inv_rel_inv_img R Y:
  inv_img R Y = img (inv_rel R) Y.
Proof.
  apply ext. intro x. split.
  * intro h. apply -> comp. split.
    - exact (set_intro h).
    - apply comp in h. destruct h as (hx, h).
      destruct h as (y, (hy, hxy)).
      exists y. split.
      -- exact hy.
      -- apply -> comp. split.
         --- apply pair_is_set.
             exact (conj (set_intro hy) hx).
         --- exists y. exists x. split.
             ---- reflexivity.
             ---- exact hxy.
  * intro h. apply -> comp. split.
    - exact (set_intro h).
    - apply comp in h. destruct h as (hx, h).
      destruct h as (y, (hy, hyx)).
      exists y. split.
      -- exact hy.
      -- apply comp in hyx. apply proj2 in hyx.
         destruct hyx as (y', (x', (hyx, hR))).
         assert (hset := (conj (set_intro hy) hx)).
         apply (pair_eq y x y' x' hset) in hyx.
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
    - left. apply -> comp. split.
      -- exact hy.
      -- exists x. exact (conj hl hxy).
    - right. apply -> comp. split.
      -- exact hy.
      -- exists x. exact (conj hr hxy).
  * intro h. apply -> comp. split.
    - exact (set_intro h).
    - apply union2_elim in h.
      destruct h as [hl | hr].
      -- apply comp in hl. apply proj2 in hl.
         destruct hl as (x, (hx, hxy)).
         exists x. split.
         --- apply union2_intro. left. exact hx.
         --- exact hxy.
      -- apply comp in hr. apply proj2 in hr.
         destruct hr as (x, (hx, hxy)).
         exists x. split.
         --- apply union2_intro. right. exact hx.
         --- exact hxy.
Qed.

Theorem img_intersection2 R A B:
  img R (A ∪ B) ⊆ img R A ∪ img R B.
Proof.
  unfold Subclass. intro y. intro h.
  apply union2_intro.
  apply comp in h. destruct h as (hy, h).
  destruct h as (x, (hx, hxy)).
  apply union2_elim in hx.
  destruct hx as [hl | hr].
  * left. apply -> comp. split.
    - exact hy.
    - exists x. exact (conj hl hxy).
  * right. apply -> comp. split.
    - exact hy.
    - exists x. exact (conj hr hxy).
Qed.

Theorem inv_img_union2 R A B:
  inv_img R (A ∪ B) = inv_img R A ∪ inv_img R B.
Proof.
  repeat rewrite inv_rel_inv_img.
  apply img_union2.
Qed.

Theorem inv_img_intersection2 R A B:
  inv_img R (A ∪ B) ⊆ inv_img R A ∪ inv_img R B.
Proof.
  repeat rewrite inv_rel_inv_img.
  apply img_intersection2.
Qed.
