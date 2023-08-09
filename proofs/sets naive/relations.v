
Load "axioms.v".

Definition img R X :=
  {y | ∃x, x ∈ X ∧ (x, y) ∈ R}.

Theorem pair_in_relation {X Y x y R}:
  (x, y) ∈ R → R ⊆ X × Y → x ∈ X ∧ y ∈ Y.
Proof.
  intro hxy. intro hR. unfold Subset in hR.
  assert (h := hR (x, y) hxy).
  apply prod_elim in h.
  destruct h as (x', (y', (hx', (hy', heq)))).
  apply pair_eq in heq. destruct heq as (hx, hy).
  rewrite hx. rewrite hy.
  exact (conj hx' hy').
Qed.

Theorem img_union2 R A B:
  img R (A ∪ B) = img R A ∪ img R B.
Proof.
  apply set_ext. intro y. split.
  * intro h. apply union2_intro.
    apply comp_elim in h. simpl in h.
    destruct h as (x, (hx, hxy)).
    apply union2_elim in hx.
    destruct hx as [hl | hr].
    - left. apply comp_intro.
      exists x. exact (conj hl hxy).
    - right. apply comp_intro.
      exists x. exact (conj hr hxy).
  * intro h. apply comp_intro.
    apply union2_elim in h.
    destruct h as [hl | hr].
    - apply comp_elim in hl. simpl in hl.
      destruct hl as (x, (hx, hxy)).
      exists x. split.
      -- apply union2_intro. left. exact hx.
      -- exact hxy.
    - apply comp_elim in hr. simpl in hr.
      destruct hr as (x, (hx, hxy)).
      exists x. split.
      -- apply union2_intro. right. exact hx.
      -- exact hxy.
Qed.

Theorem img_intersection2 R A B:
  img R (A ∪ B) ⊆ img R A ∪ img R B.
Proof.
  unfold Subset. intro y. intro h.
  apply union2_intro.
  apply comp_elim in h. simpl in h.
  destruct h as (x, (hx, hxy)).
  apply union2_elim in hx.
  destruct hx as [hl | hr].
  * left. apply comp_intro.
    exists x. exact (conj hl hxy).
  * right. apply comp_intro.
    exists x. exact (conj hr hxy).
Qed.

