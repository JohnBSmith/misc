
Load "relations.v".

Definition left_total (X Y f: set) :=
  ∀x, x ∈ X → ∃y, y ∈ Y ∧ (x, y) ∈ f.

Definition right_uniq (X Y f: set) :=
  ∀x y y', x ∈ X → y ∈ Y → y' ∈ Y →
    (x, y) ∈ f → (x, y') ∈ f → y = y'.

Definition Abb (X Y: set) :=
  {f ∈ 𝓟 (X × Y) | left_total X Y f ∧ right_uniq X Y f}.

Theorem proj_subset_prod {X Y f: set}:
  f ∈ Abb X Y → f ⊆ X × Y.
Proof.
  intro h. apply sep in h. apply proj1 in h.
  apply power_set_axiom in h. exact h.
Qed.

Theorem proj_left_total {X Y f: set}:
  f ∈ Abb X Y → ∀x, x ∈ X → ∃y, y ∈ Y ∧ (x, y) ∈ f.
Proof.
  intro h. apply sep in h. apply proj2 in h.
  apply proj1 in h. exact h.
Qed.

Theorem proj_right_uniq {X Y f: set}:
  f ∈ Abb X Y → ∀x y y', 
    (x, y) ∈ f → (x, y') ∈ f → y = y'.
Proof.
  intro hf. intros x y y'. intro hfy. intro hfy'.
  apply sep in hf. destruct hf as (hf, (hflt, hfru)).
  apply power_set_axiom in hf.
  assert (hxy := pair_in_relation X Y x y f hfy hf).
  assert (hxy' := pair_in_relation X Y x y' f hfy' hf).
  destruct hxy as (hx, hy).
  destruct hxy' as (_, hy').
  unfold right_uniq in hfru.
  exact (hfru x y y' hx hy hy' hfy hfy').
Qed.

Definition inv_img (X f B: set) :=
  {x ∈ X | ∃y, y ∈ B ∧ (x, y) ∈ f}.

Theorem preimg_intersection (X Y f A B: set):
  f ∈ Abb X Y → A ⊆ Y → B ⊆ Y →
    inv_img X f (A ∩ B) = (inv_img X f A) ∩ (inv_img X f B).
Proof.
  intros hf hAY hBY.
  apply set_ext. intro x. split.
  * intro h. apply sep in h.
    destruct h as (hx, (y, (hyAB, hxyf))).
    apply intersection2_elim in hyAB.
    destruct hyAB as (hyA, hyB).
    apply intersection2_intro. split.
    - apply sep. split.
      -- exact hx.
      -- exists y. exact (conj hyA hxyf). 
    - apply sep. split.
      -- exact hx.
      -- exists y. exact (conj hyB hxyf).
  * intro h. apply intersection2_elim in h.
    destruct h as (hA, hB).
    apply sep in hA. destruct hA as (hx, (y, (hy, hfy))).
    apply sep in hB. destruct hB as (_, (y', (hy', hfy'))).
    apply sep. split.
    - exact hx.
    - exists y.
      assert (hyY := hAY y hy). clear hAY.
      assert (hy'Y := hBY y' hy'). clear hBY.
      assert (huniq := proj_right_uniq hf).
      assert (hyy' := huniq x y y' hfy hfy').
      clear huniq. rewrite <- hyy' in hy'. clear hyy'.
      split.
      -- apply intersection2_intro. exact (conj hy hy').
      -- exact hfy.
Qed.

Definition app (Y f x: set): set :=
  ⋃{y ∈ Y | (x, y) ∈ f}.

Theorem application_iff (X Y f x y: set):
  x ∈ X → f ∈ Abb X Y → (y = app Y f x ↔ (x, y) ∈ f).
Proof.
  intro hx. intro hf.
  split.
  * intro h.
    assert (hflt := proj_left_total hf).
    destruct (hflt x hx) as (y', (_, hy')).
    assert (heq: y' = app Y f x). {
      apply set_ext. intro u. split.
      * intro hu. apply union_axiom.
        exists y'. split.
        - exact hu.
        - apply sep. split.
          -- apply proj_subset_prod in hf.
             apply (pair_in_relation X Y x y' f hy') in hf.
             exact (proj2 hf).
          -- exact hy'.
      * intro hu. apply union_axiom in hu.
        destruct hu as (y'', (hu, hy'')).
        apply sep in hy''. apply proj2 in hy''.
        assert (hfru := proj_right_uniq hf).
        assert (heq := hfru x y' y'' hy' hy'').
        rewrite heq. exact hu.
    }
    rewrite <- h in heq. rewrite heq in hy'.
    exact hy'.
  * intro h. apply set_ext. intro u. split.
    - intro hu. unfold app.
      apply union_axiom. exists y.
      split.
      -- exact hu.
      -- apply sep. split.
         --- apply proj_subset_prod in hf.
             apply (pair_in_relation X Y x y f h) in hf.
             exact (proj2 hf).
         --- exact h.
    - intro hu. unfold app in hu.
      apply union_axiom in hu.
      destruct hu as (y', (hu, hy')).
      apply sep in hy'. destruct hy' as (hy', hxy').
      assert (hfru := proj_right_uniq hf).
      assert (heq := hfru x y y' h hxy').
      rewrite heq. exact hu.
Qed.

Theorem img_in_dom (X Y f x: set):
  f ∈ Abb X Y → x ∈ X → app Y f x ∈ Y.
Proof.
  intro hf. intro hx. set (y := app Y f x).
  assert (hy: y = app Y f x). {
    reflexivity.
  }
  apply (application_iff X Y f x y hx hf) in hy.
  assert (hfrel := proj_subset_prod hf).
  assert (hxy := pair_in_relation X Y x y f hy hfrel).
  exact (proj2 hxy).
Qed.

Definition composition (X Y Z g f: set) :=
  {t ∈ Prod X Z | ∃x z, t = (x, z) ∧ z = app Z g (app Y f x)}.

Theorem composition_is_mapping (X Y Z g f: set):
  f ∈ Abb X Y → g ∈ Abb Y Z → (composition X Y Z g f) ∈ Abb X Z.
Proof.
  intro hf. intro hg. set (gf := composition X Y Z g f).
  apply sep. repeat split.
  * apply power_set_axiom. intro t. intro ht.
    apply sep in ht. apply proj1 in ht. exact ht.
  * unfold left_total. intro x. intro hx.
    pose (y := app Y f x).
    pose (z := app Z g y).
    assert (hy := img_in_dom X Y f x hf hx).
    assert (hz := img_in_dom Y Z g y hg hy).
    exists z. split.
    - exact hz.
    - apply sep. split.
      -- exact (prod_intro_term hx hz).
      -- exists x. exists z. split.
         --- reflexivity.
         --- reflexivity.
  * unfold right_uniq.
    intros x z z' hx hz hz' hxz hxz'.
    apply sep in hxz. apply proj2 in hxz.
    destruct hxz as (x0, (z0, (hp0, ha0))).
    apply pair_eq in hp0. destruct hp0 as (hxx0, hzz0).
    rewrite <- hxx0 in ha0. rewrite <- hzz0 in ha0.
    apply sep in hxz'. apply proj2 in hxz'.
    destruct hxz' as (x1, (z1, (hp1, ha1))).
    apply pair_eq in hp1. destruct hp1 as (hxx1, hzz1).
    rewrite <- hxx1 in ha1. rewrite <- hzz1 in ha1.
    rewrite <- ha1 in ha0. exact ha0.
Qed.

