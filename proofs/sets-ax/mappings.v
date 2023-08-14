
Require Import Coq.Unicode.Utf8.
Require Import axioms.

Definition left_total X f :=
  ∀x, x ∈ X → ∃y, (x, y) ∈ f.

Definition right_uniq f :=
  ∀x y y', (x, y) ∈ f → (x, y') ∈ f → y = y'.

Definition app f x := ⋃ {y | (x, y) ∈ f}.

Definition mapping f X Y :=
  f ⊆ X × Y ∧ left_total X f ∧ right_uniq f.

Definition inj X f := ∀x x', x ∈ X → x' ∈ X →
  app f x = app f x' → x = x'.

Lemma proj_right_uniq {f X Y}: mapping f X Y
  → ∀x y y', (x, y) ∈ f → (x, y') ∈ f → y = y'.
Proof.
  intro h. unfold mapping in h.
  exact (proj2 (proj2 h)).
Qed.

Lemma proj_left_total {f X Y}: mapping f X Y
  → ∀x, x ∈ X → ∃y, (x, y) ∈ f.
Proof.
  intro h. unfold mapping in h.
  exact (proj1 (proj2 h)).
Qed.

Lemma proj_relation {f X Y}:
  mapping f X Y → f ⊆ X × Y.
Proof.
  intro h. unfold mapping in h. exact (proj1 h).
Qed.

Theorem pair_in_mapping {f X Y x y}:
  mapping f X Y → (x, y) ∈ f → x ∈ X ∧ y ∈ Y.
Proof.
  intro hf. intro hxy. apply proj_relation in hf.
  unfold Subclass in hf. apply hf in hxy. clear hf.
  apply prod_elim_term in hxy. exact hxy.
Qed.

Theorem app_iff {f X Y x y}:
  mapping f X Y → x ∈ X → ((x, y) ∈ f ↔ y = app f x).
Proof.
  intros hf hx. split.
  * intro h. unfold app. apply ext. intro u. split.
    - intro hu. apply union_intro. exists y. split.
      -- apply -> comp. split.
         --- assert (hxy := pair_in_mapping hf h).
             exact (set_intro (proj2 hxy)).
         --- exact h.
      -- exact hu.
    - intro hu. apply union_elim in hu.
      destruct hu as (y', (h', huy')).
      apply comp in h'. apply proj2 in h'.
      assert (hyy' := proj_right_uniq hf x y y' h h').
      rewrite <- hyy' in huy'. exact huy'.
  * intro h. assert (hflt := proj_left_total hf x hx).
    destruct hflt as (y', hy').
    assert (heq: y' = app f x). {
      apply ext. intro u. split.
      * intro hu. unfold app. apply union_intro.
        exists y'. split.
        - apply -> comp. split.
          --- assert (hxy' := pair_in_mapping hf hy').
              exact (set_intro (proj2 hxy')).
          --- exact hy'.
        - exact hu.
      * intro hu. apply union_elim in hu.
        destruct hu as (y'', (hy'', huy'')).
        apply comp in hy''. apply proj2 in hy''.
        assert (hyy'' := proj_right_uniq
          hf x y' y'' hy' hy'').
        rewrite <- hyy'' in huy''.
        exact huy''.
    }
    rewrite <- heq in h. rewrite <- h in hy'.
    exact hy'.
Qed.

Lemma mapping_ext_lemma {X Y f g}:
  mapping f X Y → mapping g X Y
  → (∀x, app f x = app g x) → f ⊆ g.
Proof.
  intro hf. intro hg. intro h. unfold Subclass. intro t.
  intro ht. assert (hrel := proj_relation hf).
  unfold Subclass in hrel. assert (h0 := hrel t ht).
  clear hrel. apply prod_elim in h0.
  destruct h0 as (x, (y, (hx, (hy, htxy)))).
  assert (h := h x). rewrite htxy in ht.
  apply (app_iff hf hx) in ht.
  rewrite h in ht.
  apply (app_iff hg hx) in ht.
  rewrite <- htxy in ht. exact ht.
Qed.

Theorem mapping_ext {X Y f g}:
  mapping f X Y → mapping g X Y
  → (∀x, app f x = app g x) → f = g.
Proof.
  intro hf. intro hg. intro h.
  assert (hfg := mapping_ext_lemma hf hg h).
  assert (h': ∀x, app g x = app f x). {
    intro x. apply eq_sym. exact (h x).
  }
  assert (hgf := mapping_ext_lemma hg hf h').
  apply ext. intro x. split.
  * intro hx. exact (hfg x hx). 
  * intro hx. exact (hgf x hx).
Qed.

Definition composition g f :=
  {t | ∃x y z, t = (x, z) ∧ (y, z) ∈ g ∧ (x, y) ∈ f}.
Notation "g ∘ f" := (composition g f) (at level 40): class_scope.

Theorem composition_is_mapping {X Y Z f g}:
  mapping f X Y → mapping g Y Z → mapping (g ∘ f) X Z.
Proof.
  intros hf hg. unfold mapping. repeat split.
  * unfold Subclass. intro t. intro h.
    apply comp in h. destruct h as (ht, h).
    destruct h as (x, (y, (z, (hxz, (hyz, hxy))))).
    assert (h0 := pair_in_mapping hf hxy).
    assert (h1 := pair_in_mapping hg hyz).
    apply -> comp. split.
    - exact ht.
    - exists x. exists z. repeat split.
      -- exact (proj1 h0).
      -- exact (proj2 h1).
      -- exact hxz.
  * unfold left_total. intros x hx.
    assert (h0 := proj_left_total hf x hx).
    destruct h0 as (y, hxy).
    assert (hy := proj2 (pair_in_mapping hf hxy)).
    assert (h2 := proj_left_total hg y hy).
    destruct h2 as (z, hyz).
    assert (hz := proj2 (pair_in_mapping hg hyz)).
    exists z. apply -> comp. split.
    - apply pair_is_set.
      exact (conj (set_intro hx) (set_intro hz)).
    - exists x. exists y. exists z. repeat split.
      -- exact hyz.
      -- exact hxy.
  * unfold right_uniq. intros x z z' hxz hxz'.
    apply comp in hxz. destruct hxz as (hsxz, hxz).
    destruct hxz as (x1, (y1, (z1, (h1, (hg1, hf1))))).
    apply pair_is_set_rev in hsxz.
    destruct hsxz as (hsx, hsz).
    apply (pair_eq x z x1 z1 hsx hsz) in h1.
    destruct h1 as (hxx1, hzz1).
    rewrite <- hxx1 in hf1. clear hxx1 x1.
    rewrite <- hzz1 in hg1. clear hzz1 z1.
    apply comp in hxz'. destruct hxz' as (hsxz', hxz').
    destruct hxz' as (x2, (y2, (z2, (h2, (hg2, hf2))))).
    apply pair_is_set_rev in hsxz'.
    destruct hsxz' as (_, hsz').
    apply (pair_eq x z' x2 z2 hsx hsz') in h2.
    destruct h2 as (hxx2, hz'z2).
    rewrite <- hxx2 in hf2. clear hxx2 x2.
    rewrite <- hz'z2 in hg2. clear hz'z2 z2.
    assert (hy := proj_right_uniq hf x y1 y2 hf1 hf2).
    rewrite <- hy in hg2. clear hy hf2 hf1 y2.
    assert (hz := proj_right_uniq hg y1 z z' hg1 hg2).
    exact hz.
Qed.

Theorem app_value_in_cod {X Y f x}:
  mapping f X Y → x ∈ X → app f x ∈ Y.
Proof.
  intros hf hx. unfold set.
  set (y := app f x).
  assert (h: y = app f x) by reflexivity.
  apply (app_iff hf hx) in h.
  apply (pair_in_mapping hf) in h.
  exact (proj2 h).
Qed.

Theorem composition_eq {X Y Z g f x}:
  mapping f X Y → mapping g Y Z → x ∈ X →
  app (g ∘ f) x = app g (app f x).
Proof.
  intros hf hg hx.
  assert (hgf := composition_is_mapping hf hg).
  apply eq_sym. apply (app_iff hgf hx).
  apply -> comp. split.
  * assert (h := app_value_in_cod hf hx).
    apply (app_value_in_cod hg) in h.
    apply set_intro in h.
    apply pair_is_set. split.
    - exact (set_intro hx).
    - exact h.
  * set (y := app f x). set (z := app g y).
    assert (hy := app_value_in_cod hf hx). fold y in hy.
    exists x. exists y. exists z. repeat split.
    - apply (app_iff hg hy). reflexivity.
    - apply (app_iff hf hx). reflexivity.
Qed.

Theorem composition_of_injections {X Y Z f g}:
  mapping f X Y → mapping g Y Z
  → inj X f → inj Y g → inj X (g ∘ f).
Proof.
  intros hfm hgm hf hg.
  assert (hm := composition_is_mapping hfm hgm).
  unfold inj. intros x x' hx hx' h.
  rewrite (composition_eq hfm hgm hx) in h.
  rewrite (composition_eq hfm hgm hx') in h.
  assert (hy  := app_value_in_cod hfm hx).
  assert (hy' := app_value_in_cod hfm hx').
  unfold inj in hf. unfold inj in hg.
  apply (hg _ _ hy hy') in h.
  apply (hf x x' hx hx') in h.
  exact h.
Qed.

