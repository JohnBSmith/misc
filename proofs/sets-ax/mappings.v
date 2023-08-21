
Require Import Coq.Unicode.Utf8.
Require Import axioms.

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
      -- apply comp. split.
         --- assert (hxy := pair_in_mapping hf h).
             exact (set_intro (proj2 hxy)).
         --- exact h.
      -- exact hu.
    - intro hu. apply union_elim in hu.
      destruct hu as (y', (h', huy')).
      apply comp_elim in h'.
      assert (hyy' := proj_right_uniq hf x y y' h h').
      rewrite <- hyy' in huy'. exact huy'.
  * intro h. assert (hflt := proj_left_total hf x hx).
    destruct hflt as (y', hy').
    assert (heq: y' = app f x). {
      apply ext. intro u. split.
      * intro hu. unfold app. apply union_intro.
        exists y'. split.
        - apply comp. split.
          --- assert (hxy' := pair_in_mapping hf hy').
              exact (set_intro (proj2 hxy')).
          --- exact hy'.
        - exact hu.
      * intro hu. apply union_elim in hu.
        destruct hu as (y'', (hy'', huy'')).
        apply comp_elim in hy''.
        assert (hyy'' := proj_right_uniq
          hf x y' y'' hy' hy'').
        rewrite <- hyy'' in huy''.
        exact huy''.
    }
    rewrite <- heq in h. rewrite <- h in hy'.
    exact hy'.
Qed.

(*
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
*)

Lemma mapping_ext_lemma {X Y f g}:
  mapping f X Y → mapping g X Y
  → (∀x, x ∈ X → app f x = app g x) → f ⊆ g.
Proof.
  intro hf. intro hg. intro h. unfold Subclass. intro t.
  intro ht. assert (hrel := proj_relation hf).
  unfold Subclass in hrel. assert (h0 := hrel t ht).
  clear hrel. apply prod_elim in h0.
  destruct h0 as (x, (y, (hx, (hy, htxy)))).
  assert (h := h x). rewrite htxy in ht.
  apply (app_iff hf hx) in ht.
  rewrite (h hx) in ht.
  apply (app_iff hg hx) in ht.
  rewrite <- htxy in ht. exact ht.
Qed.

Theorem mapping_ext {X Y f g}:
  mapping f X Y → mapping g X Y
  → (∀x, x ∈ X → app f x = app g x) → f = g.
Proof.
  intro hf. intro hg. intro h.
  assert (hfg := mapping_ext_lemma hf hg h).
  assert (h': ∀x, x ∈ X → app g x = app f x). {
    intros x hx. apply eq_sym. exact (h x hx).
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
    apply comp. split.
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
    exists z. apply comp. split.
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
  apply comp. split.
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

Theorem outside_of_domain X Y f x:
  mapping f X Y → x ∉ X → app f x = ∅.
Proof.
  intro hf. intro hnx. apply ext. intro u. split.
  * intro h. apply comp in h.
    destruct h as (hsu, (y, (hy, hu))).
    apply comp in hy. destruct hy as (hsy, hxy).
    apply proj_relation in hf. unfold Subclass in hf.
    apply hf in hxy. clear hf.
    apply prod_elim_term in hxy.
    destruct hxy as (hx, _). exfalso.
    exact (hnx hx).
  * intro hu. exfalso. exact (empty_set_property hu).
Qed.

Theorem dom_is_dom X Y f:
  mapping f X Y → dom f = X.
Proof.
  intro hf. apply ext. intro x. split.
  * intro h. apply comp_elim in h.
    destruct h as (y, hxy).
    apply (pair_in_mapping hf) in hxy.
    exact (proj1 hxy).
  * intro hx. apply comp. split.
    - exact (set_intro hx).
    - exact (proj_left_total hf x hx).
Qed.

Theorem cod_subclass_rng_implies_sur Y f:
  Y ⊆ rng f → sur Y f.
Proof.
  intros hf. unfold sur. intro y. intro hy.
  apply hf in hy. apply comp_elim in hy.
  exact hy.
Qed.

Theorem empty_set_is_mapping Y:
  mapping ∅ ∅ Y.
Proof.
  unfold mapping. repeat split.
  * unfold Subclass. intro t. intro ht.
    exfalso. exact (empty_set_property ht).
  * unfold left_total. intros x hx.
    exfalso. exact (empty_set_property hx).
  * unfold right_uniq. intros x y y' hxy hxy'.
    exfalso. exact (empty_set_property hxy).
Qed.

Definition graph_from X (f: Class → Class) :=
  {t | ∃x, x ∈ X ∧ t = (x, f x)}.

Theorem graph_is_mapping X Y (f: Class → Class):
  (∀x, x ∈ X → f x ∈ Y) →
  mapping (graph_from X f) X Y.
Proof.
  intro htotal. set (Gf := graph_from X f).
  unfold mapping. repeat split.
  * unfold Subclass. intros t ht.
    apply comp in ht.
    destruct ht as (hst, (x, (hx, ht))).
    apply comp. split.
    - exact hst.
    - exists x. exists (f x). repeat split.
      -- exact hx.
      -- exact (htotal x hx).
      -- exact ht.
  * unfold left_total. intros x hx.
    exists (f x). apply comp. split.
    - apply pair_is_set. split.
      -- exact (set_intro hx).
      -- exact (set_intro (htotal x hx)).
    - exists x. split.
      -- exact hx.
      -- reflexivity.
  * unfold right_uniq. intros x y1 y2 hy1 hy2.
    apply comp_elim in hy1.
    apply comp_elim in hy2.
    destruct hy1 as (x1, (hx1, h1)).
    destruct hy2 as (x2, (hx2, h2)).
    assert (hy1 := htotal x1 hx1).
    assert (hy2 := htotal x2 hx2).
    apply eq_sym in h1.
    apply eq_sym in h2.
    apply (pair_eq _ _ _ _
      (set_intro hx1) (set_intro hy1)) in h1.
    apply (pair_eq _ _ _ _
      (set_intro hx2) (set_intro hy2)) in h2.
    destruct h1 as (h1x, h1y).
    destruct h2 as (h2x, h2y).
    rewrite <- h1y. rewrite <- h2y.
    rewrite h1x. rewrite h2x.
    reflexivity.
Qed.

Theorem app_graph X f x:
  x ∈ X → set (f x) → app (graph_from X f) x = f x.
Proof.
  intros hx hsfx. apply ext. intro u. split.
  * intro h. apply comp_elim in h.
    destruct h as (y, (hy, hu)).
    apply comp_elim in hy.
    apply comp in hy. destruct hy as (hxy, hy).
    destruct hy as (x0, (hx0, heq)).
    apply pair_is_set_rev in hxy.
    destruct hxy as (hsx, hsy).
    apply (pair_eq _ _ _ _ hsx hsy) in heq.
    destruct heq as (h1, h2).
    rewrite h1. rewrite <- h2. exact hu.
  * intro h. apply comp. split.
    - exact (set_intro h).
    - exists (f x). split.
      -- apply comp. split.
         --- exact hsfx.
         --- apply comp. split.
             ---- apply pair_is_set.
                  exact (conj (set_intro hx) hsfx).
             ---- exists x. split.
                  ----- exact hx.
                  ----- reflexivity.
      -- exact h.
Qed.

Theorem dom_subclass_inv_img_cod X Y f:
  mapping f X Y → X ⊆ inv_img f Y.
Proof.
  intros hf. unfold Subclass. intros x hx.
  apply comp. split.
  * exact (set_intro hx).
  * exists (app f x). split.
    - exact (app_value_in_cod hf hx).
    - apply (app_iff hf hx). reflexivity.
Qed.

Theorem img_as_union {X Y f A}: mapping f X Y →
  A ⊆ X → img f A = ⋃{sgy | ∃x, x ∈ A ∧ sgy = SgSet (app f x)}.
Proof.
  intros hf hAX. apply ext. intro y. split.
  * intro hy. apply comp in hy.
    destruct hy as (hsy, (x, (hx, hxy))).
    apply union_intro. exists (SgSet y). split.
    - apply comp. split.
      -- exact (sg_is_set y hsy).
      -- exists x. split.
         --- exact hx.
         --- apply hAX in hx.
             apply (app_iff hf hx) in hxy.
             rewrite <- hxy. reflexivity.
    - apply comp. split.
      -- exact hsy.
      -- intros _. reflexivity.
  * intro hy. apply comp in hy.
    destruct hy as (hsy, (sgy, (hsgy, hy))).
    apply comp in hsgy.
    destruct hsgy as (hssgy, (x, (hx, heq))).
    apply comp. split.
    - exact hsy.
    - exists x. split.
      -- exact hx.
      -- rewrite heq in hssgy.
         apply sg_is_set_rev in hssgy.
         rewrite heq in hy. clear heq.
         apply comp_elim in hy.
         apply hy in hssgy as heq. clear hy hssgy.
         apply hAX in hx.
         apply (app_iff hf hx). exact heq.
Qed.

Theorem sur_img X Y f:
  mapping f X Y → sur Y f → Y = img f X.
Proof.
  intros hf h. apply ext. intros y. split.
  * intro hy. apply comp. split.
    - exact (set_intro hy).
    - unfold sur in h. destruct (h y hy) as (x, hxy).
      clear h hy. exists x.
      assert (hx := proj1 (pair_in_mapping hf hxy)).
      exact (conj hx hxy).
  * intro hy. apply comp_elim in hy.
    destruct hy as (x, (_, hxy)).
    exact (proj2 (pair_in_mapping hf hxy)).
Qed.

Theorem from_cod_proper_class {X Y f}:
  mapping f X Y → sur Y f → ¬set Y → ¬set X.
Proof.
  intros hf h hnsY hsX.
  assert (hXX := subclass_refl X).
  assert (hsY := replacement X Y f X hf hXX hsX).
  rewrite <- (sur_img X Y f hf h) in hsY.
  exact (hnsY hsY).
Qed.

Theorem graph_proper_class {X Y f}:
  mapping f X Y → ¬set X → ¬set f.
Proof.
  intro hf. intro hn.
  pose (g := graph_from f (fun t => ⋃⋂t)).
  assert (hg: mapping g f X). {
    apply graph_is_mapping. clear g. intros t ht.
    assert (hxy := proj_relation hf t ht).
    apply prod_elim in hxy.
    destruct hxy as (x, (y, (hx, (hy, heq)))).
    assert (hsx := set_intro hx).
    assert (hsy := set_intro hy).
    rewrite heq. rewrite <- (pair_proj1 x y hsx hsy).
    exact hx.
  }
  assert (hsur: sur X g). {
    unfold sur. intros x hx.
    pose (y := app f x).
    assert (hxy: (x, y) ∈ f). {
      apply (app_iff hf hx). reflexivity.
    }
    assert (hy := proj2 (pair_in_mapping hf hxy)).
    assert (hsx := set_intro hx).
    assert (hsy := set_intro hy).
    exists (x, y). apply (app_iff hg).
    * exact hxy.
    * assert (heq := pair_proj1 x y hsx hsy).
      unfold g. rewrite (app_graph f).
      - exact heq.
      - exact hxy.
      - rewrite <- heq. exact hsx.
  }
  exact (from_cod_proper_class hg hsur hn).
Qed.

Theorem graph_is_set {X Y f}:
  mapping f X Y → set f → set X.
Proof.
  intros hf hsf.
  assert (h := graph_proper_class hf).
  apply DNE. intro hnsX. exact (h hnsX hsf).
Qed.

Theorem inv_img_subclass_dom X Y B f:
  mapping f X Y → inv_img f B ⊆ X.
Proof.
  intros hf. unfold Subclass. intros x hx.
  apply comp_elim in hx.
  destruct hx as (y, (hy, hxy)).
  apply (pair_in_mapping hf) in hxy.
  exact (proj1 hxy).
Qed.

Theorem inv_img_is_set_from_dom {X Y f} B:
  mapping f X Y → set X → set (inv_img f B).
Proof.
  intros hf hsX.
  apply (inv_img_subclass_dom X Y B f) in hf.
  exact (subset _ X hsX hf).
Qed.

Theorem inv_img_is_set_from_graph {X Y f} B:
  mapping f X Y → set f → set (inv_img f B).
Proof.
  intros hf hsf.
  assert (hsX := graph_is_set hf hsf).
  exact (inv_img_is_set_from_dom B hf hsX).
Qed.

Theorem inv_img_restr f M B:
  inv_img (restr f M) B = M ∩ inv_img f B.
Proof.
  apply ext. intro x. split.
  * intro h.
    apply comp_elim in h.
    destruct h as (y, (hy, hxy)).
    apply comp in hxy.
    destruct hxy as (hsxy, (hxy, (x0, (y0, (hx, heq))))).
    apply pair_is_set_rev in hsxy as (hsx, hsy).
    apply (pair_eq x y _ _ hsx hsy) in heq as (hxx0, _).
    rewrite <- hxx0 in hx. clear hxx0 x0 y0.
    apply intersection2_intro. split.
    - exact hx.
    - apply comp. split.
      -- exact hsx.
      -- exists y. exact (conj hy hxy).
  * intro h. apply intersection2_elim in h.
    destruct h as (hx, h).
    apply comp_elim in h.
    destruct h as (y, (hy, hxy)).
    apply comp. split.
    - exact (set_intro hx).
    - exists y. split.
      -- exact hy.
      -- apply comp. repeat split.
         --- apply pair_is_set. split.
             ---- exact (set_intro hx).
             ---- exact (set_intro hy).
         --- exact hxy.
         --- exists x. exists y. split.
             ---- exact hx.
             ---- reflexivity.
Qed.

Theorem restr_subclass_prod {f X Y M}:
  mapping f X Y → M ⊆ X → restr f M ⊆ M × Y.
Proof.
  intros hf hMX. unfold Subclass. intros t ht.
  apply comp_elim in ht.
  destruct ht as (ht, (x, (y, (hx, hxy)))).
  apply comp. split.
  * exact (set_intro ht).
  * exists x. exists y. repeat split.
    - exact hx.
    - rewrite hxy in ht.
      apply (pair_in_mapping hf) in ht.
      exact (proj2 ht).
    - exact hxy.
Qed.

Theorem restr_is_mapping {f X Y M}:
  mapping f X Y → M ⊆ X → mapping (restr f M) M Y.
Proof.
  intros hf hMX. unfold mapping. repeat split.
  * exact (restr_subclass_prod hf hMX).
  * unfold left_total. intros x hx.
    assert (h := proj_left_total hf x (hMX x hx)).
    destruct h as (y, hxy).
    exists y. apply comp. repeat split.
    -- exact (set_intro hxy).
    -- exact hxy.
    -- exists x. exists y. split.
       --- exact hx.
       --- reflexivity.
  * unfold right_uniq. intros x y1 y2 hy1 hy2.
    apply comp_elim in hy1. apply proj1 in hy1.
    apply comp_elim in hy2. apply proj1 in hy2.
    assert (h := proj_right_uniq hf).
    exact (h x y1 y2 hy1 hy2).
Qed.

Theorem restr_subclass_graph f M:
  restr f M ⊆ f.
Proof.
  unfold Subclass. intros t ht.
  apply comp_elim in ht. exact (proj1 ht).
Qed.

Theorem restr_is_set_from_graph f M:
  set f → set (restr f M).
Proof.
  intro hf. assert (h := restr_subclass_graph f M).
  exact (subset _ f hf h).
Qed.

Theorem restr_is_set {f X Y M}:
  set X → set Y → mapping f X Y → M ⊆ X → set (restr f M).
Proof.
  intros hsX hsY hf hMX.
  assert (hsub := restr_subclass_prod hf hMX).
  assert (h: set (M × Y)). {
    apply prod_is_set.
    * exact (subset M X hsX hMX).
    * exact hsY.
  }
  apply (subset _ _ h hsub).
Qed.

