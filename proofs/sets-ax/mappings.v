
Require Import Coq.Unicode.Utf8.
Require Import axioms.
Require Import relations.

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
  unfold subclass in hf. apply hf in hxy. clear hf.
  apply prod_elim_term in hxy. exact hxy.
Qed.

Theorem mapping_property {X Y f x}:
  mapping f X Y → x ∈ X → ∃!y, set y ∧ (x, y) ∈ f.
Proof.
  intros hf hx. unfold ex_uniq. split.
  * assert (hlt := proj_left_total hf x hx).
    destruct hlt as (y, hxy).
    assert (hy := proj2 (pair_in_mapping hf hxy)).
    apply set_intro in hy.
    exists y. exact (conj hy hxy).
  * intros y1 y2 ((_, hy1), (_, hy2)).
    exact (proj_right_uniq hf x y1 y2 hy1 hy2).
Qed.

Theorem mapping_property_rev {X Y f}:
  f ⊆ X × Y → (∀x, x ∈ X → ∃!y, (x, y) ∈ f)
  → mapping f X Y.
Proof.
  intros hfsub hf. unfold mapping. split; [| split].
  * exact hfsub.
  * unfold left_total. intros x hx.
    exact (proj1 (hf x hx)).
  * unfold right_uniq. intros x y1 y2 h1 h2.
    assert (h := h1). apply hfsub in h.
    apply prod_elim_term in h as (hx, _).
    assert (h := hf x hx). apply proj2 in h.
    apply h. exact (conj h1 h2).
Qed.

Theorem app_iff {f X Y x y}:
  mapping f X Y → x ∈ X → ((x, y) ∈ f ↔ y = app f x).
Proof.
  intros hf hx.
  assert (h := mapping_property hf hx).
  unfold app. fold (iota (fun y => (x, y) ∈ f)).
  split.
  * intro hxy. apply iota_property_rev.
    - exact h.
    - split.
      -- apply (pair_in_mapping hf) in hxy.
         exact (set_intro (proj2 hxy)).
      -- exact hxy.
  * intro hxy.
    exact (iota_property y h hxy).
Qed.

Lemma mapping_ext_lemma {X Y f g}:
  mapping f X Y → mapping g X Y
  → (∀x, x ∈ X → app f x = app g x) → f ⊆ g.
Proof.
  intro hf. intro hg. intro h. unfold subclass. intro t.
  intro ht. assert (hrel := proj_relation hf).
  unfold subclass in hrel. assert (h0 := hrel t ht).
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
  * unfold subclass. intro t. intro h.
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

Theorem composition_of_surjections {X Y Z f g}:
  mapping f X Y → mapping g Y Z
  → sur Y f → sur Z g → sur Z (g ∘ f).
Proof.
  intros hf hg hsf hsg. unfold sur. intros z hz.
  unfold sur in hsf. unfold sur in hsg.
  destruct (hsg z hz) as (y, hyz).
  assert (hy := proj1 (pair_in_mapping hg hyz)).
  destruct (hsf y hy) as (x, hxy).
  assert (hx := proj1 (pair_in_mapping hf hxy)).
  exists x. apply comp. split.
  * apply pair_is_set. split.
    - exact (set_intro hx).
    - exact (set_intro hz).
  * exists x. exists y. exists z. repeat split.
    - exact hyz.
    - exact hxy.
Qed.

Theorem composition_of_bijections {X Y Z f g}:
  mapping f X Y → mapping g Y Z
  → bij X Y f → bij Y Z g → bij X Z (g ∘ f).
Proof.
  intros hf hg hbf hbg. unfold bij.
  unfold bij in hbf. destruct hbf as (hif, hsf).
  unfold bij in hbg. destruct hbg as (hig, hsg).
  split.
  * exact (composition_of_injections hf hg hif hig).
  * exact (composition_of_surjections hf hg hsf hsg).
Qed.

Theorem inj_from_composition {X Y Z f g}:
  mapping f X Y → mapping g Y Z →
  inj X (g ∘ f) → inj X f.
Proof.
  intros hf hg h.
  unfold inj. intros x1 x2 hx1 hx2 heq.
  apply (f_equal (fun y => app g y)) in heq.
  rewrite <- (composition_eq hf hg hx1) in heq.
  rewrite <- (composition_eq hf hg hx2) in heq.
  unfold inj in h.
  exact (h x1 x2 hx1 hx2 heq).
Qed.

Theorem sur_from_composition {X Y Z f g}:
  mapping f X Y → mapping g Y Z →
  sur Z (g ∘ f) → sur Z g.
Proof.
  intros hf hg h.
  unfold sur. intros z hz.
  unfold sur in h.
  destruct (h z hz) as (x, hxz).
  clear h.
  assert (hgf := composition_is_mapping hf hg).
  assert (hxy := pair_in_mapping hgf hxz).
  destruct hxy as (hx, _).
  apply (app_iff hgf hx) in hxz.
  rewrite (composition_eq hf hg hx) in hxz.
  assert (hy := app_value_in_cod hf hx).
  apply (app_iff hg hy) in hxz.
  exists (app f x). exact hxz.
Qed.

Theorem inj_from_composition_sur {X Y Z f g}:
  mapping f X Y → mapping g Y Z →
  inj X (g ∘ f) → sur Y f → inj Y g.
Proof.
  intros hf hg hi hs.
  unfold inj. intros y1 y2 hy1 hy2 heq.
  unfold sur in hs.
  destruct (hs y1 hy1) as (x1, h1).
  destruct (hs y2 hy2) as (x2, h2).
  assert (hx1 := proj1 (pair_in_mapping hf h1)).
  assert (hx2 := proj1 (pair_in_mapping hf h2)).
  apply (app_iff hf hx1) in h1.
  apply (app_iff hf hx2) in h2.
  rewrite h1. rewrite h1 in heq.
  rewrite h2. rewrite h2 in heq.
  clear hs h1 h2.
  rewrite <- (composition_eq hf hg hx1) in heq.
  rewrite <- (composition_eq hf hg hx2) in heq.
  unfold inj in hi.
  apply (hi x1 x2 hx1 hx2) in heq.
  apply (f_equal (fun x => app f x)) in heq.
  exact heq.
Qed.

Theorem outside_of_domain {X Y f x}:
  mapping f X Y → x ∉ X → app f x = UnivCl.
Proof.
  intro hf. intro hnx.
  assert (hempty: {y | (x, y) ∈ f} = ∅). {
    apply ext. intro y. split.
    * intro h. exfalso. apply comp_elim in h.
      apply (pair_in_mapping hf) in h.
      exact (hnx (proj1 h)).
    * intro hy. exfalso.
      exact (empty_set_property hy).
  }
  unfold app. rewrite hempty.
  exact intersection_empty_set.
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

Theorem graph_subclass_dom_times_rng {X Y f}:
  mapping f X Y → f ⊆ X × rng f.
Proof.
  intro hf. unfold subclass. intros t ht.
  apply comp. split.
  * exact (set_intro ht).
  * assert (hprod := proj_relation hf).
    assert (h := hprod t ht). clear hprod.
    apply prod_elim in h.
    destruct h as (x, (y, (hx, (hy, hxy)))).
    exists x. exists y. repeat split.
    - exact hx.
    - apply comp. split.
      -- exact (set_intro hy).
      -- exists x. rewrite hxy in ht. exact ht.
    - exact hxy.
Qed.

Theorem empty_set_is_mapping Y:
  mapping ∅ ∅ Y.
Proof.
  unfold mapping. repeat split.
  * unfold subclass. intro t. intro ht.
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
  * unfold subclass. intros t ht.
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

Theorem app_graph_from_set X f x:
  x ∈ X → set (f x) → app (graph_from X f) x = f x.
Proof.
  intros hx hsfx. symmetry.
  assert (h: set (f x) ∧ (x, f x) ∈ graph_from X f). {
    split.
    * exact hsfx.
    * apply comp. split.
      - apply set_intro in hx.
        exact (pair_is_set (conj hx hsfx)).
      - exists x. split.
        -- exact hx.
        -- reflexivity.
  }
  apply iota_property_rev.
  * unfold ex_uniq. split.
    - exists (f x). exact h.
    - intros y1 y2 ((hsy1, hy1), (hsy2, hy2)).
      apply comp_elim in hy1.
      apply comp_elim in hy2.
      destruct hy1 as (x1, (_, h1)).
      destruct hy2 as (x2, (_, h2)).
      apply set_intro in hx.
      apply (pair_eq _ _ _ _ hx hsy1) in h1.
      apply (pair_eq _ _ _ _ hx hsy2) in h2.
      destruct h1 as (h11, h12).
      destruct h2 as (h21, h22).
      rewrite h12. rewrite h22.
      rewrite <- h11. rewrite <- h21.
      reflexivity.
  * exact h.
Qed.

Theorem app_graph {X Y f x}:
  x ∈ X → mapping (graph_from X f) X Y →
  app (graph_from X f) x = f x.
Proof.
  intros hx hf.
  assert (h: f x ⊆ app (graph_from X f) x). {
    unfold subclass. intros u hu.
    apply comp. split.
    * exact (set_intro hu).
    * intros y hy. apply comp_elim in hy.
      apply comp in hy.
      destruct hy as (hsxy, (x0, (hx0, heq))).
      apply pair_is_set_rev in hsxy as (hsx, hsy).
      apply (pair_eq _ _ _ _ hsx hsy) in heq.
      destruct heq as (hxx0, hyy0).
      rewrite <- hxx0 in hyy0.
      rewrite <- hyy0 in hu.
      exact hu.
  }
  assert (hy := app_value_in_cod hf hx).
  apply set_intro in hy.
  apply app_graph_from_set.
  * exact hx.
  * apply (subset h). exact hy.
Qed.

Theorem dom_subclass_inv_img_cod X Y f:
  mapping f X Y → X ⊆ inv_img f Y.
Proof.
  intros hf. unfold subclass. intros x hx.
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

Theorem img_subclass_cod {X Y f A}:
  mapping f X Y → A ⊆ X → img f A ⊆ Y.
Proof.
  intros hf hAX. unfold subclass. intros y hy.
  apply comp_elim in hy.
  destruct hy as (x, (hx, hxy)).
  apply (pair_in_mapping hf) in hxy.
  exact (proj2 hxy).
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

Theorem img_composition {X Y Z f g A}:
  mapping f X Y → mapping g Y Z →
  A ⊆ X → img (g ∘ f) A = img g (img f A).
Proof.
  intros hf hg hAX. apply ext. intro z. split.
  * intro hz. apply comp_elim in hz.
    destruct hz as (x, (hx, hxz)).
    assert (hgf := composition_is_mapping hf hg).
    apply (app_iff hgf (hAX x hx)) in hxz.
    rewrite (composition_eq hf hg (hAX x hx)) in hxz.
    assert (hy := app_value_in_cod hf (hAX x hx)).
    assert (hz := app_value_in_cod hg hy).
    apply comp. split.
    - rewrite <- hxz in hz.
      exact (set_intro hz).
    - exists (app f x). split.
      -- apply comp. split.
         --- apply (set_intro hy).
         --- exists x. split.
             ---- exact hx.
             ---- apply (app_iff hf (hAX x hx)).
                  reflexivity.
      -- apply (app_iff hg hy). exact hxz.
  * intro hz. apply comp_elim in hz.
    destruct hz as (y, (hy, hyz)).
    apply comp_elim in hy.
    destruct hy as (x, (hx, hxy)).
    apply (app_iff hf (hAX x hx)) in hxy.
    assert (hy := app_value_in_cod hf (hAX x hx)).
    rewrite <- hxy in hy.
    apply (app_iff hg hy) in hyz.
    assert (hz := app_value_in_cod hg hy).
    rewrite <- hyz in hz.
    apply comp. split.
    - exact (set_intro hz).
    - exists x. split.
      -- exact hx.
      -- assert (hgf := composition_is_mapping hf hg).
         apply (app_iff hgf (hAX x hx)).
         rewrite (composition_eq hf hg (hAX x hx)).
         rewrite <- hxy. rewrite <- hyz.
         reflexivity.
Qed.

Theorem img_dom_is_rng {X Y f}:
  mapping f X Y → img f X = rng f.
Proof.
  intro hf. apply ext. intro y. split.
  * intro hy. apply comp_elim in hy.
    destruct hy as (x, (hx, hxy)).
    apply comp. split.
    - apply (pair_in_mapping hf) in hxy.
      exact (set_intro (proj2 hxy)).
    - exists x. exact hxy.
  * intro hy. apply comp_elim in hy.
    destruct hy as (x, hxy).
    apply comp. split.
    - apply (pair_in_mapping hf) in hxy.
      exact (set_intro (proj2 hxy)).
    - exists x. split.
      -- apply (pair_in_mapping hf) in hxy.
         exact (proj1 hxy).
      -- exact hxy.
Qed.

Theorem rng_is_set_from_dom {X Y f}:
  mapping f X Y → set X → set (rng f).
Proof.
  intros hf hsX.
  assert (hXX := subclass_refl X).
  assert (hsY := replacement X Y f X hf hXX hsX).
  rewrite (img_dom_is_rng hf) in hsY.
  exact hsY.
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
  pose (g := graph_from f projl).
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
      unfold g. rewrite (app_graph_from_set f).
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

Theorem graph_is_set_from_dom_cod {X Y f}:
  mapping f X Y → set X → set Y → set f.
Proof.
  intros hf hsX hsY.
  assert (hprod := prod_is_set hsX hsY).
  apply proj_relation in hf.
  apply (subset hf). exact hprod.
Qed.

Theorem expand_graph {X Y f}:
  mapping f X Y → f = {t | ∃x, x ∈ X ∧ t = (x, app f x)}.
Proof.
  intro hf. fold (graph_from X (fun x => app f x)).
  pose (G := graph_from X (fun x => app f x)).
  assert (hG: mapping G X Y). {
    apply graph_is_mapping. intros x hx.
    exact (app_value_in_cod hf hx).
  }
  apply (mapping_ext hf hG). intros x hx.
  assert (hsy := set_intro (app_value_in_cod hf hx)).
  assert (heq := app_graph_from_set X (fun x => app f x) x hx hsy).
  simpl in heq. fold G in heq. symmetry. exact heq.
Qed.

Theorem graph_is_set_from_dom {X Y f}:
  mapping f X Y → set X → set f.
Proof.
  intros hf hsX.
  assert (hsrng := rng_is_set_from_dom hf hsX).
  assert (hprod := prod_is_set hsX hsrng).
  assert (hsub := graph_subclass_dom_times_rng hf).
  apply (subset hsub). exact hprod.
Qed.

(* Alternative proof. *)
Goal ∀X Y f,
  mapping f X Y → set X → set f.
Proof.
  intros X Y f. intros hf hsX.
  pose (g := graph_from X (fun x => (x, app f x))).
  assert (hg: mapping g X (X × Y)). {
    apply graph_is_mapping. intros x hx.
    apply prod_intro_term. split.
    * exact hx.
    * exact (app_value_in_cod hf hx).
  }
  assert (hX := subclass_refl X).
  assert (hsimg := replacement X _ g X hg hX hsX).
  assert (hgf: ∀x, x ∈ X → app g x = (x, app f x)). {
    intros x hx. unfold g.
    rewrite (app_graph_from_set X _ x hx).
    * reflexivity.
    * apply pair_is_set. split.
      - exact (set_intro hx).
      - exact (set_intro (app_value_in_cod hf hx)).
  }
  assert (heq: f = img g X). {
    apply ext. intro t. split.
    * intro ht. apply comp. split.
      - exact (set_intro ht).
      - rewrite (expand_graph hf) in ht.
        apply comp_elim in ht.
        destruct ht as (x, (hx, ht)).
        exists x. split.
        -- exact hx.
        -- apply (app_iff hg hx).
           rewrite (hgf x hx). exact ht.
    * intro ht. apply comp_elim in ht.
      destruct ht as (x, (hx, ht)).
      apply (app_iff hg hx) in ht.
      rewrite ht. rewrite (hgf x hx).
      destruct (proj_left_total hf x hx) as (y, hxy).
      assert (hy := hxy).
      apply (app_iff hf hx) in hy.
      rewrite <- hy. exact hxy.
  }
  rewrite heq. exact hsimg.
Qed.

Theorem inv_img_subclass_dom X Y B f:
  mapping f X Y → inv_img f B ⊆ X.
Proof.
  intros hf. unfold subclass. intros x hx.
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
  apply (subset hf). exact hsX.
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
  intros hf hMX. unfold subclass. intros t ht.
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
  unfold subclass. intros t ht.
  apply comp_elim in ht. exact (proj1 ht).
Qed.

Theorem restr_is_set_from_graph f M:
  set f → set (restr f M).
Proof.
  intro hf. assert (h := restr_subclass_graph f M).
  apply (subset h). exact hf.
Qed.

Theorem restr_is_set {f X Y M}:
  set X → set Y → mapping f X Y → M ⊆ X → set (restr f M).
Proof.
  intros hsX hsY hf hMX.
  assert (hsub := restr_subclass_prod hf hMX).
  assert (h: set (M × Y)). {
    apply prod_is_set.
    * apply (subset hMX). exact hsX.
    * exact hsY.
  }
  apply (subset hsub). exact h.
Qed.

Theorem composition_assoc {A B C D f g h}:
  mapping f A B → mapping g B C → mapping h C D →
  h ∘ (g ∘ f) = (h ∘ g) ∘ f.
Proof.
  intros hf hg hh.
  assert (hgf := composition_is_mapping hf hg).
  assert (hhg := composition_is_mapping hg hh).
  assert (hhgf1 := composition_is_mapping hgf hh).
  assert (hhgf2 := composition_is_mapping hf hhg).
  apply (mapping_ext hhgf1 hhgf2). intros x hx.
  assert (h1 := composition_eq hgf hh hx).
  assert (h2 := composition_eq hf hhg hx).
  assert (h3 := composition_eq hf hg hx).
  assert (hy := app_value_in_cod hf hx).
  assert (h4 := composition_eq hg hh hy).
  rewrite h1. rewrite h2.
  rewrite h3. rewrite h4.
  reflexivity.
Qed.

Definition id X := graph_from X (fun x => x).

Theorem id_is_mapping X:
  mapping (id X) X X.
Proof.
  apply graph_is_mapping. intros x hx. exact hx.
Qed.

Theorem id_app {X x}:
  x ∈ X → app (id X) x = x.
Proof.
  intro hx. unfold id. apply app_graph_from_set.
  * exact hx.
  * exact (set_intro hx).
Qed.

Theorem id_img {X A}:
  A ⊆ X → img (id X) A = A.
Proof.
  intro hAX. apply ext. intros x. split.
  * intro h. apply comp_elim in h.
    destruct h as (x0, (hx0, h)).
    assert (hx0' := hAX x0 hx0).
    apply (app_iff (id_is_mapping X) hx0') in h.
    rewrite (id_app hx0') in h.
    rewrite h. exact hx0.
  * intro h. apply comp. split.
    - exact (set_intro h).
    - exists x. split.
      -- exact h.
      -- apply (app_iff (id_is_mapping X) (hAX x h)).
         rewrite (id_app (hAX x h)).
         reflexivity.
Qed.

Theorem id_is_left_neutral {X Y f}:
  mapping f X Y → id Y ∘ f = f.
Proof.
  intro hf. assert(hid := id_is_mapping Y).
  assert (h := composition_is_mapping hf hid).
  apply (mapping_ext h hf). intros x hx.
  rewrite (composition_eq hf hid hx).
  assert (hy := app_value_in_cod hf hx).
  rewrite (id_app hy). reflexivity.
Qed.

Theorem id_is_right_neutral {X Y f}:
  mapping f X Y → f ∘ id X = f.
Proof.
  intro hf. assert (hid := id_is_mapping X).
  assert (h := composition_is_mapping hid hf).
  apply (mapping_ext h hf). intros x hx.
  rewrite (composition_eq hid hf hx).
  rewrite (id_app hx). reflexivity.
Qed.

Theorem id_is_bijective X:
  bij X X (id X).
Proof.
  unfold bij. split.
  * unfold inj. intros x1 x2 h1 h2 h.
    rewrite (id_app h1) in h.
    rewrite (id_app h2) in h.
    exact h.
  * unfold sur. intros x hx. exists x.
    assert (h := id_is_mapping X).
    apply (app_iff h hx).
    rewrite (id_app hx).
    reflexivity.
Qed.

Theorem inv_of_bij_is_mapping {X Y f}:
  mapping f X Y → bij X Y f → mapping (inv f) Y X.
Proof.
  intros hf hbf. unfold bij in hbf.
  destruct hbf as (hif, hsf).
  unfold mapping. repeat split.
  * apply proj_relation in hf.
    exact (inv_relation_subset hf).
  * unfold left_total. intros y hy.
    unfold sur in hsf.
    destruct (hsf y hy) as (x, hxy).
    exists x. apply comp. split.
    - apply pair_is_set.
      apply (pair_in_mapping hf) in hxy as (hx, _).
      exact (conj (set_intro hy) (set_intro hx)).
    - exists y. exists x. split.
      -- reflexivity.
      -- exact hxy.
  * clear hsf.
    unfold right_uniq. intros x y y' hxy hxy'.
    apply comp_elim in hxy.
    apply comp_elim in hxy'.
    destruct hxy as (x0, (y0, (heq0, h0))).
    destruct hxy' as (x1, (y1, (heq1, h1))).
    symmetry in heq0. symmetry in heq1.
    assert (h0xy := pair_in_mapping hf h0).
    assert (h1xy := pair_in_mapping hf h1).
    destruct h0xy as (hy0, hx0).
    destruct h1xy as (hy1, hx1).
    unfold inj in hif.
    assert (h := hif y0 y1 hy0 hy1). clear hif.
    apply (app_iff hf hy0) in h0.
    apply (app_iff hf hy1) in h1.
    apply (pair_eq_from hx0 hy0) in heq0.
    apply (pair_eq_from hx1 hy1) in heq1.
    clear hx0 hy0 hx1 hy1.
    destruct heq0 as (hxx0, hyy0).
    destruct heq1 as (hxx1, hyy1).
    rewrite <- hyy0. rewrite <- hyy1.
    apply h. clear hyy0 hyy1 h.
    rewrite <- h0. rewrite <- h1.
    rewrite hxx0. rewrite hxx1.
    reflexivity.
Qed.

Theorem bij_inv_is_left_inv {X Y f x}:
  mapping f X Y → bij X Y f → x ∈ X →
  app (inv f) (app f x) = x.
Proof.
  intros hf hbf hx. set (y := app f x).
  assert (hy := app_value_in_cod hf hx).
  fold y in hy.
  assert (hinv := inv_of_bij_is_mapping hf hbf).
  symmetry.
  apply (app_iff hinv hy). clear hinv.
  apply comp. split.
  * apply pair_is_set. split.
    - exact (set_intro hy).
    - exact (set_intro hx).
  * exists y. exists x. split.
    - reflexivity.
    - apply (app_iff hf hx). reflexivity.
Qed.

Theorem bij_inv_is_right_inv {X Y f y}:
  mapping f X Y → bij X Y f → y ∈ Y →
  app f (app (inv f) y) = y.
Proof.
  intros hf hbf hy. set (x := app (inv f) y).
  assert (hinv := inv_of_bij_is_mapping hf hbf).
  assert (hx := app_value_in_cod hinv hy).
  fold x in hx.
  symmetry. apply (app_iff hf hx).
  assert (h: x = x) by reflexivity.
  unfold x in h at 2.
  apply (app_iff hinv hy) in h.
  apply comp_elim in h.
  destruct h as (y0, (x0, (heq, hxy))).
  apply (pair_eq_from hy hx) in heq as (hyy0, hxx0).
  rewrite hyy0. rewrite hxx0. exact hxy.
Qed.

Theorem bij_invl {X Y f}:
  mapping f X Y → bij X Y f →
  inv f ∘ f = id X.
Proof.
  intros hf hbf.
  assert (hinv := inv_of_bij_is_mapping hf hbf).
  assert (h := composition_is_mapping hf hinv).
  apply (mapping_ext h (id_is_mapping X)).
  intros x hx. rewrite (id_app hx).
  rewrite (composition_eq hf hinv hx).
  exact (bij_inv_is_left_inv hf hbf hx).
Qed.

Theorem bij_invr {X Y f}:
  mapping f X Y → bij X Y f →
  f ∘ inv f = id Y.
Proof.
  intros hf hbf.
  assert (hinv := inv_of_bij_is_mapping hf hbf).
  assert (h := composition_is_mapping hinv hf).
  apply (mapping_ext h (id_is_mapping Y)).
  intros y hy. rewrite (id_app hy).
  rewrite (composition_eq hinv hf hy).
  exact (bij_inv_is_right_inv hf hbf hy).
Qed.

Theorem inv_of_bij_is_bij {X Y f}:
  mapping f X Y → bij X Y f → bij Y X (inv f).
Proof.
  intros hf hbf.
  assert (hif := proj1 hbf).
  assert (hsf := proj2 hbf).
  unfold bij. split.
  * unfold inj. intros y1 y2 hy1 hy2. intro h.
    unfold sur in hsf.
    destruct (hsf y1 hy1) as (x1, h1).
    destruct (hsf y2 hy2) as (x2, h2).
    assert (hx1 := proj1 (pair_in_mapping hf h1)).
    assert (hx2 := proj1 (pair_in_mapping hf h2)).
    apply (app_iff hf hx1) in h1.
    apply (app_iff hf hx2) in h2.
    rewrite h1 in h. rewrite h2 in h.
    rewrite (bij_inv_is_left_inv hf hbf hx1) in h.
    rewrite (bij_inv_is_left_inv hf hbf hx2) in h.
    rewrite h1. rewrite h2. rewrite h.
    reflexivity.
  * unfold sur. intros x hx.
    exists (app f x).
    assert (hinv := inv_of_bij_is_mapping hf hbf).
    assert (hy := app_value_in_cod hf hx).
    apply (app_iff hinv hy).
    rewrite (bij_inv_is_left_inv hf hbf hx).
    reflexivity.
Qed.

Theorem invl_invr_impl_bij {X Y f}:
  mapping f X Y →
  (∃g, mapping g Y X ∧ g ∘ f = id X) →
  (∃g, mapping g Y X ∧ f ∘ g = id Y) →
  bij X Y f.
Proof.
  intros hf hl hr.
  unfold bij. split.
  * unfold inj.
    intros x1 x2 hx1 hx2 heq.
    destruct hl as (g, (hg, hgf)).
    assert (h1 := f_equal (fun u => app u x1) hgf).
    assert (h2 := f_equal (fun u => app u x2) hgf).
    simpl in h1. simpl in h2.
    rewrite (composition_eq hf hg hx1) in h1.
    rewrite (composition_eq hf hg hx2) in h2.
    rewrite (id_app hx1) in h1.
    rewrite (id_app hx2) in h2.
    apply (f_equal (fun y => app g y)) in heq.
    rewrite h1 in heq. rewrite h2 in heq.
    exact heq.
  * unfold sur. intros y hy.
    destruct hr as (g, (hg, heq)).
    pose (x := app g y). exists x.
    assert (hx := app_value_in_cod hg hy).
    fold x in hx.
    apply (app_iff hf hx).
    symmetry in heq.
    apply (f_equal (fun u => app u y)) in heq.
    rewrite (composition_eq hg hf hy) in heq.
    rewrite (id_app hy) in heq.
    unfold x. exact heq.
Qed.

Theorem bij_uniq_inv {X Y f}:
  mapping f X Y → bij X Y f →
  ∃!g, mapping g Y X ∧ g ∘ f = id X ∧ f ∘ g = id Y.
Proof.
  intros hf hbf.
  unfold ex_uniq. split.
  * exists (inv f). split; [| split].
    - exact (inv_of_bij_is_mapping hf hbf).
    - exact (bij_invl hf hbf).
    - exact (bij_invr hf hbf).
  * intros g1 g2 (hg1, hg2).
    destruct hg1 as (hg1, (h11, h12)).
    destruct hg2 as (hg2, (h21, h22)).
    rewrite <- (id_is_right_neutral hg1).
    rewrite <- h22.
    rewrite (composition_assoc hg2 hf hg1).
    rewrite h11.
    rewrite (id_is_left_neutral hg2).
    reflexivity.
Qed.

Definition img_rel X R :=
  graph_from (Power X) (fun A => img R A).

Definition inv_img_rel Y R :=
  graph_from (Power Y) (fun B => inv_img R B).

Theorem img_rel_is_mapping {X Y R}:
  set Y → R ⊆ X × Y →
  mapping (img_rel X R) (Power X) (Power Y).
Proof.
  intros hsY hR. unfold img_rel.
  apply graph_is_mapping.
  intros A hA. apply comp. split.
  * apply comp in hA as (hsA, hA).
    assert (h := rel_img_subclass_cod hR hA).
    apply (subset h). exact hsY.
  * unfold subclass. intros y hy.
    apply comp_elim in hy.
    destruct hy as (x, (hx, hxy)).
    apply hR in hxy.
    apply prod_elim_term in hxy.
    exact (proj2 hxy).
Qed.

Theorem inv_img_rel_is_mapping {X Y R}:
  set X → R ⊆ X × Y →
  mapping (inv_img_rel Y R) (Power Y) (Power X).
Proof.
  intros hsX hR. unfold inv_img_rel.
  apply graph_is_mapping.
  intros B hB. apply comp. split.
  * apply comp in hB as (hsB, hB).
    assert (h := rel_inv_img_subclass_src hR hB).
    apply (subset h). exact hsX.
  * unfold subclass. intros x hx.
    apply comp_elim in hx.
    destruct hx as (y, (hy, hxy)).
    apply hR in hxy. apply prod_elim_term in hxy.
    exact (proj1 hxy).
Qed.

Theorem img_rel_univ_is_mapping {R}:
  R ⊆ UnivCl × UnivCl → (∀A, set A → set (img R A)) →
  mapping (img_rel UnivCl R) UnivCl UnivCl.
Proof.
  intros hR hsimg. unfold img_rel.
  rewrite power_UnivCl.
  apply graph_is_mapping.
  intros A hA. apply comp in hA as (hsA, _).
  apply comp. exact (conj (hsimg A hsA) I).
Qed.

Theorem inv_img_rel_univ_is_mapping {R}:
  R ⊆ UnivCl × UnivCl → (∀B, set B → set (inv_img R B)) →
  mapping (inv_img_rel UnivCl R) UnivCl UnivCl.
Proof.
  intros hR hsinv_img. unfold inv_img_rel.
  rewrite power_UnivCl.
  apply graph_is_mapping.
  intros B hB. apply comp in hB as (hsB, _).
  apply comp. exact (conj (hsinv_img B hsB) I).
Qed.

Theorem pair_eq_from_graph {f x y x' y'}:
  (x, y) ∈ f → (x, y) = (x', y') → x = x' ∧ y = y'.
Proof.
  intros hxy h.
  apply set_intro in hxy.
  apply pair_is_set_rev in hxy as (hx, hy).
  apply (pair_eq x y x' y' hx hy) in h.
  exact h.
Qed.

Theorem pair_eq_from_graph_rev {f x y x' y'}:
  (y, x) ∈ f → (x, y) = (x', y') → x = x' ∧ y = y'.
Proof.
  intros hyx h.
  apply set_intro in hyx.
  apply pair_is_set_rev in hyx as (hy, hx).
  apply (pair_eq x y x' y' hx hy) in h.
  exact h.
Qed.

Theorem app_if {X Y f x y}:
  mapping f X Y → (x, y) ∈ f → y = app f x.
Proof.
  intros hf hxy.
  assert (h := pair_in_mapping hf hxy).
  destruct h as (hx, _).
  apply (app_iff hf hx) in hxy.
  exact hxy.
Qed.

Theorem inv_from_inj {X Y f}:
  mapping f X Y → inj X f →
  mapping (inv f) (img f X) X.
Proof.
  intros hf hinj. unfold mapping.
  split; [| split].
  * unfold subclass. intros t ht.
    apply comp_elim in ht.
    destruct ht as (y, (x, (heq, hxy))).
    assert (h := pair_in_mapping hf hxy).
    destruct h as (hx, hy).
    apply prod_intro.
    exists y. exists x. split; [| split].
    - apply comp. split.
      -- exact (set_intro hy).
      -- exists x. exact (conj hx hxy).
    - exact hx.
    - exact heq.
  * unfold left_total. intros y hy.
    apply comp_elim in hy.
    destruct hy as (x, (hx, hxy)).
    exists x. apply comp. split.
    - apply (pair_in_mapping hf) in hxy as (_, hy).
      apply pair_is_set. split.
      -- exact (set_intro hy).
      -- exact (set_intro hx).
    - exists y. exists x. split.
      -- reflexivity.
      -- exact hxy.
  * unfold right_uniq. intros y x1 x2 h1 h2.
    apply comp_elim in h1.
    apply comp_elim in h2.
    destruct h1 as (y1, (x01, (h01, h1))).
    destruct h2 as (y2, (x02, (h02, h2))).
    symmetry in h01. symmetry in h02.
    apply (pair_eq_from_graph_rev h1) in h01.
    apply (pair_eq_from_graph_rev h2) in h02.
    destruct h01 as (h11, h12).
    destruct h02 as (h21, h22).
    rewrite h12 in h1. clear h12.
    rewrite h22 in h2. clear h22.
    rewrite h11 in h1. clear h11.
    rewrite h21 in h2. clear h21.
    assert (hx1 := proj1 (pair_in_mapping hf h1)).
    assert (hx2 := proj1 (pair_in_mapping hf h2)).
    apply (app_iff hf hx1) in h1.
    apply (app_iff hf hx2) in h2.
    rewrite h1 in h2.
    exact (hinj x1 x2 hx1 hx2 h2).
Qed.

Definition graph_from_cases X P f1 f2 :=
  {t | ∃x, x ∈ X ∧
   (P x ∧ t = (x, f1 x) ∨
   ¬P x ∧ t = (x, f2 x))}.

Theorem graph_cases_is_mapping X Y (P: Class → Prop) f1 f2:
  (∀x, x ∈ X → P x → f1 x ∈ Y) →
  (∀x, x ∈ X → ¬P x → f2 x ∈ Y) →
  mapping (graph_from_cases X P f1 f2) X Y.
Proof.
  intros h1 h2.
  set (f := graph_from_cases X P f1 f2).
  unfold mapping. split; [| split].
  * unfold subclass. intros t ht.
    apply prod_intro.
    apply comp_elim in ht.
    destruct ht as (x, (hx, hlr)).
    destruct hlr as [(hl, heq) | (hr, heq)].
    - exists x. exists (f1 x). split; [| split].
      -- exact hx.
      -- exact (h1 x hx hl).
      -- exact heq.
    - exists x. exists (f2 x). split; [| split].
      -- exact hx.
      -- exact (h2 x hx hr).
      -- exact heq.
  * unfold left_total. intros x hx.
    destruct (LEM (P x)) as [hl | hr].
    - exists (f1 x).
      assert (hy := h1 x hx hl).
      assert (hsy := set_intro hy).
      apply comp. split.
      -- apply pair_is_set.
         exact (conj (set_intro hx) hsy).
      -- exists x. split.
         --- exact hx.
         --- left. split.
             ---- exact hl.
             ---- reflexivity.
    - exists (f2 x).
      assert (hy := h2 x hx hr).
      assert (hsy := set_intro hy).
      apply comp. split.
      -- apply pair_is_set.
         exact (conj (set_intro hx) hsy).
      -- exists x. split.
         --- exact hx.
         --- right. split.
             ---- exact hr.
             ---- reflexivity.
  * unfold right_uniq. intros x y1 y2 hy1 hy2.
    assert (h := pair_is_set_rev x y1 (set_intro hy1)).
    destruct h as (hsx, hsy1).
    assert (h := pair_is_set_rev x y2 (set_intro hy2)).
    destruct h as (_, hsy2).
    apply comp_elim in hy1.
    destruct hy1 as (x1, (hx1, hlr1)).
    apply comp_elim in hy2.
    destruct hy2 as (x2, (hx2, hlr2)).
    destruct hlr1 as [(hl1, heq1) | (hr1, heq1)].
    - destruct hlr2 as [(hl2, heq2) | (hr2, heq2)].
      -- apply (pair_eq _ _ _ _ hsx hsy1) in heq1 as (h11, h12).
         apply (pair_eq _ _ _ _ hsx hsy2) in heq2 as (h21, h22).
         rewrite h12. clear h12.
         rewrite h22. clear h22.
         rewrite <- h11. rewrite <- h21.
         reflexivity.
      -- exfalso.
         apply (pair_eq _ _ _ _ hsx hsy1) in heq1 as (h11, _).
         apply (pair_eq _ _ _ _ hsx hsy2) in heq2 as (h21, _).
         rewrite <- h11 in hl1. rewrite <- h21 in hr2.
         exact (hr2 hl1).
    - destruct hlr2 as [(hl2, heq2) | (hr2, heq2)].
      -- exfalso.
         apply (pair_eq _ _ _ _ hsx hsy1) in heq1 as (h11, _).
         apply (pair_eq _ _ _ _ hsx hsy2) in heq2 as (h21, _).
         rewrite <- h11 in hr1. rewrite <- h21 in hl2.
         exact (hr1 hl2).
      -- apply (pair_eq _ _ _ _ hsx hsy1) in heq1 as (h11, h12).
         apply (pair_eq _ _ _ _ hsx hsy2) in heq2 as (h21, h22).
         rewrite h12. clear h12.
         rewrite h22. clear h22.
         rewrite <- h11. rewrite <- h21.
         reflexivity.
Qed.

Theorem invl_from_inj {X Y f}:
  X ≠ ∅ → mapping f X Y → inj X f →
  ∃g, mapping g Y X ∧ g ∘ f = id X.
Proof.
  intros hX hf hinj.
  apply non_empty_class in hX.
  destruct hX as (x0, hx0).
  pose (g := graph_from_cases Y
  (fun y => y ∈ img f X)
    (fun y => app (inv f) y)
    (fun y => x0)).
  assert (hg: mapping g Y X). {
    apply graph_cases_is_mapping.
    * intros y hy h.
      assert (hi := inv_from_inj hf hinj).
      exact (app_value_in_cod hi h).
    * intros _ _ _. exact hx0.
  }
  exists g. split.
  * exact hg.
  * assert (hgf := composition_is_mapping hf hg).
    assert (hid := id_is_mapping X).
    apply (mapping_ext hgf hid).
    intros x hx.
    rewrite (composition_eq hf hg hx).
    rewrite (id_app hx). clear hid hgf.
    symmetry.
    assert (hy := app_value_in_cod hf hx).
    set (y := app f x). fold y in hy.
    assert (hy_img: y ∈ img f X). {
      apply comp. split.
      * exact (set_intro hy).
      * exists x. split.
        - exact hx.
        - apply (app_iff hf hx). reflexivity.
    }
    assert (heq: x = app (inv f) y). {
      assert (hi := inv_from_inj hf hinj).
      apply (app_iff hi hy_img).
      apply comp. split.
      * apply pair_is_set. split.
        - exact (set_intro hy).
        - exact (set_intro hx).
      * exists y. exists x. split.
        - reflexivity.
        - apply (app_iff hf hx). reflexivity.
    }
    apply (app_iff hg hy).
    apply comp. split.
    - apply pair_is_set.
      exact (conj (set_intro hy) (set_intro hx)).
    - exists y. split.
      -- exact hy.
      -- left. split.
         --- exact hy_img.
         --- rewrite <- heq. reflexivity.
Qed.
