
Require Import Coq.Unicode.Utf8.
Require Import axioms.
Require Import relations.
Require Import mappings.

Definition cat_assoc Ob Hom compose := ∀A B C D f g h,
  A ∈ Ob → B ∈ Ob → C ∈ Ob → D ∈ Ob →
  f ∈ Hom A B → g ∈ Hom B C → h ∈ Hom C D →
  compose (compose h g) f = compose h (compose g f).

Definition cat_neut Ob Hom compose id :=
  ∀A B f, A ∈ Ob → B ∈ Ob → f ∈ Hom A B →
    compose f (id A) = f ∧ compose (id B) f = f.

Definition category := fun '(Ob, Hom, compose, id) =>
  cat_assoc Ob Hom compose ∧ cat_neut Ob Hom compose id.

Definition functor_cov Fob F :=
  fun '(ObC, HomC, composeC, idC)
      '(ObD, HomD, composeD, idD) =>
  (∀X, X ∈ ObC → Fob X ∈ ObD) ∧
  (∀X Y f, f ∈ HomC X Y → F f ∈ HomD (Fob X) (Fob Y)) ∧
  (∀X Y Z f g, f ∈ HomC X Y → g ∈ HomC Y Z →
    F (composeC g f) = composeD (F g) (F f)) ∧
  (∀X, X ∈ ObC → F (idC X) = idD (Fob X)).

Definition functor_contra Fob F :=
  fun '(ObC, HomC, composeC, idC)
      '(ObD, HomD, composeD, idD) =>
  (∀X, X ∈ ObC → Fob X ∈ ObD) ∧
  (∀X Y f, f ∈ HomC X Y → F f ∈ HomD (Fob Y) (Fob X)) ∧
  (∀X Y Z f g, f ∈ HomC X Y → g ∈ HomC Y Z →
    F (composeC g f) = composeD (F f) (F g)) ∧
  (∀X, X ∈ ObC → F (idC X) = idD (Fob X)).

Definition Abb A B := {f | mapping f A B}.
Definition Ens := (UnivCl, Abb, composition, id).
Definition Fimg f :=
  graph_from (Power (dom f)) (fun A => img f A).

Theorem category_of_sets:
  category Ens.
Proof.
  split.
  * unfold cat_assoc.
    intros A B C D f g h _ _ _ _.
    intros hf hg hh. symmetry.
    apply comp_elim in hf.
    apply comp_elim in hg.
    apply comp_elim in hh.
    exact (composition_assoc hf hg hh).
  * unfold cat_neut.
    intros A B f _ _. intro hf.
    apply comp_elim in hf.
    split.
    - exact (id_is_right_neutral hf).
    - exact (id_is_left_neutral hf).
Qed.

Theorem Fimg_is_mapping {X Y f}:
  mapping f X Y → mapping (Fimg f) (Power X) (Power Y).
Proof.
  intro hf. unfold Fimg.
  rewrite (dom_is_dom X Y f hf).
  apply graph_is_mapping.
  intros A hA. apply comp in hA as (hA, hAX).
  apply comp. split.
  * exact (replacement X Y f A hf hAX hA).
  * exact (img_subclass_cod hf hAX).
Qed.

Theorem power_set_functor_covariant:
  functor_cov Power Fimg Ens Ens.
Proof.
  repeat split.
  * intros X hX. apply in_UnivCl_iff_set.
    apply in_UnivCl_iff_set in hX.
    exact (power_set X hX).
  * intros X Y f hf.
    apply comp in hf as (hsf, hf).
    assert (h := Fimg_is_mapping hf).
    apply comp. split.
    - assert (hsX := graph_is_set hf hsf).
      apply power_set in hsX.
      apply (graph_is_set_from_dom h).
      exact hsX.
    - exact h.
  * intros X Y Z f g hf hg.
    apply comp_elim in hf.
    apply comp_elim in hg.
    assert (hgf := composition_is_mapping hf hg).
    assert (hFf := Fimg_is_mapping hf).
    assert (hFg := Fimg_is_mapping hg).
    assert (hFgf := Fimg_is_mapping hgf).
    assert (hFgFf := composition_is_mapping hFf hFg).
    apply (mapping_ext hFgf hFgFf). intros A hA.
    assert (hAsub := hA). apply comp_elim in hAsub.
    assert (hsA := set_intro hA).
    rewrite (composition_eq hFf hFg hA).
    unfold Fimg at 1. rewrite app_graph_from_set.
    3: { apply (replacement _ _ _ _ hgf hAsub hsA). }
    2: { rewrite (dom_is_dom _ _ _ hgf). exact hA. }
    assert (hAX := hA). apply comp_elim in hAX.
    rewrite (img_composition hf hg hAX).
    unfold Fimg at 2. rewrite app_graph_from_set.
    3: { apply (replacement _ _ _ _ hf hAX hsA). }
    2: { rewrite (dom_is_dom _ _ _ hf). exact hA. }
    unfold Fimg. rewrite app_graph_from_set.
    - reflexivity.
    - rewrite (dom_is_dom _ _ _ hg). apply comp. split.
      -- apply (replacement _ _ _ _ hf hAX hsA).
      -- exact (img_subclass_cod hf hAX).
    - apply (replacement _ _ _ _ hg).
      -- exact (img_subclass_cod hf hAX).
      -- apply (replacement _ _ _ _ hf hAX hsA).
  * intros X hX.
    assert (hid := id_is_mapping X).
    assert (hid' := id_is_mapping (Power X)).
    assert (hFid := Fimg_is_mapping hid).
    apply (mapping_ext hFid hid'). intros A hA.
    assert (hAsub := hA). apply comp_elim in hAsub.
    assert (hsA := set_intro hA).
    unfold Fimg. rewrite app_graph_from_set.
    - rewrite (id_img hAsub).
      unfold id. rewrite (app_graph_from_set _ _ _ hA hsA).
      reflexivity.
    - rewrite (dom_is_dom _ _ _ hid). exact hA.
    - apply (replacement _ _ _ _ hid hAsub hsA).
Qed.

Definition prod Ob compose Y1 Y2 Y proj1 proj2 :=
  Y1 ∈ Ob ∧ Y2 ∈ Ob ∧ Y ∈ Ob ∧
  mapping proj1 Y Y1 ∧ mapping proj2 Y Y2 ∧
  ∀X f1 f2, X ∈ Ob → mapping f1 X Y1 → mapping f2 X Y2 →
  ∃!f, mapping f X Y ∧
    f1 = compose proj1 f ∧ f2 = compose proj2 f.

Definition pr1 Y1 Y2 := graph_from (Y1 × Y2) projl.
Definition pr2 Y1 Y2 := graph_from (Y1 × Y2) projr.

Theorem prod_of_sets_is_prod Y1 Y2:
  set Y1 → set Y2 →
  prod UnivCl composition Y1 Y2
    (Y1 × Y2) (pr1 Y1 Y2) (pr2 Y1 Y2).
Proof.
  intros hsY1 hsY2.
  assert (hpr1: mapping (pr1 Y1 Y2) (Y1 × Y2) Y1). {
    unfold pr1.
    apply graph_is_mapping. intros t ht.
    apply prod_elim in ht as (y1, (y2, (hy1, (hy2, ht)))).
    rewrite ht. unfold pr1.
    assert (hsy1 := set_intro hy1).
    assert (hsy2 := set_intro hy2).
    rewrite <- (pair_proj1 y1 y2 hsy1 hsy2).
    exact hy1.
  }
  assert (hpr2: mapping (pr2 Y1 Y2) (Y1 × Y2) Y2). {
    apply graph_is_mapping. intros t ht.
    apply prod_elim in ht as (y1, (y2, (hy1, (hy2, ht)))).
    rewrite ht. unfold pr2.
    assert (hsy1 := set_intro hy1).
    assert (hsy2 := set_intro hy2).
    rewrite <- (pair_proj2 y1 y2 hsy1 hsy2).
    exact hy2.
  }
  unfold prod.
  split; [| split; [| split; [| split; [| split]]]].
  * apply comp. exact (conj hsY1 I).
  * apply comp. exact (conj hsY2 I).
  * apply comp. exact (conj (prod_is_set hsY1 hsY2) I).
  * exact hpr1.
  * exact hpr2.
  * intros X f1 f2 hX hf1 hf2.
    pose (f := fun x => (app f1 x, app f2 x)).
    pose (Gf := graph_from X f).
    assert (hf: mapping Gf X (Y1 × Y2)). {
      unfold Gf. apply graph_is_mapping.
      intros x hx. unfold f.
      apply prod_intro_term. split.
      * apply (app_value_in_cod hf1 hx).
      * apply (app_value_in_cod hf2 hx).
    }
    apply ex_uniq_equi2.
    exists Gf. split.
    - split; [| split].
      -- exact hf.
      -- assert (h := composition_is_mapping hf hpr1).
         apply (mapping_ext hf1 h). intros x hx.
         rewrite (composition_eq hf hpr1 hx).
         assert (hy := app_value_in_cod hf hx).
         unfold pr1. rewrite (app_graph hy hpr1).
         unfold Gf.  rewrite (app_graph hx hf).
         unfold f.
         assert (hy1 := app_value_in_cod hf1 hx).
         assert (hy2 := app_value_in_cod hf2 hx).
         apply set_intro in hy1. apply set_intro in hy2.
         rewrite <- (pair_proj1 _ _ hy1 hy2).
         reflexivity.
      -- assert (h := composition_is_mapping hf hpr2).
         apply (mapping_ext hf2 h). intros x hx.
         rewrite (composition_eq hf hpr2 hx).
         assert (hy := app_value_in_cod hf hx).
         unfold pr2. rewrite (app_graph hy hpr2).
         unfold Gf.  rewrite (app_graph hx hf).
         unfold f.
         assert (hy1 := app_value_in_cod hf1 hx).
         assert (hy2 := app_value_in_cod hf2 hx).
         apply set_intro in hy1. apply set_intro in hy2.
         rewrite <- (pair_proj2 _ _ hy1 hy2).
         reflexivity.
    - intros Gg (hg, (h1, h2)).
      apply (mapping_ext hf hg). intros x hx.
      unfold Gf. rewrite (app_graph hx hf).
      unfold f. rewrite h1. rewrite h2.
      rewrite (composition_eq hg hpr1 hx).
      rewrite (composition_eq hg hpr2 hx).
      set (y := app Gg x).
      assert (hy := app_value_in_cod hg hx).
      fold y in hy.
      assert (h := prod_elim hy).
      destruct h as (y1, (y2, (hy1, (hy2, heq)))).
      unfold pr1. rewrite (app_graph hy hpr1).
      unfold pr2. rewrite (app_graph hy hpr2).
      apply set_intro in hy1. apply set_intro in hy2.
      rewrite heq.
      rewrite <- (pair_proj1 _ _ hy1 hy2).
      rewrite <- (pair_proj2 _ _ hy1 hy2).
      reflexivity.
Qed.

