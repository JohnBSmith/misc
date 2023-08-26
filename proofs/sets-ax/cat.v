
Require Import Coq.Unicode.Utf8.
Require Import axioms.
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
  graph_from (Power (dom f)) (fun X => img f X).

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
    unfold Fimg at 1. rewrite app_graph.
    3: { apply (replacement _ _ _ _ hgf hAsub hsA). }
    2: { rewrite (dom_is_dom _ _ _ hgf). exact hA. }
    assert (hAX := hA). apply comp_elim in hAX.
    rewrite (img_composition hf hg hAX).
    unfold Fimg at 2. rewrite app_graph.
    3: { apply (replacement _ _ _ _ hf hAX hsA). }
    2: { rewrite (dom_is_dom _ _ _ hf). exact hA. }
    unfold Fimg. rewrite app_graph.
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
    unfold Fimg. rewrite app_graph.
    - rewrite (id_img hAsub).
      unfold id. rewrite (app_graph _ _ _ hA hsA).
      reflexivity.
    - rewrite (dom_is_dom _ _ _ hid). exact hA.
    - apply (replacement _ _ _ _ hid hAsub hsA).
Qed.
