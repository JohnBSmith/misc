
Require Import Coq.Unicode.Utf8.
Require Import axioms.
Require Import basic.
Require Import mappings.

Definition InductiveSets U B F1 F2 :=
  {A | A ⊆ U ∧ B ⊆ A ∧
    (∀f, f ∈ F1 → ∀x, x ∈ A → app f x ∈ A) ∧
    (∀f, f ∈ F2 → ∀x, x ∈ A × A → app f x ∈ A)}.

Definition Abb X Y := {f | mapping f X Y}.

Theorem universe_is_inductive {U B F1 F2}:
  set U → B ⊆ U → F1 ⊆ Abb U U → F2 ⊆ Abb (U × U) U →
  U ∈ InductiveSets U B F1 F2.
Proof.
  intros hsU hBU hF1 hF2. apply comp.
  split; [| split; [| split; [| split]]].
  * exact hsU.
  * exact (subclass_refl U).
  * exact hBU.
  * intros f hf. intros x hx.
    apply hF1 in hf. apply comp_elim in hf.
    exact (app_value_in_cod hf hx).
  * intros f hf. intros x hx.
    apply hF2 in hf. apply comp_elim in hf.
    exact (app_value_in_cod hf hx).
Qed.

Theorem intersection_inductive_sets {U B F1 F2}:
  set U → B ⊆ U → F1 ⊆ Abb U U → F2 ⊆ Abb (U × U) U →
  let M := InductiveSets U B F1 F2 in ⋂M ∈ M.
Proof.
  intros hsU hBU hF1 hF2. intro M.
  assert (hM: ⋂M ⊆ U). {
    unfold subclass. intros x hx.
    apply comp_elim in hx. apply hx.
    exact (universe_is_inductive hsU hBU hF1 hF2).
  }
  apply comp.
  split; [| split; [| split; [| split]]].
  * apply (subset hM). exact hsU.
  * exact hM.
  * unfold subclass. intros x hx. apply comp. split.
    - exact (set_intro hx).
    - intros A hA. apply comp_elim in hA.
      destruct hA as (_, (hA, _)).
      exact (hA x hx).
  * intros f hf. intros x hx. apply comp. split.
    - apply hF1 in hf. apply comp_elim in hf.
      apply hM in hx.
      assert (h := app_value_in_cod hf hx).
      exact (set_intro h).
    - intros A hA. apply comp_elim in hx.
      assert (h := hA). apply hx in h.
      apply comp_elim in hA.
      destruct hA as (_, (_, (hA, _))).
      exact (hA f hf x h).
  * intros f hf. intros x hx. apply comp. split.
    - apply hF2 in hf. apply comp_elim in hf.
      assert (hM2 := prod_subclass_prod hM hM).
      apply hM2 in hx.
      assert (h := app_value_in_cod hf hx).
      exact (set_intro h).
    - intros A hA. apply prod_elim in hx.
      destruct hx as (x1, (x2, (hx1, (hx2, heq)))).
      apply comp_elim in hx1.
      apply comp_elim in hx2.
      assert (h1 := hA). apply hx1 in h1.
      assert (h2 := hA). apply hx2 in h2.
      assert (h := prod_intro_term (conj h1 h2)).
      rewrite <- heq in h. clear h1 h2 hx1 hx2 heq.
      apply comp_elim in hA.
      destruct hA as (_, (_, (_, hA))).
      exact (hA f hf x h).
Qed.

Definition extend B F1 F2 A :=
  B ∪ (⋃{Y | ∃f, f ∈ F1 ∧ Y = img f A} ∪
  ⋃{Y | ∃f, f ∈ F2 ∧ Y = img f (A × A)}).

Theorem app_value_in_img {f X Y A x}:
  mapping f X Y → A ⊆ X → x ∈ A → app f x ∈ img f A.
Proof.
  intros hf hAX hx. apply comp. split.
  * apply hAX in hx.
    apply (app_value_in_cod hf) in hx.
    exact (set_intro hx).
  * exists x. split.
    - exact hx.
    - apply hAX in hx.
      apply (app_iff hf hx). reflexivity.
Qed.

Theorem inductive_set_iff_pre_fixed_point {U B F1 F2}:
  B ⊆ U → F1 ⊆ Abb U U → F2 ⊆ Abb (U × U) U →
  let F := extend B F1 F2 in
    InductiveSets U B F1 F2 = {A | A ⊆ U ∧ F A ⊆ A}.
Proof.
  intros hBU hF1 hF2. intro F. apply ext. intro A. split.
  * intro hA. apply comp. split; [| split].
    - exact (set_intro hA).
    - apply comp_elim in hA as (hA, _).
      exact hA.
    - apply comp_elim in hA.
      destruct hA as (hAU, (hBA, (h1, h2))).
      unfold subclass. intros y hy.
      unfold F in hy. unfold extend in hy.
      apply union2_elim in hy.
      destruct hy as [hl | hr].
      -- exact (hBA y hl).
      -- apply union2_elim in hr as [hl | hr].
         --- apply union_elim in hl.
             destruct hl as (Y, (hY, hy)).
             apply comp_elim in hY.
             destruct hY as (f, (hf, heq)).
             rewrite heq in hy. clear heq.
             apply comp_elim in hy.
             destruct hy as (x, (hx, hxy)).
             assert (hfm := hF1 f hf).
             apply comp_elim in hfm.
             apply (app_iff hfm (hAU x hx)) in hxy.
             rewrite hxy.
             exact (h1 f hf x hx).
         --- apply union_elim in hr.
             destruct hr as (Y, (hY, hy)).
             apply comp_elim in hY.
             destruct hY as (f, (hf, heq)).
             rewrite heq in hy. clear heq.
             apply comp_elim in hy.
             destruct hy as (x, (hx, hxy)).
             assert (hfm := hF2 f hf).
             apply comp_elim in hfm.
             assert (hAAUU := prod_subclass_prod hAU hAU).
             apply (app_iff hfm (hAAUU x hx)) in hxy.
             rewrite hxy.
             exact (h2 f hf x hx).
  * intro hA. apply comp in hA as (hsA, (hAU, hA)).
    apply comp. split; [| split; [| split; [| split]]].
    - exact hsA.
    - exact hAU.
    - unfold F in hA. unfold extend in hA.
      unfold subclass. intros x hx. apply hA.
      apply union2_intro. left. exact hx.
    - intros f hf. intros x hx.
      unfold F in hA. unfold extend in hA.
      apply hA. apply union2_intro. right.
      apply union2_intro. left. apply union_intro.
      exists (img f A). split.
      -- apply comp. split.
         --- apply hF1 in hf. apply comp_elim in hf.
             exact (replacement U U f A hf hAU hsA).
         --- exists f. split.
             ---- exact hf.
             ---- reflexivity.
      -- apply hF1 in hf. apply comp_elim in hf.
         exact (app_value_in_img hf hAU hx).
    - intros f hf. intros x hx.
      unfold F in hA. unfold extend in hA.
      apply hA. apply union2_intro. right.
      apply union2_intro. right. apply union_intro.
      exists (img f (A × A)). split.
      -- apply comp. split.
         --- apply hF2 in hf. apply comp_elim in hf.
             assert (hAAUU := prod_subclass_prod hAU hAU).
             apply (replacement _ U f _ hf hAAUU).
             exact (prod_is_set hsA hsA).
         --- exists f. split.
             ---- exact hf.
             ---- reflexivity.
      -- apply hF2 in hf. apply comp_elim in hf.
         assert (hAAUU := prod_subclass_prod hAU hAU).
         exact (app_value_in_img hf hAAUU hx).
Qed.

Theorem least_inductive_set_is_least_pre_fixed_point {U B F1 F2}:
  B ⊆ U → F1 ⊆ Abb U U → F2 ⊆ Abb (U × U) U →
  let F := extend B F1 F2 in
    ⋂(InductiveSets U B F1 F2) = ⋂{A | A ⊆ U ∧ F A ⊆ A}.
Proof.
  intros hBU hF1 hF2. intro F.
  assert (h := inductive_set_iff_pre_fixed_point hBU hF1 hF2).
  rewrite h. unfold F. reflexivity.
Qed.

Theorem img_is_monotone {f X Y A B}:
  mapping f X Y → B ⊆ X → A ⊆ B → img f A ⊆ img f B.
Proof.
  intros hf hBX hAB.
  unfold subclass. intros y hy.
  apply comp_elim in hy.
  destruct hy as (x, (hx, hxy)).
  apply comp. split.
  * apply (pair_in_mapping hf) in hxy as (_, hy).
    exact (set_intro hy).
  * exists x. split.
    - exact (hAB x hx).
    - exact hxy.
Qed.

Theorem F_is_monotone {U B F1 F2}:
  set U → F1 ⊆ Abb U U → F2 ⊆ Abb (U × U) U →
  let F := extend B F1 F2 in
    ∀ X Y, Y ⊆ U → X ⊆ Y → F X ⊆ F Y.
Proof.
  intros hsU hF1 hF2. intro F. intros X Y hYU hXY.
  unfold subclass. intros x hx.
  unfold F in hx. unfold extend in hx.
  apply union2_elim in hx.
  destruct hx as [hl | hr].
  * unfold F. unfold extend.
    apply union2_intro. left. exact hl.
  * apply union2_elim in hr.
    destruct hr as [hl | hr].
    - apply union_elim in hl.
      destruct hl as (A, (hA, hx)).
      apply comp_elim in hA.
      destruct hA as (f, (hf, heq)).
      unfold F. unfold extend.
      apply union2_intro. right.
      apply union2_intro. left.
      apply union_intro. exists (img f Y). split.
      -- apply comp. split.
         --- assert (h := subset hYU hsU).
             apply hF1 in hf. apply comp_elim in hf.
             exact (replacement U U f Y hf hYU h).
         --- exists f. split.
             ---- exact hf.
             ---- reflexivity.
      -- rewrite heq in hx. clear heq A.
         apply hF1 in hf. apply comp_elim in hf.
         assert (hsub := img_is_monotone hf hYU hXY).
         exact (hsub x hx).
    - apply union_elim in hr.
      destruct hr as (A, (hA, hx)).
      apply comp_elim in hA.
      destruct hA as (f, (hf, heq)).
      unfold F. unfold extend.
      apply union2_intro. right.
      apply union2_intro. right.
      apply union_intro. exists (img f (Y × Y)). split.
      -- apply comp. split.
         --- assert (h := subset hYU hsU).
             apply hF2 in hf. apply comp_elim in hf.
             assert (hYYUU := prod_subclass_prod hYU hYU).
             apply (replacement (U × U) U f (Y × Y) hf).
             ---- exact hYYUU.
             ---- exact (prod_is_set h h).
         --- exists f. split.
             ---- exact hf.
             ---- reflexivity.
      -- rewrite heq in hx. clear heq A.
         apply hF2 in hf. apply comp_elim in hf.
         assert (hYYUU := prod_subclass_prod hYU hYU).
         assert (hXXYY := prod_subclass_prod hXY hXY).
         assert (hsub := img_is_monotone hf hYYUU hXXYY).
         exact (hsub x hx).
Qed.

Theorem least_inductive_set_is_fixed_point {U B F1 F2}:
  set U → B ⊆ U → F1 ⊆ Abb U U → F2 ⊆ Abb (U × U) U →
  let F := extend B F1 F2 in
  let X := ⋂(InductiveSets U B F1 F2) in
    F X = X.
Proof.
  intros hsU hBU hF1 hF2. intros F X.
  assert (hsub: F X ⊆ X). {
    assert (h := intersection_inductive_sets hsU hBU hF1 hF2).
    simpl in h. fold X in h.
    assert (heq := inductive_set_iff_pre_fixed_point hBU hF1 hF2).
    rewrite heq in h. apply comp_elim in h.
    apply proj2 in h. fold F in h. exact h.
  }
  apply subclass_antisym. split.
  * exact hsub.
  * assert (hXU: X ⊆ U). {
      unfold subclass. intros x hx.
      unfold X in hx. apply comp_elim in hx. apply hx.
      exact (universe_is_inductive hsU hBU hF1 hF2).
    }
    assert (hX: F X ∈ InductiveSets U B F1 F2). {
      assert (h := inductive_set_iff_pre_fixed_point hBU hF1 hF2).
      simpl in h. rewrite h. apply comp. split; [| split].
      * assert (hX := intersection_inductive_sets hsU hBU hF1 hF2).
        simpl in hX. fold X in hX. apply set_intro in hX.
        apply (subset hsub). exact hX.
      * exact (subclass_trans (conj hsub hXU)).
      * fold F. apply (F_is_monotone hsU hF1 hF2).
        - exact hXU.
        - exact hsub.
    }
    apply intersection_is_lower_bound in hX.
    fold X in hX. exact hX.
Qed.

Definition closure U B0 F1 F2 B :=
  let F := extend (B ∪ B0) F1 F2 in
    ⋂{A | A ⊆ U ∧ F A ⊆ A}.

Theorem extensivity U B0 F1 F2:
  let cl := closure U B0 F1 F2 in
    ∀B, B ⊆ cl B.
Proof.
  intro cl. intro B.
  unfold subclass. intros x hx.
  unfold cl. unfold closure. clear cl.
  apply comp.  split.
  * exact (set_intro hx).
  * intros A hA. apply comp_elim in hA as (_, hA).
    apply hA. unfold extend.
    apply union2_intro. left. 
    apply union2_intro. left. exact hx.
Qed.

Theorem monotonicity U B0 F1 F2:
  let cl := closure U B0 F1 F2 in
    ∀B1 B2, B1 ⊆ B2 → cl B1 ⊆ cl B2.
Proof.
  intro cl. intros B1 B2. intro h.
  unfold subclass. intros x hx.
  unfold cl. unfold closure.
  apply comp. split.
  * exact (set_intro hx).
  * intros A hA. apply comp in hA as (hsA, (hAU, hA)).
    unfold cl in hx. unfold closure in hx.
    apply comp_elim in hx. apply hx.
    apply comp. split; [| split].
    - exact hsA.
    - exact hAU.
    - unfold subclass. intros u hu.
      apply hA. unfold extend in hu.
      apply union2_elim in hu.
      destruct hu as [hl | hr].
      -- unfold extend. apply union2_intro.
         left. apply union2_elim in hl.
         destruct hl as [hl | hr].
         --- apply union2_intro. left.
             apply h. exact hl.
         --- apply union2_intro. right.
             exact hr.
      -- unfold extend. apply union2_intro.
         right. exact hr.
Qed.

Local Theorem union2_subclass {A B U}:
  A ⊆ U → B ⊆ U → A ∪ B ⊆ U.
Proof.
  intros hA hB. unfold subclass. intros x hx.
  apply union2_elim in hx. destruct hx as [hl | hr].
  * apply hA. exact hl.
  * apply hB. exact hr.
Qed.

Theorem extensivity0 U B0 F1 F2:
  let cl := closure U B0 F1 F2 in
    ∀B, B0 ⊆ cl B.
Proof.
  intro cl. intro B. unfold subclass. intros x hx.
  unfold cl. unfold closure. clear cl.
  apply comp. split.
  * exact (set_intro hx).
  * intros A hA. apply comp_elim in hA as (hAU, hA).
    apply hA. unfold extend.
    apply union2_intro. left.
    apply union2_intro. right. exact hx.
Qed.

Theorem closedness {U B0 F1 F2}:
  set U → B0 ⊆ U → F1 ⊆ Abb U U → F2 ⊆ Abb (U × U) U →
  let cl := closure U B0 F1 F2 in
    ∀B, B ⊆ U → cl (cl B) ⊆ cl B.
Proof.
  intros hsU hB0 hF1 hF2. intro cl. intros B hB.
  set (F := extend (B ∪ B0) F1 F2).
  assert (h: cl B ∈ {A | A ⊆ U ∧ F A ⊆ A}). {
    unfold F. unfold cl. unfold closure.
    assert (hsub := union2_subclass hB hB0).
    rewrite <- (inductive_set_iff_pre_fixed_point hsub hF1 hF2).
    apply (intersection_inductive_sets hsU hsub hF1 hF2).
  }
  unfold cl at 1. unfold closure.
  apply intersection_is_lower_bound.
  apply comp. split; [| split].
  * exact (set_intro h).
  * apply comp_elim in h as (h, _). exact h.
  * unfold subclass. intros x hx.
    unfold extend in hx. apply union2_elim in hx.
    destruct hx as [hl | hr].
    - apply union2_elim in hl.
      destruct hl as [hl | hr].
      -- exact hl.
      -- apply extensivity0. exact hr.
    - apply comp_elim in h as (_, h).
      apply h. unfold F. unfold extend.
      apply union2_intro. right. exact hr.
Qed.

Theorem idempotence U B0 F1 F2:
  set U → B0 ⊆ U → F1 ⊆ Abb U U → F2 ⊆ Abb (U × U) U →
  let cl := closure U B0 F1 F2 in
    ∀B, B ⊆ U → cl (cl B) = cl B.
Proof.
  intros hsU hB0 hF1 hF2. intro cl. intros B hB.
  apply subclass_antisym. split.
  * exact (closedness hsU hB0 hF1 hF2 B hB).
  * apply monotonicity. apply extensivity.
Qed.
