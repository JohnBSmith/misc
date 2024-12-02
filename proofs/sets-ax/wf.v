
Require Import Coq.Unicode.Utf8.
Require Import axioms.
Require Import basic.
Require Import relations.
Require Import mappings.
Require Import nat.
Require Import prop_calc.
Require Import pred_calc.

Definition is_minimal R y A :=
  y ∈ A ∧ ¬∃x, x ∈ A ∧ R x y.

Definition well_founded M R :=
  ∀A, A ⊆ M → A ≠ ∅ → ∃y, is_minimal R y A.

(* Descending Chain Condition *)
Definition DCC M (R: Class → Class → Prop) :=
  ¬∃f, mapping f ℕ M ∧ ∀n, n ∈ ℕ → R (app f (succ n)) (app f n).

Definition wf_induction M (R: Class → Class → Prop) := ∀A, A ⊆ M →
  (∀x, x ∈ M → (∀y, y ∈ M → R y x → y ∈ A) → x ∈ A) → A = M.

Theorem well_founded_implies_antireflexive M R:
  well_founded M R → ∀u, u ∈ M → ¬R u u.
Proof.
  intro h. intros u hu.
  assert (hsu := set_intro hu).
  assert (hsgu: SgSet u ⊆ M). {
    unfold subclass. intros x hx.
    apply (sg_elim x u hsu) in hx.
    rewrite hx. exact hu.
  }
  assert (hu_in_sgu := sg_intro u u hsu (eq_refl u)).
  assert (hsgu_non_empty: SgSet u ≠ ∅). {
    intro hcontra.
    assert (h0 := hu_in_sgu).
    rewrite hcontra in h0.
    exact (empty_set_property h0).
  }
  unfold well_founded in h.
  assert (h := h (SgSet u) hsgu hsgu_non_empty).
  destruct h as (y, hy).
  unfold is_minimal in hy.
  destruct hy as (hy, hcontra).
  apply comp in hy.
  destruct hy as (_, hy).
  assert (hy := hy (set_intro hu)).
  intro hR.
  assert (hex: ∃x, x ∈ SgSet u ∧ R x y). {
    exists u. split.
    * exact hu_in_sgu.
    * rewrite hy. exact hR.
  }
  exact (hcontra hex).
Qed.

Theorem img_non_empty_class f X Y A:
  mapping f X Y → A ⊆ X → A ≠ ∅ → ∃y, y ∈ img f A.
Proof.
  intros hf hAX h. apply non_empty_class in h.
  destruct h as (x, hx).
  set (y := app f x). exists y.
  assert (hfx: app f x ∈ Y). {
    apply (app_value_in_cod hf).
    apply hAX. exact hx.
  }
  unfold img. apply comp. split.
  * exact (set_intro hfx).
  * exists x. split.
    - exact hx.
    - apply hAX in hx.
      apply (app_iff hf hx).
      unfold y. reflexivity.
Qed.

Theorem img_non_empty_domain {f X Y}:
  mapping f X Y → X ≠ ∅ → img f X ≠ ∅.
Proof.
  intros hf h. assert (hXX := subclass_refl X).
  assert (himg: ∃y, y ∈ img f X). {
    apply (img_non_empty_class f X Y X hf hXX h).
  }
  exact (non_empty_from_ex himg).
Qed.

Theorem well_founded_implies_DCC M R:
  well_founded M R → DCC M R.
Proof.
  intro hR. unfold DCC. intro h.
  destruct h as (f, (hmf, hf)).
  unfold well_founded in hR.
  assert (nat_non_empty: ℕ ≠ ∅). {
    apply non_empty_from_ex. exists ∅.
    exact zero_in_nat.
  }
  assert (himgf := img_non_empty_domain hmf nat_non_empty).
  assert (h0 := img_subclass_cod hmf (subclass_refl ℕ)).
  assert (h1 := hR _ h0 himgf).
  destruct h1 as (y, hy).
  unfold is_minimal in hy.
  destruct hy as (hy, hcontra).
  unfold img in hy. apply comp in hy.
  destruct hy as (hsy, (n, (hn, hny))).
  apply (app_iff hmf hn) in hny.
  assert (h2: ∃x, x ∈ img f ℕ ∧ R x y). {
    exists (app f (succ n)). split.
    * unfold img. apply comp. split.
      - assert (h3: app f (succ n) ∈ M). {
          apply (app_value_in_cod hmf (succ_in_nat hn)).
        }
        exact (set_intro h3).
      - exists (succ n). split.
        -- apply succ_in_nat. exact hn.
        -- apply (app_iff hmf (succ_in_nat hn)).
           reflexivity.
    * rewrite hny. apply (hf n hn).
  }
  exact (hcontra h2).
Qed.

Theorem well_founded_implies_wf_induction M R:
  well_founded M R → wf_induction M R.
Proof.
  intro hwf. unfold wf_induction.
  intros A hA. intro h.
  apply DNE. intro hcontra.
  pose (B := M \ A).
  assert (hB: B ⊆ M). {
    unfold B. unfold subclass. intros x hx.
    apply difference_elim in hx.
    exact (proj1 hx).
  }
  unfold well_founded in hwf.
  assert (hB0: B ≠ ∅). {
    intro h0. unfold B in h0. apply hcontra.
    apply subclass_iff_difference_is_empty in h0.
    apply subclass_antisym. split.
    * exact hA.
    * exact h0.
  }
  assert (hwf := hwf B hB hB0).
  destruct hwf as (a, ha).
  unfold is_minimal in ha.
  destruct ha as (ha, hex).
  assert (h1 := neg_ex hex).
  simpl in h1. clear hex.
  assert (h := h a (hB a ha)).
  assert (h2: ∀y, y ∈ M → R y a → y ∈ A). {
    intros b hb hab.
    assert (h1 := h1 b).
    apply DNE. intro h3.
    apply h1. split.
    * unfold B. apply difference_intro. split.
      - exact hb.
      - exact h3.
    * exact hab. 
  }
  assert (h := h h2).
  unfold B in ha. apply difference_elim in ha.
  apply proj2 in ha.
  exact (ha h).
Qed.

Theorem wf_induction_implies_well_founded M R:
  wf_induction M R → well_founded M R.
Proof.
  intro hwfi. unfold well_founded.
  intros B hBM hB.
  unfold wf_induction in hwfi.
  pose (A := M \ B).
  assert (hAM: A ⊆ M). {
    unfold A. unfold subclass. intros x hx.
    apply difference_elim in hx.
    exact (proj1 hx).
  }
  assert (hwfi := hwfi A hAM).
  assert (hA: A ≠ M). {
    unfold A. intro hcontra.
    symmetry in hcontra.
    apply subclass_from_eq in hcontra.
    apply hB. apply subclass_antisym. split.
    * unfold subclass. intros x hx. exfalso.
      assert (hcontra := hcontra x (hBM x hx)).
      apply difference_elim in hcontra.
      apply proj2 in hcontra.
      exact (hcontra hx).
    * unfold subclass. intros x hx. exfalso.
      exact (empty_set_property hx).
  }
  assert (h1 := contraposition hwfi). clear hwfi.
  assert (h1 := h1 hA).
  apply DNE. intro hcontra.
  apply h1. clear h1.
  intros a ha h2.
  assert (h3 := neg_ex hcontra).
  simpl in h3. clear hcontra.
  assert (h3 := h3 a). unfold is_minimal in h3.
  assert (h4 := neg_conj h3). clear h3.
  destruct h4 as [hl | hr].
  * unfold A. apply difference_intro. split.
    - exact ha.
    - exact hl.
  * exfalso. apply DNE in hr.
    destruct hr as (b, (hb, hba)).
    assert (h5 := h2 b (hBM b hb) hba).
    unfold A in h5. apply difference_elim in h5.
    apply proj2 in h5. exact (h5 hb).
Qed.

Theorem well_founded_set_implies_LEM:
  (∃M R, well_founded M R ∧ (∃x y, x ∈ M ∧ y ∈ M ∧ R y x)) →
  ∀Q, Q ∨ ¬Q.
Proof.
  intro h.
  destruct h as (M, (R, (hwf, h))).
  intro Q.
  destruct h as (x, (y, (hx, (hy, hyx)))).
  pose (P := {a | a ∈ M ∧ (a = x ∨ R a x ∧ Q)}).
  assert(hxP: x ∈ P). {
    unfold P. apply comp. split; [| split].
    * exact (set_intro hx).
    * exact hx.
    * left. reflexivity.
  }
  assert (h1: P ≠ ∅). {
    apply non_empty_from_ex.
    exists x. exact hxP.
  }
  assert (hPM: P ⊆ M). {
    unfold subclass. intros a ha.
    unfold P in ha. apply comp_elim in ha.
    exact (proj1 ha).
  }
  unfold well_founded in hwf.
  assert (h2 := hwf P hPM h1). clear hwf.
  destruct h2 as (m, hm).
  unfold is_minimal in hm.
  destruct hm as (hm, hnex).

  unfold P in hm. apply comp_elim in hm.
  destruct hm as (hmM, hm).
  destruct hm as [hl | hr].
  * right. intro hQ.
    assert (h3: y ∈ P). {
      unfold P. apply comp. split; [| split].
      - exact (set_intro hy).
      - exact hy.
      - right. exact (conj hyx hQ).
    }
    apply hnex. exists y.
    rewrite hl. exact (conj h3 hyx).
  * left. exact (proj2 hr).
Qed.

Definition wf_induction_schema M (R: Class → Class → Prop) :=
  ∀P: Class → Prop,
  (∀x, x ∈ M → (∀y, y ∈ M → R y x → P y) → P x) →
  ∀x, x ∈ M → P x.

Theorem wf_induction_schema_from_well_founded {M R}:
  well_founded M R → wf_induction_schema M R.
Proof.
  intro hwf. apply well_founded_implies_wf_induction in hwf.
  unfold wf_induction_schema. intro P. intro h. intros x hx.
  unfold wf_induction in hwf.
  pose (A := {x | x ∈ M ∧ P x}).
  assert (hA: A ⊆ M). {
    unfold subclass. intros u hu.
    unfold A in hu. apply comp in hu.
    apply proj2 in hu. exact (proj1 hu).
  }
  assert (hwf := hwf A hA).
  assert (h0: (∀ x : Class, x ∈ M →
    (∀ y : Class, y ∈ M → R y x → y ∈ A) → x ∈ A)). {
    intros u hu. intro h1.
    assert (h := h u hu).
    assert (h2: ∀y, y ∈ M → R y u → P y). {
      intros y hy hRyu.
      assert (h1 := h1 y hy hRyu).
      unfold A in h1. apply comp in h1.
      apply proj2 in h1. exact (proj2 h1).
    }
    apply h in h2. apply comp. split; [| split].
    * exact (set_intro hu).
    * exact hu.
    * exact h2.
  }
  clear h. assert (h1 := hwf h0). clear hwf h0.
  rewrite <- h1 in hx. apply comp in hx.
  apply proj2 in hx. exact (proj2 hx).
Qed.

Definition seg X (R: Class → Class → Prop) x :=
  {u | u ∈ X ∧ R u x}.

Definition wf_rec_eq X R φ f :=
  ∀x, x ∈ X → app f x = app φ (x, restr f (seg X R x)).

Theorem restr_eq {f X Y A}:
  mapping f X Y → A ⊆ X → ∀x, x ∈ A →
  app f x = app (restr f A) x.
Proof.
  intros hf hAX. intros x hx.
  assert (hfr := restr_is_mapping hf hAX).
  apply (app_iff hfr hx).
  unfold restr. apply comp. split; [| split].
  * apply pair_is_set. split.
    - exact (set_intro hx).
    - assert (h := app_value_in_cod hf (hAX x hx)).
      exact (set_intro h).
  * apply (app_iff hf (hAX x hx)). reflexivity.
  * exists x. exists (app f x). split.
    - exact hx.
    - reflexivity.
Qed.

Theorem wf_rec_uniqueness {X R Y φ} f1 f2:
  well_founded X R → mapping φ (X × UnivCl) Y →
  mapping f1 X Y → mapping f2 X Y →
  wf_rec_eq X R φ f1 → wf_rec_eq X R φ f2 → f1 = f2. 
Proof.
  intros hwf hphi hf1 hf2 hr1 hr2.
  apply (mapping_ext hf1 hf2).
  apply wf_induction_schema_from_well_founded in hwf.
  unfold wf_induction_schema in hwf.
  assert (hwf := hwf (fun x => app f1 x = app f2 x)).
  simpl in hwf. apply hwf. clear hwf.
  intros x hx. intro h.
  assert (heq: restr f1 (seg X R x) = restr f2 (seg X R x)). {
    assert (hseg: seg X R x ⊆ X). {
      unfold subclass. intros hu hsu.
      unfold seg in hsu. apply comp_elim in hsu.
      exact (proj1 hsu).
    }
    assert (hf1r := restr_is_mapping hf1 hseg).
    assert (hf2r := restr_is_mapping hf2 hseg).
    apply (mapping_ext hf1r hf2r).
    intros u hu. assert (h0 := hu).
    unfold seg in h0. apply comp_elim in h0.
    destruct h0 as (huX, hRux).
    assert (h := h u huX hRux).
    assert (h1 := restr_eq hf1 hseg u hu).
    assert (h2 := restr_eq hf2 hseg u hu).
    rewrite <- h1. rewrite <- h2.
    exact h.
  }
  clear h.
  unfold wf_rec_eq in hr1. assert (hr1 := hr1 x hx).
  unfold wf_rec_eq in hr2. assert (hr2 := hr2 x hx).
  rewrite hr1. rewrite hr2. rewrite heq. reflexivity.
Qed.

Theorem restr_rel_subclass_prod {f X Y A}:
  f ⊆ X × Y → A ⊆ X → restr f A ⊆ A × Y.
Proof.
  intros hf hAX. unfold subclass. intros t ht.
  apply comp_elim in ht.
  destruct ht as (ht, (x, (y, (hx, hxy)))).
  apply prod_intro.
  exists x. exists y. split; [| split].
  * exact hx.
  * rewrite hxy in ht.
    apply hf in ht. apply prod_elim_term in ht.
    exact (proj2 ht).
  * exact hxy.
Qed.

Definition mapping_on f X :=
  ∀x, x ∈ X → ∃!y, (x, y) ∈ f.

Theorem mapping_from_mapping_on {f X Y}:
  f ⊆ X × Y → mapping_on f X → mapping f X Y.
Proof.
  intros hf hmf. unfold mapping_on in hmf.
  exact (mapping_property_rev hf hmf).
Qed.

Theorem restr_eq_intersection f A:
  restr f A = f ∩ (A × UnivCl).
Proof.
  apply ext. intro t. split.
  * intro h. apply comp_elim in h.
    destruct h as (hf, h).
    apply intersection2_intro. split.
    - exact hf.
    - apply prod_intro.
      destruct h as (x, (y, (hx, ht))).
      exists x. exists y. split; [| split].
      -- exact hx.
      -- apply in_UnivCl_iff_set.
         rewrite ht in hf.
         apply set_intro in hf.
         apply pair_is_set_rev in hf.
         exact (proj2 hf).
      -- exact ht.
  * intro h. apply comp. split; [| split].
    - exact (set_intro h).
    - apply intersection2_elim in h.
      exact (proj1 h).
    - apply intersection2_elim in h.
      apply proj2 in h.
      apply prod_elim in h.
      destruct h as (x, (y, (hx, (_, ht)))).
      exists x. exists y. exact (conj hx ht).
Qed.

Theorem restr_app_iff {f A Y x y}:
  mapping (restr f A) A Y → x ∈ A →
  ((x, y) ∈ f ↔ y = app f x).
Proof.
  intros hf hx.
  assert (h := mapping_property hf hx).
  unfold app. fold (iota (fun y => (x, y) ∈ f)).
  split.
  * intro hxy. apply iota_property_rev.
    - apply ex_uniq_equi2 in h.
      apply ex_uniq_equi2.
      destruct h as (y0, ((hsy0, hxy0), hy0)).
      exists y0. split; [split |].
      -- exact hsy0.
      -- apply (restr_subclass_graph f A). exact hxy0.
      -- intros y1 (hsy1, hy1).
         assert (hy0 := hy0 y1). apply hy0. split.
         --- exact hsy1.
         --- apply comp. split; [| split].
             ---- apply pair_is_set.
                  exact (conj (set_intro hx) hsy1).
             ---- exact hy1.
             ---- exists x. exists y1. split.
                  ----- exact hx.
                  ----- reflexivity.
    - split.
      -- apply set_intro in hxy.
         apply pair_is_set_rev in hxy.
         exact (proj2 hxy).
      -- exact hxy.
  * intro hxy.
    assert (h0: ∃!y, set y ∧ (x, y) ∈ f). {
      apply ex_uniq_equi2 in h.
      apply ex_uniq_equi2.
      destruct h as (y0, ((hsy0, hxy0), hy0)).
      exists y0. split; [split |].
      - exact hsy0.
      - apply comp_elim in hxy0. exact (proj1 hxy0).
      - intros y1 (hsy1, hxy1).
        assert (hy0 := hy0 y1). apply hy0.
        split.
        -- exact hsy1.
        -- apply comp. split; [| split].
           --- apply pair_is_set.
               exact (conj (set_intro hx) hsy1).
           --- exact hxy1.
           --- exists x. exists y1. split.
               ---- exact hx.
               ---- reflexivity.
    }
    exact (iota_property y h0 hxy).
Qed.

Theorem app_restr {f A Y}:
  mapping (restr f A) A Y → ∀x, x ∈ A →
  app f x = app (restr f A) x.
Proof.
  intros hf. intros x hx.
  set (y := app f x).
  assert (h: y = app f x) by reflexivity.
  apply (restr_app_iff hf hx) in h.
  apply (app_iff hf hx).
  rewrite (restr_eq_intersection f A).
  apply intersection2_intro. split.
  * exact h.
  * apply prod_intro_term. split.
    - exact hx.
    - apply in_UnivCl_iff_set.
      apply set_intro in h.
      apply pair_is_set_rev in h.
      exact (proj2 h).
Qed.

Theorem wf_rec_existence X R Y φ:
  set X → set Y → well_founded X R → mapping φ (X × UnivCl) Y →
  ∃f, mapping f X Y ∧ wf_rec_eq X R φ f.
Proof.
  intros hsX hsY hwf hphi.
  pose (M := {A | A ⊆ X × Y ∧ ∀x, x ∈ X →
    ∀f, f ⊆ X × Y ∧ mapping_on f (seg X R x) →
    (∀u, u ∈ seg X R x → (u, app f u) ∈ A) →
    (x, app φ (x, restr f (seg X R x))) ∈ A}).
  assert (hprod: X × Y ∈ M). {
    apply comp. split; [| split].
    * exact (prod_is_set hsX hsY).
    * exact (subclass_refl _).
    * intros x hx f hf _.
      apply prod_intro_term. split.
      - exact hx.
      - apply (app_value_in_cod hphi).
        apply prod_intro_term. split.
        -- exact hx.
        -- apply comp. apply proj1 in hf.
           assert (hsXY := prod_is_set hsX hsY).
           split.
           --- apply restr_is_set_from_graph.
               apply (subset hf). exact hsXY.
           --- exact I.
  }
  pose (G := ⋂M).
  assert (hG: G ∈ M). {
    apply comp. split; [| split].
    * assert (hsub: M ⊆ Power (X × Y)). {
        unfold subclass. intros A hA.
        apply comp. split.
        * exact (set_intro hA).
        * apply comp in hA as (_, (hA, _)).
          exact hA.
      }
      assert (hsM: set M). {
        assert (h := power_set _ (set_intro hprod)).
        apply (subset hsub). exact h.
      }
      apply intersection_is_set. intro hM.
      rewrite hM in hprod.
      exact (empty_set_property hprod).
    * unfold subclass. intros t ht.
      apply comp_elim in ht. exact (ht _ hprod).
    * intros x hx f hf h.
      apply intersection_intro.
      - apply pair_is_set. split.
        -- exact (set_intro hx).
        -- apply (@set_intro _ Y).
           apply (app_value_in_cod hphi).
           apply prod_intro_term. split.
           --- exact hx.
           --- apply comp. apply proj1 in hf.
               assert (hsXY := prod_is_set hsX hsY).
               split.
               ---- apply restr_is_set_from_graph.
                    apply (subset hf). exact hsXY.
               ---- exact I.
      - intros A hA. assert (h0 := hA).
        apply comp_elim in h0.
        destruct h0 as (_, h0).
        apply (h0 x hx f hf). intros u hu.
        assert (h := h u hu).
        apply comp_elim in h.
        exact (h A hA).
  }
  assert (hGm: mapping G X Y). {
    assert (hGsub: G ⊆ X × Y). {
      apply comp_elim in hG as (hG, _).
      exact hG.
    }
    apply (mapping_property_rev hGsub).
    intros x hx. revert x hx.
    assert (hwi := wf_induction_schema_from_well_founded hwf).
    apply hwi. clear hwi. intros x hx ih.
    pose (f := G). apply comp_elim in hG. apply proj2 in hG.
    assert (hf: mapping_on f (seg X R x)). {
      unfold f. unfold mapping_on. intros u hu.
      unfold seg in hu. apply comp_elim in hu.
      destruct hu as (huX, hRux).
      exact (ih u huX hRux).
    }
    assert (hG' := hG).
    assert (hG := hG x hx f (conj hGsub hf)).
    pose (frestr := restr f (seg X R x)).
    assert (hfm: mapping frestr (seg X R x) Y). {
      apply mapping_property_rev.
      * assert (hseg: seg X R x ⊆ X). {
          unfold subclass. intros u hu.
          apply comp_elim in hu. exact (proj1 hu).
        }
        unfold subclass. intros t ht.
        assert (h0 := restr_rel_subclass_prod hGsub hseg).
        apply h0. exact ht.
      * intros u hu. apply comp_elim in hu.
        destruct hu as (huX, hRux).
        assert (h := ih u huX hRux).
        apply ex_uniq_equi2 in h.
        destruct h as (y, (huy, h)).
        apply ex_uniq_equi2. exists y.
        split.
        - unfold frestr. unfold f. apply comp.
          split; [| split].
          -- exact (set_intro huy).
          -- exact huy.
          -- exists u. exists y. split.
             --- apply comp. split; [| split].
                 ---- exact (set_intro huX).
                 ---- exact huX.
                 ---- exact hRux.
             --- reflexivity.
        - intros y0 hy0.
          assert (hy0G: (u, y0) ∈ G). {
            apply comp_elim in hy0.
            exact (proj1 hy0).
          }
          exact (h y0 hy0G).
    }
    apply ex_uniq_equi2.
    pose (y := app φ (x, frestr)).
    exists y. split.
    * apply hG. intros u hu. unfold f.
      assert (h0 := restr_subclass_graph G (seg X R x)).
      apply h0. apply (app_iff hfm hu).
      exact (app_restr hfm u hu).
    * intros y1 hy1. apply DNE. intro hcontra.
      pose (A := G \ SgSet (x, y1)).
      assert (A ∈ M). {
        apply comp. split; [| split].
        - apply difference_is_set.
          apply intersection_is_set.
          apply non_empty_from_ex.
          exists (X × Y). exact hprod.
        - unfold subclass. intros t ht.
          unfold A in ht. apply difference_elim in ht.
          apply proj1 in ht. apply hGsub. exact ht.
        - intros x0 hx0 f0 hf0.
          assert (hG' := hG' x0 hx0 f0 hf0).
          intro h.
          assert (h0: ∀ u : Class, u ∈ seg X R x0 → (u, app f0 u) ∈ G). {
            intros u hu. assert (h := h u hu).
            apply difference_elim in h.
            exact (proj1 h).
          }
          assert (h1 := hG' h0). apply difference_intro.
          split.
          -- exact h1.
          -- intro h2. apply comp_elim in h2.
             assert (h2 := h2 (set_intro hy1)).
             symmetry in h2.
             apply set_intro in hy1. apply pair_is_set_rev in hy1.
             destruct hy1 as (hsx, hsy1).
             apply (pair_eq _ _ _ _ hsx hsy1) in h2.
             destruct h2 as (hxeq, hy1eq).
             rewrite <- hxeq in hy1eq.
             assert (heq: f = f0).
             admit.
      }
  }
  exists G. split.
  * exact hGm.
  * unfold wf_rec_eq.
    intros x hx. symmetry.
    apply (app_iff hGm hx).
    apply comp_elim in hG as (_, hG).
    apply (hG x hx). admit.
    intros u hu.
    apply (app_iff hGm). admit.
    admit.
Admitted.
