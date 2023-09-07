
Require Import Coq.Unicode.Utf8.
Require Import axioms.
Require Import basic.
Require Import mappings.
Require Import order_sc.

Theorem intersection_is_lower_bound {A M}:
  A ∈ M → ⋂M ⊆ A.
Proof.
  intro h. unfold subclass. intro x. intro hx.
  apply comp_elim in hx. exact (hx A h).
Qed.

Theorem nat_is_set:
  set ℕ.
Proof.
  destruct infinity as (A, hA).
  assert (h := hA). apply comp in h.
  destruct h as (hsA, _).
  apply intersection_is_lower_bound in hA.
  fold ℕ in hA.  exact (subset ℕ A hsA hA).
Qed.

Theorem succ_is_set n:
  set n → set (succ n).
Proof.
  intro h. unfold succ. apply union2_is_set.
  * exact h.
  * apply sg_is_set. exact h.
Qed.

Theorem zero_in_nat:
  ∅ ∈ ℕ.
Proof.
  unfold ℕ. apply comp. split.
  * exact empty_set_is_set.
  * intro A. intro hA. apply comp in hA.
    destruct hA as (_, (hA, _)).
    exact hA.
Qed.

Theorem succ_in_nat {n}:
  n ∈ ℕ → succ n ∈ ℕ.
Proof.
  intro hn. apply comp. split.
  * apply succ_is_set. exact (set_intro hn).
  * apply comp_elim in hn.
    intros A hA. assert (hn := hn A hA).
    apply comp_elim in hA. apply proj2 in hA.
    exact (hA n hn).
Qed.

Theorem induction_sets A:
  A ⊆ ℕ → (∅ ∈ A ∧ ∀n, n ∈ A → succ n ∈ A) → ℕ = A.
Proof.
  intros h hind. apply subclass_antisym. split.
  * unfold ℕ.
    apply intersection_is_lower_bound.
    apply (subset A ℕ nat_is_set) in h.
    apply comp.
    exact (conj h hind).
  * exact h.
Qed.

Theorem induction_sets_brief A:
  A ∈ InductiveSets → ℕ ⊆ A.
Proof.
  intro h. unfold ℕ.
  apply intersection_is_lower_bound.
  exact h.
Qed.

Theorem nat_is_inductive:
  ℕ ∈ InductiveSets.
Proof.
  apply comp. repeat split.
  * exact nat_is_set.
  * apply comp. split.
    - exact empty_set_is_set.
    - intro A. intro hA. apply comp in hA.
      destruct hA as (_, (hA, _)). exact hA.
  * intro n. intro hn. apply comp in hn.
    destruct hn as (hsn, hn). apply comp. split.
    - exact (succ_is_set n hsn).
    - intro A. intro hA. assert (h := hA).
      apply comp in h. destruct h as (_, (_, h)).
      apply (hn A) in hA. apply (h n) in hA.
      exact hA.
Qed.

Theorem induction (A: Class → Prop):
  A ∅ ∧ (∀n, n ∈ ℕ → A n → A (succ n)) →
  (∀n, n ∈ ℕ → A n).
Proof.
  pose (M := {n | n ∈ ℕ ∧ A n}).
  assert (hM := induction_sets M).
  assert (hsub: M ⊆ ℕ). {
    unfold subclass. intro n. intro hn.
    apply comp in hn. destruct hn as (_, (hn, _)).
    exact hn.
  }
  assert (hM := hM hsub). clear hsub.
  intro h.
  assert (h': ∅ ∈ M ∧ (∀ n : Class, n ∈ M → succ n ∈ M)). {
    destruct h as (h0, hind). split.
    * apply comp. repeat split.
      - exact empty_set_is_set.
      - exact zero_in_nat.
      - exact h0.
    * intro n. intro hn. apply comp.
      apply comp in hn.
      destruct hn as (hsn, (hn, hA)).
      repeat split.
      - exact (succ_is_set n hsn).
      - assert (h := nat_is_inductive).
        apply comp in h. destruct h as (_, (_, h)).
        exact (h n hn).
      - exact (hind n hn hA).
  }
  assert (hM := hM h'). clear h h'.
  intro n. intro hn. rewrite hM in hn.
  apply comp in hn. destruct hn as (_, (_, hn)).
  exact hn.
Qed.

Local Lemma empty_union2 {A B}:
  A ∪ B = ∅ → A = ∅.
Proof.
  intro heq. apply ext. intro x. split.
  * intro hx.
    assert (h: x ∈ A ∪ B). {
      apply union2_intro. left. exact hx.
    }
    rewrite heq in h. exact h.
  * intro hx. exfalso. exact (empty_set_property hx).
Qed.

Theorem zero_is_not_a_successor:
  ∀n, n ∈ ℕ → succ n ≠ ∅.
Proof.
  apply induction. split.
  * intro h. unfold succ in h.
    rewrite union2_com in h.
    rewrite union2_neutral in h.
    assert (hcontra: ∅ ∈ (SgSet ∅)). {
      apply comp. split.
      * exact empty_set_is_set.
      * intros _. reflexivity.
    }
    rewrite h in hcontra.
    exact (empty_set_property hcontra).
  * intros n _ ih. intro h.
    unfold succ in h at 1.
    apply empty_union2 in h.
    exact (ih h).
Qed.

Theorem empty_set_is_not_a_successor:
  ∀n, succ n ≠ ∅.
Proof.
  intros n h. unfold succ in h.
  assert (h0 := empty_union2 h).
  rewrite h0 in h. clear h0.
  rewrite union2_com in h.
  rewrite union2_neutral in h.
  symmetry in h.
  pose (u := ∅).
  assert (hcontra: u ∈ ∅). {
    rewrite h. apply comp. split.
    * exact empty_set_is_set.
    * intros _. reflexivity.
  }
  exact (empty_set_property hcontra).
Qed.

Theorem union_succ n:
  n ∈ ℕ → ⋃(succ n) = n.
Proof.
  revert n. apply induction. split.
  * unfold succ. rewrite union2_com.
    rewrite union2_neutral.
    rewrite <- (union_sg _ empty_set_is_set).
    reflexivity.
  * intros n hn ih. unfold succ at 1.
    rewrite union_union2.
    rewrite ih. clear ih.
    assert (hs := succ_is_set n (set_intro hn)).
    rewrite <- (union_sg _ hs).
    unfold succ at 1. rewrite union2_assoc.
    rewrite union2_idem. unfold succ.
    reflexivity.
Qed.

Theorem succ_is_inj {m n}:
  m ∈ ℕ → n ∈ ℕ → succ m = succ n → m = n.
Proof.
  intros hm hn h.
  apply (f_equal (fun u => ⋃u)) in h.
  rewrite (union_succ n hn) in h.
  rewrite (union_succ m hm) in h.
  exact h.
Qed.

Definition rec_eq2 x0 φ f :=
  app f ∅ = x0 ∧ ∀n, n ∈ ℕ →
  app f (succ n) = app φ (n, app f n).

Theorem rec_def_uniqueness {X x0 φ f1 f2}:
  mapping φ (ℕ × X) X → mapping f1 ℕ X → mapping f2 ℕ X →
  rec_eq2 x0 φ f1 → rec_eq2 x0 φ f2 → f1 = f2.
Proof.
  intros hphi hf1 hf2 hr1 hr2.
  apply (mapping_ext hf1 hf2).
  apply induction. split.
  * apply proj1 in hr1. apply proj1 in hr2.
    rewrite hr1. rewrite hr2. reflexivity.
  * intros n hn ih.
    apply proj2 in hr1. apply proj2 in hr2.
    rewrite (hr1 n hn). rewrite (hr2 n hn).
    rewrite ih. reflexivity.
Qed.

Theorem diff_sg_smaller {x A}:
  x ∈ A → ¬A ⊆ A \ SgSet x.
Proof.
  intro hx. intro h. assert (h := h x hx).
  apply difference_elim in h as (_, hn).
  assert (h: x ∈ SgSet x). {
    apply comp. split.
    * exact (set_intro hx).
    * intros _. reflexivity.
  }
  exact (hn h).
Qed.

Theorem rec_def_existence {X x0 φ}:
  set X → x0 ∈ X → mapping φ (ℕ × X) X →
  ∃f, mapping f ℕ X ∧ rec_eq2 x0 φ f.
Proof.
  intro hsX. intro hx0. intro hphi.
  pose (M := {A | A ⊆ ℕ × X ∧ (∅, x0) ∈ A ∧
    ∀n x, (n, x) ∈ A → (succ n, app φ (n, x)) ∈ A}).
  assert (hprod: ℕ × X ∈ M). {
    apply comp. repeat split.
    * exact (prod_is_set nat_is_set hsX).
    * apply subclass_refl.
    * apply prod_intro_term. split.
      - exact zero_in_nat.
      - exact hx0.
    * intros n x hnx. apply prod_elim_term in hnx.
      destruct hnx as (hn, hx).
      apply prod_intro_term. split.
      - exact (succ_in_nat hn).
      - assert (hnx := prod_intro_term (conj hn hx)).
        exact (app_value_in_cod hphi hnx).
  }
  pose (G := ⋂M).
  assert (hG: G ∈ M). {
    apply comp. repeat split.
    * assert (hsub: M ⊆ Power (ℕ × X)). {
        unfold subclass. intros A hA.
        apply comp. split.
        * exact (set_intro hA).
        * apply comp in hA as (_, (hA, _)).
          exact hA.
      }
      assert (hsM: set M). {
        assert (h := power_set _ (set_intro hprod)).
        exact (subset M _ h hsub).
      }
      apply intersection_is_set. intro hM.
      rewrite hM in hprod.
      exact (empty_set_property hprod).
    * unfold subclass. intros t ht.
      apply comp_elim in ht. exact (ht _ hprod).
    * apply comp. split.
      - apply pair_is_set. split.
        -- exact empty_set_is_set.
        -- exact (set_intro hx0).
      - intros A hA. apply comp_elim in hA.
        exact (proj1 (proj2 hA)).
    * intros n x hnx. apply comp. split.
      - apply comp in hnx as (hsnx, hnx).
        assert (h := hnx _ hprod). clear hnx.
        apply prod_elim_term in h as (hn, hx).
        apply pair_is_set. split.
        -- unfold succ. apply union2_is_set.
           --- exact (set_intro hn).
           --- apply sg_is_set. exact (set_intro hn).
        -- assert (hnx := prod_intro_term (conj hn hx)).
           assert (h := app_value_in_cod hphi hnx).
           exact (set_intro h).
      - intros A hA. assert (h := hA).
        apply comp_elim in h.
        apply proj2 in h. apply proj2 in h.
        apply h. clear h.
        apply comp_elim in hnx. apply hnx.
        exact hA.
  }
  assert (hGinf: is_inf G M). {
    apply inf_is_intersection. reflexivity.
  }
  assert (hGm: mapping G ℕ X). {
    assert (hGsub: G ⊆ ℕ × X). {
      apply comp_elim in hG as (hG, _).
      exact hG.
    }
    apply (mapping_property_rev hGsub).
    intros n hn. apply ex_uniq_equi2.
    revert n hn. apply induction. split.
    - exists x0. split.
      -- apply comp_elim in hG as (_, (hG, _)).
         exact hG.
      -- intros x1 hx1. apply DNE. intro hneq.
         pose (G0 := G \ SgSet (∅, x1)).
         assert (h0: G0 ∈ M). {
           apply comp. repeat split.
           * unfold G0.
             apply difference_is_set.
             exact (set_intro hG).
           * unfold G0. unfold subclass. intros t ht.
             apply comp_elim in ht as (ht, _).
             exact (hGsub t ht).
           * unfold G0. apply difference_intro.
             split.
             - apply comp_elim in hG as (_, (hG, _)).
               exact hG.
             - intro h. apply comp_elim in h.
               assert (h := h (set_intro hx1)).
               symmetry in h.
               apply (pair_eq_from_graph hx1) in h as (_, h).
               symmetry in h. exact (hneq h).
           * intros m x hmx.
             unfold G0 in hmx.
             apply difference_elim in hmx as (hmx, _).
             apply comp_elim in hG as (_, (_, hG)).
             apply hG in hmx. unfold G0.
             apply difference_intro. split.
             - exact hmx.
             - intro h. apply comp_elim in h.
               assert (h := h (set_intro hx1)).
               symmetry in h.
               apply (pair_eq_from_graph hx1) in h.
               destruct h as (h, _). symmetry in h.
               exact (empty_set_is_not_a_successor m h).
         }
         unfold is_inf in hGinf.
         destruct hGinf as (h, _).
         unfold lower_bound in h.
         apply h in h0. unfold G0 in h0.
         exact (diff_sg_smaller hx1 h0).
    - intros n hn (x, (hnx, heq)).
      exists (app φ (n, x)). split.
      -- apply comp_elim in hG as (_, (_, hG)).
         exact (hG n x hnx).
      -- intros y hy.
         pose (G0 := G \ SgSet (succ n, y)).
         apply DNE. intro hneq.
         assert (h0: G0 ∈ M). {
           apply comp. repeat split.
           * unfold G0. apply difference_is_set.
             exact (set_intro hG).
           * unfold G0. unfold subclass. intros t ht.
             apply comp_elim in ht as (ht, _).
             exact (hGsub t ht).
           * unfold G0. apply difference_intro.
             split.
             - apply comp_elim in hG as (_, (hG, _)).
               exact hG.
             - intro h. apply comp_elim in h.
               assert (h := h (set_intro hy)).
               symmetry in h.
               apply (pair_eq_from_graph hy) in h as (h, _).
               apply (empty_set_is_not_a_successor n).
               exact h.
           * intros m u hmu.
             unfold G0 in hmu.
             apply difference_elim in hmu as (hmu, _).
             assert (hm: m ∈ ℕ). {
               apply hGsub in hmu.
               apply prod_elim_term in hmu.
               exact (proj1 hmu).
             }
             apply comp_elim in hG as (_, (_, hG)).
             assert (hmu' := hG m u hmu).
             unfold G0.
             apply difference_intro. split.
             - exact hmu'.
             - intro h. apply comp_elim in h.
               assert (h := h (set_intro hy)).
               symmetry in h.
               apply (pair_eq_from_graph hy) in h.
               destruct h as (h, hyu).
               apply (succ_is_inj hn hm) in h.
               assert (hxu: x = u). {
                 apply heq. rewrite h.
                 exact hmu.
               }
               apply (f_equal (fun x => app φ (m, x))) in hxu.
               rewrite <- hxu in hyu. symmetry in hyu.
               rewrite h in hneq. exact (hneq hyu).
         }
         unfold is_inf in hGinf.
         destruct hGinf as (h, _).
         unfold lower_bound in h.
         apply h in h0. unfold G0 in h0.
         exact (diff_sg_smaller hy h0).
  }
  exists G. split.
  * exact hGm.
  * unfold rec_eq2. split.
    - assert (h0 := zero_in_nat).
      symmetry. apply (app_iff hGm h0).
      apply comp_elim in hG as (_, (hG, _)).
      exact hG.
    - intros n hn. symmetry.
      assert (hs := succ_in_nat hn).
      apply (app_iff hGm hs).
      apply comp_elim in hG as (_, (_, hG)).
      apply hG. apply (app_iff hGm hn).
      reflexivity.
Qed.

Theorem recursion_theorem2 X x0 φ:
  set X → x0 ∈ X → mapping φ (ℕ × X) X →
  ∃!f, mapping f ℕ X ∧ rec_eq2 x0 φ f.
Proof.
  intros hsX hx0 hphi. split.
  * exact (rec_def_existence hsX hx0 hphi).
  * intros f1 f2 ((hf1, h1), (hf2, h2)).
    exact (rec_def_uniqueness hphi hf1 hf2 h1 h2).
Qed.

Definition rec_eq x0 φ f :=
  app f ∅ = x0 ∧ ∀n, n ∈ ℕ →
  app f (succ n) = app φ (app f n).

Theorem recursion_theorem X x0 φ:
  set X → x0 ∈ X → mapping φ X X →
  ∃!f, mapping f ℕ X ∧ rec_eq x0 φ f.
Proof.
  intros hsX hx0 hphi.
  pose (ψ := graph_from (ℕ × X) (fun t => app φ (projr t))).
  assert (hpsi: mapping ψ (ℕ × X) X). {
    apply graph_is_mapping.
    intros t ht.
    apply (app_value_in_cod hphi).
    apply prod_elim in ht.
    destruct ht as (n, (x, (hn, (hx, heq)))).
    rewrite heq.
    rewrite <- (pair_proj2 n x (set_intro hn) (set_intro hx)).
    exact hx.
  }
  assert (hpsi_eq: ∀n x, n ∈ ℕ → x ∈ X →
     app ψ (n, x) = app φ x).
  {
     intros n x hn hx.
     assert (hnx := prod_intro_term (conj hn hx)).
     unfold ψ.
     rewrite (app_graph hnx hpsi).
     apply set_intro in hn.
     apply set_intro in hx.
     rewrite <- (pair_proj2 n x hn hx).
     reflexivity.
  }
  assert (h := recursion_theorem2 X x0 ψ hsX hx0 hpsi).
  destruct h as (hex, huniq).
  destruct hex as (f, (hf, hr)).
  unfold rec_eq in hr. destruct hr as (hr0, hrs).
  split.
  * exists f. split.
    - exact hf.
    - unfold rec_eq2. split.
      -- exact hr0.
      -- intros n hn. rewrite (hrs n hn).
         rewrite hpsi_eq.
         --- reflexivity.
         --- exact hn.
         --- exact (app_value_in_cod hf hn).
  * intros f1 f2 ((hf1, h1), (hf2, h2)).
    destruct h1 as (h10, h1s).
    destruct h2 as (h20, h2s).
    apply huniq. clear huniq. split; [split | split].
    - exact hf1.
    - unfold rec_eq. split.
      -- exact h10.
      -- intros n hn.
         assert (hx1 := app_value_in_cod hf1 hn).
         rewrite (hpsi_eq n _ hn hx1).
         exact (h1s n hn).
    - exact hf2.
    - unfold rec_eq. split.
      -- exact h20.
      -- intros n hn.
         assert (hx2 := app_value_in_cod hf2 hn).
         rewrite (hpsi_eq n _ hn hx2).
         exact (h2s n hn).
Qed.

Theorem iota_property_mapping {X Y P} f:
  set X → set Y → (∃!f, mapping f X Y ∧ P f) →
  f = iota (fun f => mapping f X Y ∧ P f) →
  mapping f X Y ∧ P f.
Proof.
  intros hsX hsY hP hf.
  assert (h: ∃!f, set f ∧ mapping f X Y ∧ P f). {
    destruct hP as (hex, huniq).
    split.
    * destruct hex as (f0, (hf0, h0)).
      exists f0. split; [| split].
      - apply proj_relation in hf0.
        assert (hprod := prod_is_set hsX hsY).
        exact (subset _ _ hprod hf0).
      - exact hf0.
      - exact h0.
    * intros f1 f2 ((_, h1), (_, h2)).
      exact (huniq f1 f2 (conj h1 h2)).
  }
  apply (iota_property f h) in hf.
  exact hf.
Qed.

Definition gsucc := graph_from ℕ succ.

Theorem succ_is_mapping:
  mapping gsucc ℕ ℕ.
Proof.
  apply graph_is_mapping. intros n hn.
  exact (succ_in_nat hn).
Qed.

Definition add a b :=
  let f := iota (fun f =>
    mapping f ℕ ℕ ∧ rec_eq a gsucc f)
  in app f b.

Theorem add_in_nat {a b}:
  a ∈ ℕ → b ∈ ℕ → add a b ∈ ℕ.
Proof.
  intros ha hb.
  assert (hnat := nat_is_set).
  assert (hsucc := succ_is_mapping).
  assert (h := recursion_theorem ℕ a gsucc hnat ha hsucc).
  unfold add.
  set (f := iota (fun f => mapping f ℕ ℕ ∧ rec_eq a gsucc f)).
  assert (hf := eq_refl f).
  apply (iota_property_mapping f hnat hnat h) in hf.
  apply proj1 in hf.
  exact (app_value_in_cod hf hb).
Qed.

Theorem add_zero {a}:
  a ∈ ℕ → add a ∅ = a.
Proof.
  intro ha.
  assert (hnat := nat_is_set).
  assert (hsucc := succ_is_mapping).
  assert (h := recursion_theorem ℕ a gsucc hnat ha hsucc).
  unfold add.
  set (f := iota (fun f => mapping f ℕ ℕ ∧ rec_eq a gsucc f)).
  assert (hf := eq_refl f).
  apply (iota_property_mapping f hnat hnat h) in hf.
  unfold rec_eq in hf. apply proj2 in hf.
  exact (proj1 hf).
Qed.

Theorem add_succ {a b}:
  a ∈ ℕ → b ∈ ℕ → add a (succ b) = succ (add a b).
Proof.
  intros ha hb.
  assert (hnat := nat_is_set).
  assert (hsucc := succ_is_mapping).
  assert (h := recursion_theorem ℕ a gsucc hnat ha hsucc).
  unfold add.
  set (f := iota (fun f => mapping f ℕ ℕ ∧ rec_eq a gsucc f)).
  assert (hf := eq_refl f).
  apply (iota_property_mapping f hnat hnat h) in hf.
  unfold rec_eq in hf.
  destruct hf as (hfm, (_, hf)).
  assert (hf := hf b hb). rewrite hf.
  assert (hy := app_value_in_cod hfm hb).
  unfold gsucc.
  rewrite (app_graph hy hsucc).
  reflexivity.
Qed.

Theorem add_assoc {a b c}:
  a ∈ ℕ → b ∈ ℕ → c ∈ ℕ →
  add (add a b) c = add a (add b c).
Proof.
  intros ha hb. revert c.
  apply induction. split.
  * assert (hab := add_in_nat ha hb).
    rewrite (add_zero hab).
    rewrite (add_zero hb).
    reflexivity.
  * intros c hc ih.
    assert (hab := add_in_nat ha hb).
    assert (hbc := add_in_nat hb hc).
    rewrite (add_succ hab hc).
    rewrite ih.
    rewrite (add_succ hb hc).
    rewrite (add_succ ha hbc).
    reflexivity.
Qed.

Theorem add_left_zero {a}:
  a ∈ ℕ → add ∅ a = a.
Proof.
  revert a. apply induction.
  assert (h0 := zero_in_nat).
  split.
  * exact (add_zero h0).
  * intros n hn ih.
    rewrite (add_succ h0 hn). rewrite ih.
    reflexivity.
Qed.

Lemma add_comm_succ {a}:
  a ∈ ℕ → add a (succ ∅) = add (succ ∅) a.
Proof.
  revert a. apply induction.
  assert (h0 := zero_in_nat).
  assert (h1 := succ_in_nat h0).
  split.
  * rewrite (add_succ h0 h0).
    rewrite (add_zero h0).
    rewrite (add_zero h1).
    reflexivity.
  * intros n hn ih.
    rewrite (add_succ (succ_in_nat hn) h0).
    rewrite (add_succ h1 hn).
    rewrite <- ih.
    rewrite (add_succ hn h0).
    rewrite (add_zero (succ_in_nat hn)).
    rewrite (add_zero hn). reflexivity.
Qed.

Theorem add_comm {a b}:
  a ∈ ℕ → b ∈ ℕ → add a b = add b a.
Proof.
  intros ha hb.
  revert b hb. apply induction. split.
  * rewrite (add_zero ha).
    rewrite (add_left_zero ha).
    reflexivity.
  * intros b hb ih.
    rewrite (add_succ ha hb).
    rewrite ih.
    rewrite <- (add_succ hb ha).
    assert (h0 := zero_in_nat).
    assert (h1 := succ_in_nat h0).
    assert (hadd1: succ a = add a (succ ∅)). {
      rewrite (add_succ ha h0).
      rewrite (add_zero ha). reflexivity.
    }
    rewrite hadd1.
    rewrite (add_comm_succ ha).
    rewrite <- (add_assoc hb h1 ha).
    rewrite (add_succ hb h0).
    rewrite (add_zero hb).
    reflexivity.
Qed.

Definition gadd b :=
  graph_from ℕ (fun a => add a b).

Theorem gadd_is_mapping {b}:
  b ∈ ℕ → mapping (gadd b) ℕ ℕ.
Proof.
  intro hb.
  apply graph_is_mapping. intros a ha.
  exact (add_in_nat ha hb).
Qed.

Definition mul a b :=
  let f := iota (fun f =>
    mapping f ℕ ℕ ∧ rec_eq ∅ (gadd a) f)
  in app f b.

Theorem mul_in_nat {a b}:
  a ∈ ℕ → b ∈ ℕ → mul a b ∈ ℕ.
Proof.
  intros ha hb.
  assert (hnat := nat_is_set).
  assert (hadd := gadd_is_mapping ha).
  assert (h0 := zero_in_nat).
  assert (h := recursion_theorem ℕ ∅ (gadd a) hnat h0 hadd).
  unfold mul.
  set (f := iota (fun f => mapping f ℕ ℕ ∧ rec_eq ∅ (gadd a) f)).
  assert (hf := eq_refl f).
  apply (iota_property_mapping f hnat hnat h) in hf.
  apply proj1 in hf.
  exact (app_value_in_cod hf hb).
Qed.

Theorem mul_zero {a}:
  a ∈ ℕ → mul a ∅ = ∅.
Proof.
  intros ha.
  assert (hnat := nat_is_set).
  assert (hadd := gadd_is_mapping ha).
  assert (h0 := zero_in_nat).
  assert (h := recursion_theorem ℕ ∅ (gadd a) hnat h0 hadd).
  unfold mul.
  set (f := iota (fun f => mapping f ℕ ℕ ∧ rec_eq ∅ (gadd a) f)).
  assert (hf := eq_refl f).
  apply (iota_property_mapping f hnat hnat h) in hf.
  apply proj2 in hf. unfold rec_eq in hf.
  exact (proj1 hf).
Qed.

Theorem mul_succ {a b}:
  a ∈ ℕ → b ∈ ℕ → mul a (succ b) = add (mul a b) a.
Proof.
  intros ha hb.
  assert (hnat := nat_is_set).
  assert (hadd := gadd_is_mapping ha).
  assert (h0 := zero_in_nat).
  assert (h := recursion_theorem ℕ ∅ (gadd a) hnat h0 hadd).
  unfold mul.
  set (f := iota (fun f => mapping f ℕ ℕ ∧ rec_eq ∅ (gadd a) f)).
  assert (hf := eq_refl f).
  apply (iota_property_mapping f hnat hnat h) in hf.
  unfold rec_eq in hf.
  destruct hf as (hfm, (_, hf)).
  rewrite (hf b hb).
  assert (hy := app_value_in_cod hfm hb).
  unfold gadd.
  rewrite (app_graph hy hadd).
  reflexivity.
Qed.

Theorem mul_add_distr_r {a b c}:
  a ∈ ℕ → b ∈ ℕ → c ∈ ℕ →
  mul (add a b) c = add (mul a c) (mul b c).
Proof.
  intros ha hb. revert c.
  assert (hab := add_in_nat ha hb).
  apply induction. split.
  * rewrite (mul_zero hab).
    rewrite (mul_zero ha).
    rewrite (mul_zero hb).
    rewrite (add_zero zero_in_nat).
    reflexivity.
  * intros c hc ih.
    rewrite (mul_succ hab hc).
    rewrite ih. clear ih.
    assert (hac := mul_in_nat ha hc).
    assert (hbc := mul_in_nat hb hc).
    assert (hacbc := add_in_nat hac hbc).
    rewrite <- (add_assoc hacbc ha hb).
    rewrite (add_assoc hac hbc ha).
    rewrite (add_comm hbc ha).
    rewrite <- (add_assoc hac ha hbc).
    assert (haca := add_in_nat hac ha).
    rewrite (add_assoc haca hbc hb).
    rewrite <- (mul_succ ha hc).
    rewrite <- (mul_succ hb hc).
    reflexivity.
Qed.

Theorem mul_zero_left {a}:
  a ∈ ℕ → mul ∅ a = ∅.
Proof.
  assert (h0 := zero_in_nat).
  revert a. apply induction. split.
  * apply (mul_zero h0).
  * intros a ha ih.
    rewrite (mul_succ h0 ha).
    rewrite ih. exact (add_zero h0).
Qed.

Theorem mul_one_right {a}:
  a ∈ ℕ → mul (succ ∅) a = a.
Proof.
  revert a. apply induction.
  assert (h0 := zero_in_nat).
  assert (h1 := succ_in_nat h0).
  split.
  * exact (mul_zero h1).
  * intros a ha ih.
    rewrite (mul_succ h1 ha).
    rewrite ih.
    rewrite (add_succ ha h0).
    rewrite (add_zero ha).
    reflexivity.
Qed.

Theorem mul_comm {a b}:
  a ∈ ℕ → b ∈ ℕ → mul a b = mul b a.
Proof.
  intros ha. revert b. apply induction. split.
  * rewrite (mul_zero ha).
    rewrite (mul_zero_left ha).
    reflexivity.
  * intros b hb ih.
    rewrite (mul_succ ha hb).
    rewrite ih.
    assert (h0 := zero_in_nat).
    assert (h1 := succ_in_nat h0).
    assert (h: succ b = add b (succ ∅)). {
      rewrite (add_succ hb zero_in_nat).
      rewrite (add_zero hb). reflexivity.
    }
    rewrite h.
    rewrite (mul_add_distr_r hb h1 ha).
    rewrite (mul_one_right ha).
    reflexivity.
Qed.

Theorem mul_add_distr_l {a b c}:
  a ∈ ℕ → b ∈ ℕ → c ∈ ℕ →
  mul c (add a b) = add (mul c a) (mul c b).
Proof.
  intros ha hb hc.
  assert (hab := add_in_nat ha hb).
  rewrite (mul_comm hc hab).
  rewrite (mul_comm hc ha).
  rewrite (mul_comm hc hb).
  exact (mul_add_distr_r ha hb hc).
Qed.

Theorem mul_assoc {a b c}:
  a ∈ ℕ → b ∈ ℕ → c ∈ ℕ →
  mul a (mul b c) = mul (mul a b) c.
Proof.
Admitted.

(* Natural number literal *)
Fixpoint nn (n: nat): Class :=
  match n with
  | 0 => ∅
  | S n => succ (nn n)
  end.

Theorem nn_in_nat (n: nat):
  nn n ∈ ℕ.
Proof.
  induction n as [| n ih].
  * unfold nn. exact (zero_in_nat).
  * simpl nn. exact (succ_in_nat ih).
Qed.

Theorem mul_1_l {a}:
  a ∈ ℕ → mul a (nn 1) = a.
Proof.
  intro ha. simpl nn.
  rewrite (mul_succ ha zero_in_nat).
  rewrite (mul_zero ha).
  rewrite (add_comm zero_in_nat ha).
  exact (add_zero ha).
Qed.

Definition gmul a :=
  graph_from ℕ (fun x => mul x a).

Theorem gmul_is_mapping {a}:
  a ∈ ℕ → mapping (gmul a) ℕ ℕ.
Proof.
  intro ha.
  apply graph_is_mapping. intros b hb.
  exact (mul_in_nat hb ha).
Qed.

Definition pow a n :=
  let f := iota (fun f =>
    mapping f ℕ ℕ ∧ rec_eq (nn 1) (gmul a) f)
  in app f n.

Theorem pow_in_nat {a b}:
  a ∈ ℕ → b ∈ ℕ → pow a b ∈ ℕ.
Proof.
  intros ha hb.
  assert (hnat := nat_is_set).
  assert (hmul := gmul_is_mapping ha).
  assert (h1 := nn_in_nat 1).
  assert (h := recursion_theorem ℕ (nn 1) (gmul a) hnat h1 hmul).
  unfold pow.
  set (f := iota (fun f => mapping f ℕ ℕ ∧ rec_eq (nn 1) (gmul a) f)).
  assert (hf := eq_refl f).
  apply (iota_property_mapping f hnat hnat h) in hf.
  apply proj1 in hf.
  exact (app_value_in_cod hf hb).
Qed.

Theorem pow_zero {a}:
  a ∈ ℕ → pow a ∅ = nn 1.
Proof.
  intros ha.
  assert (hnat := nat_is_set).
  assert (hmul := gmul_is_mapping ha).
  assert (h1 := nn_in_nat 1).
  assert (h := recursion_theorem ℕ (nn 1) (gmul a) hnat h1 hmul).
  unfold pow.
  set (f := iota (fun f => mapping f ℕ ℕ ∧ rec_eq (nn 1) (gmul a) f)).
  assert (hf := eq_refl f).
  apply (iota_property_mapping f hnat hnat h) in hf.
  apply proj2 in hf. unfold rec_eq in hf.
  exact (proj1 hf).
Qed.

Theorem pow_succ {a n}:
  a ∈ ℕ → n ∈ ℕ → pow a (succ n) = mul (pow a n) a.
Proof.
  intros ha hn.
  assert (hnat := nat_is_set).
  assert (hmul := gmul_is_mapping ha).
  assert (h1 := nn_in_nat 1).
  assert (h := recursion_theorem ℕ (nn 1) (gmul a) hnat h1 hmul).
  unfold pow.
  set (f := iota (fun f => mapping f ℕ ℕ ∧ rec_eq (nn 1) (gmul a) f)).
  assert (hf := eq_refl f).
  apply (iota_property_mapping f hnat hnat h) in hf.
  unfold rec_eq in hf. destruct hf as (hfm, (_, hf)).
  rewrite (hf n hn).
  assert (hy := app_value_in_cod hfm hn).
  unfold gmul.
  rewrite (app_graph hy hmul).
  reflexivity.
Qed.

Theorem pow_dist_mul {a b n}:
  a ∈ ℕ → b ∈ ℕ → n ∈ ℕ →
  pow (mul a b) n = mul (pow a n) (pow b n).
Proof.
  intros ha hb. revert n.
  assert (hab := mul_in_nat ha hb).
  apply induction. split.
  * rewrite (pow_zero hab).
    rewrite (pow_zero ha).
    rewrite (pow_zero hb).
    unfold nn at 3.
    assert (h0 := zero_in_nat).
    assert (h1 := nn_in_nat 1).
    rewrite (mul_succ h1 h0).
    rewrite (mul_zero h1).
    rewrite (add_comm h0 h1).
    rewrite (add_zero h1).
    reflexivity.
  * intros n hn ih.
    rewrite (pow_succ hab hn).
    rewrite ih.
    assert (han := pow_in_nat ha hn).
    assert (hbn := pow_in_nat hb hn).
    assert (hanbn := mul_in_nat han hbn).
    rewrite (mul_assoc hanbn ha hb).
    rewrite <- (mul_assoc han hbn ha).
    rewrite (mul_comm hbn ha).
    rewrite (mul_assoc han ha hbn).
    rewrite <- (mul_assoc (mul_in_nat han ha) hbn hb).
    rewrite <- (pow_succ ha hn).
    rewrite <- (pow_succ hb hn).
    reflexivity.
Qed.

Theorem pow_add_to_mul {a m n}:
  a ∈ ℕ → m ∈ ℕ → n ∈ ℕ →
  pow a (add m n) = mul (pow a m) (pow a n).
Proof.
  intros ha hm. revert n.
  apply induction. split.
  * rewrite (add_zero hm).
    rewrite (pow_zero ha).
    assert (ham := pow_in_nat ha hm).
    rewrite (mul_1_l ham).
    reflexivity.
  * intros n hn ih.
    rewrite (add_succ hm hn).
    assert (hmn := add_in_nat hm hn).
    rewrite (pow_succ ha hmn).
    rewrite ih. clear ih.
    assert (ham := pow_in_nat ha hm).
    assert (han := pow_in_nat ha hn).
    rewrite <- (mul_assoc ham han ha).
    rewrite <- (pow_succ ha hn).
    reflexivity.
Qed.

Theorem add_cancel_r {a b x}:
  a ∈ ℕ → b ∈ ℕ → x ∈ ℕ →
  add a x = add b x → a = b.
Proof.
  intros ha hb.
  pose (P a b x := add a x = add b x → a = b).
  fold (P a b x). revert x.
  apply induction. split.
  * unfold P. intro h.
    rewrite (add_zero ha) in h.
    rewrite (add_zero hb) in h.
    exact h.
  * intros x hx ih.
    unfold P. intros h.
    rewrite (add_succ ha hx) in h.
    rewrite (add_succ hb hx) in h.
    assert (hax := add_in_nat ha hx).
    assert (hbx := add_in_nat hb hx).
    apply (succ_is_inj hax hbx) in h.
    unfold P in ih. exact (ih h).
Qed.

Theorem add_cancel_l {a b x}:
  a ∈ ℕ → b ∈ ℕ → x ∈ ℕ →
  add x a = add x b → a = b.
Proof.
  intros ha hb hx h.
  rewrite (add_comm hx ha) in h.
  rewrite (add_comm hx hb) in h.
  exact (add_cancel_r ha hb hx h).
Qed.
