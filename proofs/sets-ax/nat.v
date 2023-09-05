
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

Theorem empty_set_in_nat:
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
      - exact empty_set_in_nat.
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

Theorem succ_is_inj m n:
  m ∈ ℕ → n ∈ ℕ → succ m = succ n → m = n.
Proof.
  intros hm hn h.
  apply (f_equal (fun u => ⋃u)) in h.
  rewrite (union_succ n hn) in h.
  rewrite (union_succ m hm) in h.
  exact h.
Qed.

Definition rec_eq x0 φ f :=
  app f ∅ = x0 ∧ ∀n, n ∈ ℕ → app f (succ n) = app φ (app f n).

Theorem rec_def_uniqueness {X x0 φ f1 f2}:
  mapping φ X X → mapping f1 ℕ X → mapping f2 ℕ X →
  rec_eq x0 φ f1 → rec_eq x0 φ f2 → f1 = f2.
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
  set X → x0 ∈ X → mapping φ X X →
  ∃f, mapping f ℕ X ∧ rec_eq x0 φ f.
Proof.
  intro hsX. intro hx0. intro hphi.
  pose (M := {A | A ⊆ ℕ × X ∧ (∅, x0) ∈ A ∧
    ∀n x, (n, x) ∈ A → (succ n, app φ x) ∈ A}).
  assert (hprod: ℕ × X ∈ M). {
    apply comp. repeat split.
    * exact (prod_is_set nat_is_set hsX).
    * apply subclass_refl.
    * apply prod_intro_term. split.
      - exact empty_set_in_nat.
      - exact hx0.
    * intros n x hnx. apply prod_elim_term in hnx.
      destruct hnx as (hn, hx).
      apply prod_intro_term. split.
      - exact (succ_in_nat hn).
      - exact (app_value_in_cod hphi hx).
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
        assert (h := hnx _ hprod).
        apply prod_elim_term in h as (hn, hx).
        apply pair_is_set. split.
        -- unfold succ. apply union2_is_set.
           --- exact (set_intro hn).
           --- apply sg_is_set. exact (set_intro hn).
        -- assert (h := app_value_in_cod hphi hx).
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
      exists (app φ x). split.
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
               apply (succ_is_inj n m hn hm) in h.
               assert (hxu: x = u). {
                 apply heq. rewrite h.
                 exact hmu.
               }
               apply (f_equal (fun x => app φ x)) in hxu.
               rewrite <- hxu in hyu. symmetry in hyu.
               exact (hneq hyu).
         }
         unfold is_inf in hGinf.
         destruct hGinf as (h, _).
         unfold lower_bound in h.
         apply h in h0. unfold G0 in h0.
         exact (diff_sg_smaller hy h0).
  }
  exists G. split.
  * exact hGm.
  * unfold rec_eq. split.
    - assert (h0 := empty_set_in_nat).
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

Theorem recursion_theorem X x0 φ:
  set X → x0 ∈ X → mapping φ X X →
  ∃!f, mapping f ℕ X ∧ rec_eq x0 φ f.
Proof.
  intros hsX hx0 hphi. split.
  * exact (rec_def_existence hsX hx0 hphi).
  * intros f1 f2 ((hf1, h1), (hf2, h2)).
    exact (rec_def_uniqueness hphi hf1 hf2 h1 h2).
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
  assert (h0 := empty_set_in_nat).
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
  assert (h0 := empty_set_in_nat).
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
    assert (h0 := empty_set_in_nat).
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
  assert (h0 := empty_set_in_nat).
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
  assert (h0 := empty_set_in_nat).
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
  assert (h0 := empty_set_in_nat).
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

Theorem mul_distr_right {a b c}:
  a ∈ ℕ → b ∈ ℕ → c ∈ ℕ →
  mul (add a b) c = add (mul a c) (mul b c).
Proof.
  intros ha hb. revert c.
  assert (hab := add_in_nat ha hb).
  apply induction. split.
  * rewrite (mul_zero hab).
    rewrite (mul_zero ha).
    rewrite (mul_zero hb).
    rewrite (add_zero empty_set_in_nat).
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
  assert (h0 := empty_set_in_nat).
  revert a. apply induction. split.
  * apply (mul_zero h0).
  * intros a ha ih.
    rewrite (mul_succ h0 ha).
    rewrite ih. exact (add_zero h0).
Qed.
