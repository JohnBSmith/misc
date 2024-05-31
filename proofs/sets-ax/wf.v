
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
