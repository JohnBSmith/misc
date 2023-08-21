
Require Import Coq.Unicode.Utf8.
Require Import axioms.
Require Import mappings.

(* |X| = |Y| *)
Definition card_eq X Y :=
  ∃f, mapping f X Y ∧ bij X Y f.

(* |X| ≤ |Y| *)
Definition card_le X Y :=
  ∃f, mapping f X Y ∧ inj X f.

(* |X| < |Y| *)
Definition card_lt X Y :=
  (∃f, mapping f X Y ∧ inj X f) ∧
  (¬∃f, mapping f X Y ∧ bij X Y f).

Theorem sep_is_subclass (X: Class) (P: Class → Prop):
  {x | x ∈ X ∧ P x} ⊆ X.
Proof.
  unfold subclass. intro x. intro h.
  apply comp_elim in h. exact (proj1 h).
Qed.

Theorem sep_in_power (X: Class) (P: Class → Prop):
  set X → {x | x ∈ X ∧ P x} ∈ Power X.
Proof.
  intro hsX. set (A := {x | x ∈ X ∧ P x}).
  apply comp.
  assert (h := sep_is_subclass X P). fold A in h.
  split.
  * exact (subset A X hsX h).
  * exact h.
Qed.

(* Cantor's diagonal argument *)
Theorem no_surjection_to_power_set X f:
  set X → mapping f X (Power X) → ¬sur (Power X) f.
Proof.
  intro hsX. intro hf. intro h.
  pose (D := {x | x ∈ X ∧ x ∉ app f x}).
  assert (hD := sep_in_power X (fun x => x ∉ app f x) hsX).
  simpl in hD. fold D in hD.
  unfold sur in h. apply (h D) in hD.
  destruct hD as (x, hx).
  assert (hsx := proj1 (pair_in_mapping hf hx)).
  apply (app_iff hf hsx) in hx.
  assert (hcontra: x ∈ app f x ↔ x ∉ app f x). {
    split.
    * intro hl. rewrite <- hx in hl.
      apply comp_elim in hl. exact (proj2 hl).
    * intro hr. rewrite <- hx. apply comp.
      repeat split.
      - exact (set_intro hsx).
      - exact hsx.
      - exact hr.
  }
  exact (iff_contra hcontra).
Qed.

Theorem sg_is_subset {x X}:
  x ∈ X → SgSet x ⊆ X.
Proof.
  intro h. unfold subclass.
  intros u hu. apply comp_elim in hu.
  assert (heq := hu (set_intro h)).
  rewrite heq. exact h.
Qed.

(* Cantor's theorem *)
Theorem power_set_cardinality X:
  set X → card_lt X (Power X).
Proof.
  intro hsX. unfold card_lt. split.
  * pose (f := graph_from X (fun x => SgSet x)).
    exists f. split.
    - apply graph_is_mapping.
      intros x hx. apply comp. split.
      -- apply sg_is_set. exact (set_intro hx).
      -- exact (sg_is_subset hx).
    - unfold inj. intros x x' hx hx'.
      assert (hfx: app f x = SgSet x). {
        apply app_graph.
        * exact hx.
        * apply sg_is_set. exact (set_intro hx).
      }
      assert (hfx': app f x' = SgSet x'). {
        apply app_graph.
        * exact hx'.
        * apply sg_is_set. exact (set_intro hx').
      }
      rewrite hfx. rewrite hfx'.
      apply set_intro in hx.
      apply set_intro in hx'.
      intro h. exact (sg_inj hx hx' h).
  * intro h. destruct h as (f, (hfm, h)).
    unfold bij in h. apply proj2 in h.
    assert (hn := no_surjection_to_power_set X f hsX hfm).
    exact (hn h).
Qed.

