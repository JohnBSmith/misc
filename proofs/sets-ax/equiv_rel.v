
Require Import Coq.Unicode.Utf8.
Require Import axioms.
Require Import relations.

Definition equiv_rel M (R: BinaryRel) :=
  refl M R ∧ sym M R ∧ trans M R.

Definition equiv_class M (R: BinaryRel) a :=
  {x | x ∈ M ∧ R x a}.

Definition quotient M (R: BinaryRel) :=
  {C | ∃x, x ∈ M ∧ C = equiv_class M R x}.

Theorem different_equiv_classes_disjoint M R a b:
  equiv_rel M R → a ∈ M → b ∈ M →
  let C := equiv_class M R in
    C a ≠ C b → C a ∩ C b = ∅.
Proof.
  intros hR ha hb. intro C.
  intro hn. apply DNE. intro h.
  apply non_empty_class in h.
  destruct h as (c, hc).
  apply intersection2_elim in hc as (hca, hcb).
  apply comp_elim in hca as (hc, hca).
  apply comp_elim in hcb as (_, hcb).
  destruct hR as (_, (hsym, htrans)).
  assert (h: C a = C b). {
    apply ext. intro x. split.
    * intro hx. apply comp_elim in hx as (hx, hxa).
      assert (hac := hsym c a hc ha hca). clear hca.
      assert (hxc := htrans x a c hx ha hc hxa hac).
      assert (hxb := htrans x c b hx hc hb hxc hcb).
      apply comp. repeat split.
      - exact (set_intro hx).
      - exact hx.
      - exact hxb.
    * intro hx. apply comp_elim in hx as (hx, hxb).
      assert (hbc := hsym c b hc hb hcb). clear hcb.
      assert (hxc := htrans x b c hx hb hc hxb hbc).
      assert (hxa := htrans x c a hx hc ha hxc hca).
      apply comp. repeat split.
      - exact (set_intro hx).
      - exact hx.
      - exact hxa.
  }
  exact (hn h).
Qed.
