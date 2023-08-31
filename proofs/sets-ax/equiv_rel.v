
Require Import Coq.Unicode.Utf8.
Require Import axioms.
Require Import relations.

Definition equiv_rel M (R: BinaryRel) :=
  refl M R ∧ sym M R ∧ trans M R.

Definition equiv_class M (R: BinaryRel) a :=
  {x | x ∈ M ∧ R x a}.

Definition quotient M (R: BinaryRel) :=
  {C | ∃x, x ∈ M ∧ C = equiv_class M R x}.

Theorem equiv_impl_class_eq {M R a b}:
  equiv_rel M R → a ∈ M → b ∈ M →
  let C := equiv_class M R in
    R a b → C a = C b.
Proof.
  intros hR ha hb. intro C. intro hab.
  apply ext. intro x. split.
  * intro h. apply comp_elim in h as (hx, hxa).
    apply comp. repeat split.
    - exact (set_intro hx).
    - exact hx.
    - destruct hR as (_, (_, htrans)).
      unfold trans in htrans.
      exact (htrans x a b hx ha hb hxa hab).
  * intro h. apply comp_elim in h as (hx, hxb).
    apply comp. repeat split.
    - exact (set_intro hx).
    - exact hx.
    - destruct hR as (_, (hsym, htrans)).
      unfold sym in hsym.
      assert (hba := hsym a b ha hb hab).
      clear hsym hab.
      unfold trans in htrans.
      exact (htrans x b a hx hb ha hxb hba).
Qed.

Theorem class_eq_impl_equiv {M R a b}:
  equiv_rel M R → a ∈ M → b ∈ M →
  let C := equiv_class M R in
    C a = C b → R a b.
Proof.
  intros hR ha hb. intro C. intro hab.
  assert (h: a ∈ C a). {
    apply comp. repeat split.
    - exact (set_intro ha).
    - exact ha.
    - destruct hR as (hrefl, _).
      unfold refl in hrefl.
      exact (hrefl a ha).
  }
  rewrite hab in h.
  apply comp_elim in h.
  exact (proj2 h).
Qed.

Theorem equiv_is_class_eq {M R a b}:
  equiv_rel M R → a ∈ M → b ∈ M →
  let C := equiv_class M R in
    R a b ↔ C a = C b.
Proof.
  intros hR ha hb C. split.
  * exact (equiv_impl_class_eq hR ha hb).
  * exact (class_eq_impl_equiv hR ha hb).
Qed.

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
