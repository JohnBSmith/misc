
Load "axioms.v".

Fixpoint V (n: nat)
  := match n with
     | 0 => ∅
     | S n => 𝓟 (V n)
     end.

Theorem element_is_subset:
  ∀n: nat, ∀x, x ∈ V n -> x ⊆ V n.
Proof.
  induction n as [| n ih].
  * intro x. intro hx. unfold V in hx. exfalso.
    exact (empty_set_axiom x hx).
  * intro x. intro hx. unfold Subset. intro u.
    intro hu. simpl. apply power_set_axiom.
    simpl in hx. apply power_set_axiom in hx.
    assert (hu' := hx u hu).
    exact (ih u hu').
Qed.

Theorem element_is_subset_limit (M: set):
  (∀A, A ∈ M → ∀x, x ∈ A → x ⊆ A)
  → (∀x, x ∈ ⋃M → x ⊆ ⋃M).
Proof.
  intro h. intro x. intro hx. unfold Subset.
  intro u. intro hu. apply union_axiom.
  apply union_axiom in hx.
  destruct hx as (A, (hx, hA)).
  assert (hu' := h A hA x hx u hu).
  exists A. split.
  * exact hu'.
  * exact hA.
Qed.

