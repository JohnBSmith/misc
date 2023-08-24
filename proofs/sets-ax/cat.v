
Require Import Coq.Unicode.Utf8.
Require Import axioms.
Require Import mappings.

Record category Ob Hom compose id := {
  cat_assoc: ∀A B C D f g h,
    A ∈ Ob → B ∈ Ob → C ∈ Ob → D ∈ Ob →
    f ∈ Hom A B → g ∈ Hom B C → h ∈ Hom C D →
    compose (compose h g) f = compose h (compose g f);
  cat_neut: ∀A B f, A ∈ Ob → B ∈ Ob → f ∈ Hom A B →
    compose f (id A) = f ∧ compose (id B) f = f
}.

Definition Abb A B := {f | mapping f A B}.

Theorem category_of_sets:
  category UnivCl Abb composition id.
Proof.
  split.
  * intros A B C D f g h _ _ _ _.
    intros hf hg hh. symmetry.
    apply comp_elim in hf.
    apply comp_elim in hg.
    apply comp_elim in hh.
    exact (composition_assoc hf hg hh).
  * intros A B f _ _. intro hf.
    apply comp_elim in hf.
    split.
    - exact (id_is_right_neutral hf).
    - exact (id_is_left_neutral hf).
Qed.

