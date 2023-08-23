
Require Import Coq.Unicode.Utf8.
Require Import axioms.
Require Import mappings.

Record category Ob Mor compose id := {
  cat_assoc: ∀A B C D f g h,
    A ∈ Ob → B ∈ Ob → C ∈ Ob → D ∈ Ob →
    f ∈ Mor A B → g ∈ Mor B C → h ∈ Mor C D →
    compose (compose h g) f = compose h (compose g f);
  cat_neut: ∀A B f, A ∈ Ob → B ∈ Ob → f ∈ Mor A B →
    compose f (id A) = f ∧ compose (id B) f = f
}.

Definition Abb A B := {f | mapping f A B}.
Definition id_sets A := {t | ∃x, x ∈ A ∧ t = (x, x)}.

Theorem category_of_sets:
  category UnivCl Abb composition id_sets.
Proof.
  split.
  * intros A B C D f g h _ _ _ _.
    intros hf hg hh. admit.
  * intros A B f _ _. intro hf. split.
    - admit.
    - admit.
Admitted.

