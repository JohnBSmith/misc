
Require Import axioms.

Definition iota φ := ⋃{x | φ x}.
Notation "'ι' x , t" := (iota (fun x => t)) (at level 200).

Definition app f x := ι y, (x, y) ∈ f.

