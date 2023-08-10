
Load "axioms.v".

(* The universal class. *)
Definition UnivCl := {x | True}.

(* The diagonal class (Russell's class). *)
Definition DiagCl := {x | x ∉ x}.

Theorem iff_contra {A: Prop}:
  (A ↔ ¬A) → False.
Proof.
  intro h. destruct h as (hl, hr).
  assert (hnA: ¬A). {
    intro hA. exact ((hl hA) hA).
  }
  exact (hnA (hr hnA)).
Qed.

(* Russell's paradox. *)
Theorem DiagCl_is_proper:
  ¬set DiagCl.
Proof.
  set (R := DiagCl). intro hR.
  assert (h: R ∈ R ↔ R ∉ R). {
    split.
    * intro h. unfold R in h at 2. apply comp in h.
      exact (proj2 h).
    * intro h. unfold R at 2. apply -> comp.
      exact (conj hR h).
  }
  exact (iff_contra h).
Qed.

Theorem UnivCl_by_eq:
  UnivCl = {x | x = x}.
Proof.
  apply ext. intro x. split.
  * intro h. apply comp in h. destruct h as (h, _).
    apply -> comp. split.
    - exact h.
    - reflexivity.
  * intro h. apply comp in h. destruct h as (h, _).
    apply -> comp. split.
    - exact h.
    - exact I.
Qed.

Theorem in_UnivCl_iff_set x:
  x ∈ UnivCl ↔ set x.
Proof.
  split.
  * intro h. apply comp in h. exact (proj1 h).
  * intro h. apply -> comp. exact (conj h I).
Qed.

Theorem DiagCl_subclass_UnivCl:
  DiagCl ⊆ UnivCl.
Proof.
  unfold Subclass. intro x. intro h.
  apply comp in h. apply -> comp.
  exact (conj (proj1 h) I).
Qed.

Theorem UnivCl_is_proper:
  ¬set UnivCl.
Proof.
  assert (hR := DiagCl_subclass_UnivCl).
  intro h. apply (subset DiagCl UnivCl h) in hR.
  exact (DiagCl_is_proper hR).
Qed.

Theorem compl_empty_set:
  Compl ∅ = UnivCl.
Proof.
  apply ext. intro x. split.
  * intro h. apply comp in h. apply proj1 in h.
    apply -> comp. exact (conj h I).
  * intro h. apply comp in h. apply proj1 in h.
    apply -> comp.
    exact (conj h (empty_set_property x)).
Qed.
