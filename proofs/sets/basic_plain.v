
Require Import Coq.Sets.Ensembles.

(* A ⊆ A *)
Theorem subseteq_reflexivity (U: Type) (A: Ensemble U):
  Included U A A.
Proof.
  unfold Included.
  intros x h.
  exact h.
Qed.

Theorem subseteq_reflexivity_term (U: Type) (A: Ensemble U):
  Included U A A.
Proof.
  exact (fun x => fun h => h).
Qed.

(* A ⊆ B ∧ B ⊆ C ⇒ A ⊆ C *)
Theorem subseteq_transitivity (U: Type) (A B C: Ensemble U):
  Included U A B /\ Included U B C -> Included U A C.
Proof.
  unfold Included.
  intro h.
  destruct h as (fab, fbc).
  intro x.
  intro ax.
  apply (fbc x).
  apply (fab x).
  exact ax.
Qed.

Theorem subseteq_transitivity_term (U: Type) (A B C: Ensemble U):
  Included U A B /\ Included U B C -> Included U A C.
Proof.
  exact (fun '(conj fab fbc) => fun x =>
    fun ax => (fbc x) ((fab x) ax)).
Qed.

(* A ⊆ B ∧ B ⊆ A ⇒ A = B *)
Theorem subseteq_antisymmetry (U: Type) (A B: Ensemble U):
  Included U A B /\ Included U B A -> Same_set U A B.
Proof.
  intro h. exact h.
Qed.

Theorem subseteq_antisymmetry_term (U: Type) (A B: Ensemble U):
  Included U A B /\ Included U B A -> Same_set U A B.
Proof.
  exact (fun h => h).
Qed.

(* A ∩ B ⊆ A *)
Theorem cap_subseteq (U: Type) (A B: Ensemble U):
  Included U (Intersection U A B) A.
Proof.
  unfold Included.
  intro x.
  intro h.
  destruct h as (x, a, b).
  exact a.
Qed.

(* A ⊆ A ∪ B *)
Theorem subseteq_cup (U: Type) (A B: Ensemble U):
  Included U A (Union U A B).
Proof.
  unfold Included.
  intro x. intro a.
  apply Union_introl.
  exact a.
Qed.

(* A ∩ B = B ∩ A*)
Theorem intersection_symmetric (U: Type) (A B: Ensemble U):
  (Intersection U A B) = (Intersection U B A).
Proof.
  apply Extensionality_Ensembles.
  unfold Same_set.
  unfold Included.
  split.
  * intro x. intro h. destruct h as (x, a, b).
    split. 
    - exact b.
    - exact a.
  * intro x. intro h. destruct h as (x, b, a).
    split.
    - exact a.
    - exact b.
Qed.

(* A ∪ B = B ∪ A *)
Theorem union_symmetric (U: Type) (A B: Ensemble U):
  (Union U A B) = (Union U B A).
Proof.
  apply Extensionality_Ensembles.
  unfold Same_set.
  unfold Included.
  split.
  * intro x. intro h.
    destruct h as [x a | x b].
    - apply Union_intror. exact a.
    - apply Union_introl. exact b.
  * intro x. intro h.
    destruct h as [x b | x a].
    - apply Union_intror. exact b.
    - apply Union_introl. exact a.  
Qed.

(* A ⊆ B ⇒ A ∪ B = B *)
Theorem included_char_cup (U: Type) (A B: Ensemble U):
  Included U A B -> Same_set U (Union U A B) B.
Proof.
  unfold Same_set.
  unfold Included.
  unfold In.
  intro h.
  split.
  * intro x. intro uab.
    destruct uab as [a ha | b hb].
    - apply (h a). exact ha.
    - exact hb.
  * intro x. intro hb.
    apply Union_intror. exact hb.
Qed.

(* x ∈ ∅ ⇔ ⊥ *)
Theorem empty_set_char (U: Type) (x: U):
  In U (Empty_set U) x <-> False.
Proof.
  split.
  - intro h. destruct h.
  - intro h. contradiction.
Qed.

(* A\A = ∅ *)
Theorem setminus_self (U: Type) (A: Ensemble U):
  Setminus U A A = Empty_set U.
Proof.
  apply Extensionality_Ensembles.
  unfold Same_set.
  unfold Included.
  split.
  * intro x. intro h. apply empty_set_char.
    destruct h as (a, na). apply (na a).
  * intro x. intro h. destruct h.
Qed.

(* A ∪ A = A *)
Theorem union_idem (U: Type) (A: Ensemble U):
  Union U A A = A.
Proof.
  apply Extensionality_Ensembles.
  unfold Same_set.
  split.
  * unfold Included.
    intro x. intro h.
    destruct h as [x a | x a].
    - exact a.
    - exact a.
  * unfold Included.
    intro x. intro h. apply Union_introl. exact h.
Qed.

(* A\∅ = A *)
Theorem setminus_empty_set (U: Type) (A: Ensemble U):
  Setminus U A (Empty_set U) = A.
Proof.
  apply Extensionality_Ensembles.
  unfold Same_set. unfold Included. unfold Setminus.
  split.
  * intro x. intro h. apply h.
  * intro x. intro h. unfold In.
    split.
    - exact h.
    - intro hx. destruct hx.
Qed.

(* ∅\A = ∅  *)
Theorem setminus_from_empty_set (U: Type) (A: Ensemble U):
  Setminus U (Empty_set U) A = (Empty_set U).
Proof.
  apply Extensionality_Ensembles.
  unfold Same_set. unfold Included. unfold Setminus.
  split.
  * intro x. intro h. apply h.
  * intro x. intro h. unfold In.
    split.
    - apply h.
    - intro nx. destruct h.
Qed.

(* A △ B := (A\B) ∪ (B\A) *)
Definition SymmDiff (U: Type) (A B: Ensemble U)
  := Union U (Setminus U A B) (Setminus U B A).

(* A △ A = ∅ *)
Theorem symm_diff_self (U: Type) (A: Ensemble U):
  SymmDiff U A A = Empty_set U.
Proof.
  unfold SymmDiff.
  replace (Setminus U A A) with (Empty_set U).
  apply union_idem.
  apply eq_sym.
  apply setminus_self.
Qed.

(* (A △ B) △ B = A*)
Theorem symm_diff_involution (U: Type) (A B: Ensemble U):
  SymmDiff U (SymmDiff U A B) B = A.
Proof.
Admitted.

(* A △ C = B △ C ⇒ A = B *)
Theorem symm_diff_cancel (U: Type) (A B C: Ensemble U):
  SymmDiff U A C = SymmDiff U B C -> A = B.
Proof.
  intro h.
  replace A with (SymmDiff U (SymmDiff U A C) C).
  * replace (SymmDiff U A C) with (SymmDiff U B C).
    apply symm_diff_involution.
  * apply symm_diff_involution.
Qed.
