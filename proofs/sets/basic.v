
Require Import Coq.Unicode.Utf8.
Require Import Coq.Sets.Ensembles.

Notation "x ∈ A" := (In _ A x) (at level 70).
Notation "A ⊆ B" := (Included _ A B) (at level 70).
Notation "A ∪ B" := (Union _ A B) (at level 50).
Notation "A ∩ B" := (Intersection _ A B) (at level 40).
Notation "A \ B" := (Setminus _ A B) (at level 50).
Notation "∅" := (Empty_set _) (at level 0).
Notation "⊥" := False (at level 0).

Theorem subseteq_reflexivity (U: Type) (A: Ensemble U):
  A ⊆ A.
Proof.
  unfold Included.
  intros x h.
  exact h.
Qed.

Theorem subseteq_reflexivity_term (U: Type) (A: Ensemble U):
  A ⊆ A.
Proof.
  exact (fun x => fun h => h).
Qed.

Theorem subseteq_transitivity (U: Type) (A B C: Ensemble U):
  A ⊆ B ∧ B ⊆ C → A ⊆ C.
Proof.
  unfold Included.
  intro h. destruct h as (hAB, hBC).
  intro x. intro hx.
  apply (hBC x). apply (hAB x).
  exact hx.
Qed.

Theorem subseteq_transitivity_term (U: Type) (A B C: Ensemble U):
  A ⊆ B ∧ B ⊆ C → A ⊆ C.
Proof.
  exact (fun '(conj hAB hBC) => fun x =>
    fun hx => (hBC x) ((hAB x) hx)).
Qed.

Theorem subseteq_antisymmetry (U: Type) (A B: Ensemble U):
  A ⊆ B ∧ B ⊆ A → A = B.
Proof.
  intro h. apply Extensionality_Ensembles.
  unfold Same_set. exact h.
Qed.

Theorem subseteq_antisymmetry_term (U: Type) (A B: Ensemble U):
  A ⊆ B ∧ B ⊆ A → A = B.
Proof.
  exact (fun h => Extensionality_Ensembles U A B h).
Qed.

Theorem cap_subseteq (U: Type) (A B: Ensemble U):
  A ∩ B ⊆ A.
Proof.
  unfold Included. intro x. intro h.
  destruct h as (x, hA, hB).
  exact hA.
Qed.

Theorem subseteq_cup (U: Type) (A B: Ensemble U):
  A ⊆ A ∪ B.
Proof.
  unfold Included. intro x. intro hA.
  apply Union_introl. exact hA.
Qed.

Theorem intersection_symmetric (U: Type) (A B: Ensemble U):
  A ∩ B = B ∩ A.
Proof.
  apply Extensionality_Ensembles.
  unfold Same_set. unfold Included.
  split.
  * intro x. intro h. destruct h as (x, hA, hB).
    apply Intersection_intro.
    - exact hB.
    - exact hA.
  * intro x. intro h. destruct h as (x, hB, hA).
    apply Intersection_intro.
    - exact hA.
    - exact hB.
Qed.

Theorem union_symmetric (U: Type) (A B: Ensemble U):
  A ∪ B = B ∪ A.
Proof.
  apply Extensionality_Ensembles.
  unfold Same_set. unfold Included.
  split.
  * intro x. intro h.
    destruct h as [x hA | x hB].
    - apply Union_intror. exact hA.
    - apply Union_introl. exact hB.
  * intro x. intro h.
    destruct h as [x hB | x hA].
    - apply Union_intror. exact hB.
    - apply Union_introl. exact hA.  
Qed.

Theorem included_char_cup (U: Type) (A B: Ensemble U):
  A ⊆ B → A ∪ B = B.
Proof.
  intro h. apply Extensionality_Ensembles.
  unfold Same_set. unfold Included.
  split.
  * intro x. intro hAB.
    destruct hAB as [x hA | x hB].
    - apply (h x). exact hA.
    - exact hB.
  * intro x. intro hB.
    apply Union_intror. exact hB.
Qed.

Theorem empty_set_char (U: Type) (x: U):
  x ∈ ∅ ↔ ⊥.
Proof.
  split.
  * intro h. destruct h.
  * intro h. contradiction.
Qed.

Theorem setminus_self (U: Type) (A: Ensemble U):
  A\A = ∅.
Proof.
  apply Extensionality_Ensembles.
  unfold Same_set. unfold Included.
  split.
  * intro x. intro h. apply empty_set_char.
    destruct h as (hA, hnA). apply (hnA hA).
  * intro x. intro h. destruct h.
Qed.

Theorem union_idem (U: Type) (A: Ensemble U):
  A ∪ A = A.
Proof.
  apply Extensionality_Ensembles.
  unfold Same_set.
  split.
  * unfold Included.
    intro x. intro h.
    destruct h as [x hA | x hA].
    - exact hA.
    - exact hA.
  * unfold Included.
    intro x. intro h. apply Union_introl. exact h.
Qed.

Theorem setminus_empty_set (U: Type) (A: Ensemble U):
  A\∅ = A.
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

Theorem setminus_from_empty_set (U: Type) (A: Ensemble U):
  ∅\A = ∅.
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
Notation "A △ B" := (SymmDiff _ A B) (at level 50).

Theorem symm_diff_self (U: Type) (A: Ensemble U):
  A △ A = ∅.
Proof.
  unfold SymmDiff.
  replace (A \ A) with (Empty_set U).
  apply union_idem.
  apply eq_sym.
  apply setminus_self.
Qed.

Theorem symm_diff_involution (U: Type) (A B: Ensemble U):
  (A △ B) △ B = A.
Proof.
Admitted.

Theorem symm_diff_cancel (U: Type) (A B C: Ensemble U):
  A △ C = B △ C → A = B.
Proof.
  intro h.
  replace A with (SymmDiff U (SymmDiff U A C) C).
  * replace (SymmDiff U A C) with (SymmDiff U B C).
    apply symm_diff_involution.
  * apply symm_diff_involution.
Qed.
