
(* Type of atomic variables *)
Inductive Var := var: nat -> Var.

(* Recursive definition of what should *)
(* be a logical formual *)
Inductive Formula :=
| Atom: Var -> Formula
| Neg: Formula -> Formula
| Conj: Formula -> Formula -> Formula
| Disj: Formula -> Formula -> Formula
| Impl: Formula -> Formula -> Formula.

(* Satisfaction relation *)
Fixpoint sat (I: Var -> Prop) (A: Formula) :=
  match A with
  | Atom v => I v
  | Neg A => ~(sat I A)
  | Conj A B => (sat I A) /\ (sat I B)
  | Disj A B => (sat I A) \/ (sat I B)
  | Impl A B => (sat I A) -> (sat I B)
  end.

Definition tautology (A: Formula) :=
  forall I, sat I A.

Inductive List :=
| Empty
| Cons: Formula -> List -> List.

Inductive Seq := seq: List -> Formula -> Seq.

Fixpoint sat_list (I: Var -> Prop) (Gamma: List) :=
  match Gamma with
  | Empty => True
  | Cons A Gamma => (sat I A) /\ (sat_list I Gamma)
  end.

(* Logical valid sequence *)
Definition valid '(seq Gamma A) :=
  forall I, sat_list I Gamma -> sat I A.

Theorem valid_empty (A: Formula):
  valid (seq Empty A) <-> tautology A.
Proof.
  split.
  * intro h. unfold tautology. intro I.
    unfold valid in h. simpl sat_list in h.
    apply (h I). trivial.
  * intro h. unfold tautology in h.
    unfold valid. intro I. intro h0. clear h0.
    exact (h I).
Qed.

Theorem axiom_schema_is_sound A:
  valid (seq (Cons A Empty) A).
Proof.
  unfold valid. intro I. intro h.
  simpl sat_list in h. exact (proj1 h).
Qed.

Theorem weakening_is_sound Gamma A B:
  valid (seq Gamma B) -> valid (seq (Cons A Gamma) B).
Proof.
  intro h. unfold valid. intro I. intro hI.
  simpl sat_list in hI. unfold valid in h.
  exact (h I (proj2 hI)).
Qed.

Theorem conj_intro_is_sound Gamma A B:
  valid (seq Gamma A) -> valid (seq Gamma B)
  -> valid (seq Gamma (Conj A B)).
Proof.
  intros hA hB. unfold valid.
  intro I. intro hI. simpl sat.
  unfold valid in hA.
  unfold valid in hB.
  assert (hIA := hA I hI). clear hA.
  assert (hIB := hB I hI). clear hB.
  exact (conj hIA hIB).
Qed.

Theorem conj_elim_is_sound Gamma A B:
  valid (seq Gamma (Conj A B)) -> valid (seq Gamma A).
Proof.
  intro h. unfold valid. intro I. intro hI.
  unfold valid in h. apply (h I) in hI. clear h.
  simpl sat in hI. exact (proj1 hI).
Qed.

Inductive Proof: Seq -> Type :=
| AxiomSchema: forall A, Proof (seq (Cons A Empty) A)
| ConjIntro: forall Gamma A B,
    Proof (seq Gamma A) -> Proof (seq Gamma B)
    -> Proof (seq Gamma (Conj A B)).

Theorem soundness_of_natural_deduction:
  forall S, Proof S -> valid S.
Proof.
  intro S. intro pi.
  induction pi as [A | Gamma A B piA hpiA piB hpiB].
  * exact (axiom_schema_is_sound A).
  * exact (conj_intro_is_sound Gamma A B hpiA hpiB).
Qed.

