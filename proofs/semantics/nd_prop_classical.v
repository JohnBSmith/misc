
(* Sequent natural deduction for propositional calculus. *)
(* Soundness under classical semantics. *)

(* Double negation elimination, *)
(* needed for classical semantics. *)
Axiom dne: forall A: Prop, ~~A -> A.

(* Type of atomic variables *)
Inductive Var := var: nat -> Var.

(* Recursive definition of what should *)
(* be a logical formula *)
Inductive Formula :=
| Atom: Var -> Formula
| FF: Formula
| TF: Formula
| Neg: Formula -> Formula
| Conj: Formula -> Formula -> Formula
| Disj: Formula -> Formula -> Formula
| Impl: Formula -> Formula -> Formula.

(* Satisfaction relation *)
Fixpoint sat (I: Var -> Prop) (A: Formula) :=
  match A with
  | Atom v => I v
  | FF => False
  | TF => True
  | Neg A => ~(sat I A)
  | Conj A B => (sat I A) /\ (sat I B)
  | Disj A B => (sat I A) \/ (sat I B)
  | Impl A B => (sat I A) -> (sat I B)
  end.

Definition tautology (A: Formula) :=
  forall I, sat I A.

Inductive List :=
| Empty
| Cons: List -> Formula -> List.

Fixpoint concat (Gamma Gamma': List) :=
  match Gamma' with
  | Empty => Gamma
  | (Cons Gamma' A) => Cons (concat Gamma Gamma') A
  end.

(* Type of sequents *)
Inductive Seq := seq: List -> Formula -> Seq.

Fixpoint sat_list (I: Var -> Prop) (Gamma: List) :=
  match Gamma with
  | Empty => True
  | Cons Gamma A => (sat I A) /\ (sat_list I Gamma)
  end.

(* Logical valid sequence *)
Definition valid '(seq Gamma A) :=
  forall I, sat_list I Gamma -> sat I A.

Theorem valid_empty_is_tautology (A: Formula):
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

Lemma axiom_schema_is_sound A:
  valid (seq (Cons Empty A) A).
Proof.
  unfold valid. intro I. intro h.
  simpl sat_list in h. exact (proj1 h).
Qed.

Lemma weakening_is_sound Gamma A B:
  valid (seq Gamma B) -> valid (seq (Cons Gamma A) B).
Proof.
  intro h. unfold valid. intro I. intro hI.
  simpl sat_list in hI. unfold valid in h.
  exact (h I (proj2 hI)).
Qed.

Lemma conj_intro_is_sound Gamma A B:
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

Lemma conj_eliml_is_sound Gamma A B:
  valid (seq Gamma (Conj A B)) -> valid (seq Gamma A).
Proof.
  intro h. unfold valid. intro I. intro hI.
  unfold valid in h. apply (h I) in hI. clear h.
  simpl sat in hI. exact (proj1 hI).
Qed.

Lemma conj_elimr_is_sound Gamma A B:
  valid (seq Gamma (Conj A B)) -> valid (seq Gamma B).
Proof.
  intro h. unfold valid. intro I. intro hI.
  unfold valid in h. apply (h I) in hI. clear h.
  simpl sat in hI. exact (proj2 hI).
Qed.

Lemma disj_introl_is_sound Gamma A B:
  valid (seq Gamma A) -> valid (seq Gamma (Disj A B)).
Proof.
  intro h. unfold valid. intro I. intro hI.
  unfold valid in h. apply (h I) in hI. clear h.
  simpl sat. left. exact hI.
Qed.

Lemma disj_intror_is_sound Gamma A B:
  valid (seq Gamma B) -> valid (seq Gamma (Disj A B)).
Proof.
  intro h. unfold valid. intro I. intro hI.
  unfold valid in h. apply (h I) in hI. clear h.
  simpl sat. right. exact hI.
Qed.

Lemma disj_elim_is_sound Gamma A B C:
  valid (seq Gamma (Disj A B)) -> valid (seq (Cons Gamma A) C)
  -> valid (seq (Cons Gamma B) C) -> valid (seq Gamma C).
Proof.
  intros hAB hA hB. unfold valid. intro I. intro hI.
  unfold valid in hAB. assert (hIAB := hAB I hI). clear hAB.
  simpl sat in hIAB. destruct hIAB as [hIA | hIB].
  * unfold valid in hA. simpl sat_list in hA.
    exact (hA I (conj hIA hI)).
  * unfold valid in hB. simpl sat_list in hB.
    exact (hB I (conj hIB hI)).
Qed.

Lemma impl_intro_is_sound Gamma A B:
  valid (seq (Cons Gamma A) B)
  -> valid (seq Gamma (Impl A B)).
Proof.
  intro h. unfold valid. intro I. intro hI.
  simpl sat. intro hIA.
  unfold valid in h. simpl sat_list in h.
  exact (h I (conj hIA hI)).
Qed.

Lemma impl_elim_is_sound Gamma A B:
  valid (seq Gamma (Impl A B)) -> valid (seq Gamma A)
  -> valid (seq Gamma B).
Proof.
  intros hAB hA. unfold valid. intro I. intro hI.
  unfold valid in hAB. assert (h := hAB I hI). clear hAB.
  simpl sat in h. unfold valid in hA.
  exact (h (hA I hI)).
Qed.

Lemma neg_intro_is_sound Gamma A:
  valid (seq (Cons Gamma A) FF)
  -> valid (seq Gamma (Neg A)).
Proof.
  intro h. unfold valid. intro I. intro hI.
  simpl sat. intro hIA. unfold valid in h.
  simpl sat_list in h. simpl sat in h.
  exact (h I (conj hIA hI)).
Qed.

Lemma neg_elim_is_sound Gamma A:
  valid (seq Gamma (Neg A)) -> valid (seq Gamma A)
  -> valid (seq Gamma FF).
Proof.
  intros hnA hA. unfold valid. intro I. intro hI.
  simpl sat. unfold valid in hnA. unfold valid in hA.
  assert (hInA := hnA I hI). clear hnA.
  assert (hIA := hA I hI). clear hA.
  simpl sat in hInA. exact (hInA hIA).
Qed.

Lemma contraction_is_sound Gamma Gamma' A B:
  valid (seq (concat (Cons (Cons Gamma A) A) Gamma') B)
  -> valid (seq (concat (Cons Gamma A) Gamma') B).
Proof.
  intro h. unfold valid. intro I. intro hI.
  unfold valid in h. apply (h I). clear h.
  induction Gamma' as [| Gamma' ih C].
  * simpl sat_list. simpl sat_list in hI.
    destruct hI as (hIA, hIGamma).
    exact (conj hIA (conj hIA hIGamma)).
  * simpl sat_list. simpl sat_list in hI.
    destruct hI as (hI1, hI2). split.
    - exact hI1.
    - apply ih. exact hI2. 
Qed.

Lemma exchange_is_sound Gamma Gamma' A B C:
  valid (seq (concat (Cons (Cons Gamma A) B) Gamma') C)
  -> valid (seq (concat (Cons (Cons Gamma B) A) Gamma') C).
Proof.
  intro h. unfold valid. intro I. intro hI.
  unfold valid in h. apply (h I). clear h.
  induction Gamma' as [| Gamma' ih D].
  * simpl sat_list. simpl sat_list in hI.
    destruct hI as (hIA, (hIB, hIGamma)).
    exact (conj hIB (conj hIA hIGamma)).
  * simpl sat_list. simpl sat_list in hI.
    destruct hI as (hI1, hI2). split.
    - exact hI1.
    - apply ih. exact hI2.
Qed.

Lemma dne_is_sound Gamma A:
  valid (seq Gamma (Neg (Neg A)))
  -> valid (seq Gamma A).
Proof.
  intro h. unfold valid. intro I. intro hI.
  apply dne. unfold valid in h. simpl sat in h.
  apply (h I). exact hI.
Qed.

Inductive Proof: Seq -> Type :=
| AxiomSchema: forall A, Proof (seq (Cons Empty A) A)
| Weakening: forall Gamma A B,
    Proof (seq Gamma B) -> Proof (seq (Cons Gamma A) B)
| Contraction: forall Gamma Gamma' A B,
    Proof (seq (concat (Cons (Cons Gamma A) A) Gamma') B)
    -> Proof (seq (concat (Cons Gamma A) Gamma') B)
| Exchange: forall Gamma Gamma' A B C,
    Proof (seq (concat (Cons (Cons Gamma A) B) Gamma') C)
    -> Proof (seq (concat (Cons (Cons Gamma B) A) Gamma') C)
| ConjIntro: forall Gamma A B,
    Proof (seq Gamma A) -> Proof (seq Gamma B)
    -> Proof (seq Gamma (Conj A B))
| ConjElimL: forall Gamma A B,
    Proof (seq Gamma (Conj A B)) -> Proof (seq Gamma A)
| ConjElimR: forall Gamma A B,
    Proof (seq Gamma (Conj A B)) -> Proof (seq Gamma B)
| DisjIntroL: forall Gamma A B,
    Proof (seq Gamma A) -> Proof (seq Gamma (Disj A B))
| DisjIntroR: forall Gamma A B,
    Proof (seq Gamma B) -> Proof (seq Gamma (Disj A B))
| DisjElim: forall Gamma A B C,
    Proof (seq Gamma (Disj A B)) -> Proof (seq (Cons Gamma A) C)
    -> Proof (seq (Cons Gamma B) C) -> Proof (seq Gamma C)
| ImplIntro: forall Gamma A B,
    Proof (seq (Cons Gamma A) B) -> Proof (seq Gamma (Impl A B))
| ImplElim: forall Gamma A B,
    Proof (seq Gamma (Impl A B)) -> Proof (seq Gamma A)
    -> Proof (seq Gamma B)
| NegIntro: forall Gamma A,
    Proof (seq (Cons Gamma A) FF) -> Proof (seq Gamma (Neg A))
| NegElim: forall Gamma A,
    Proof (seq Gamma (Neg A)) -> Proof (seq Gamma A)
    -> Proof (seq Gamma FF)
| DNE: forall Gamma A,
    Proof (seq Gamma (Neg (Neg A)))
    -> Proof (seq Gamma A).

Theorem soundness_of_natural_deduction:
  forall S, Proof S -> valid S.
Proof.
  intro S. intro pi.
  induction pi as [A
  | Gamma A B pi hpi
  | Gamma Gamma' A B pi hpi
  | Gamma Gamma' A B C pi hpi
  | Gamma A B piA hpiA piB hpiB
  | Gamma A B pi hpi
  | Gamma A B pi hpi
  | Gamma A B pi hpi
  | Gamma A B pi hpi
  | Gamma A B C pi hpi piA hpiA piB hpiB
  | Gamma A B pi hpi
  | Gamma A B piAB hpiAB piA hpiA
  | Gamma A pi hpi
  | Gamma A pinA hpinA piA hpiA
  | Gamma A pi hpi].
  * exact (axiom_schema_is_sound A). 
  * exact (weakening_is_sound Gamma A B hpi).
  * exact (contraction_is_sound Gamma Gamma' A B hpi).
  * exact (exchange_is_sound Gamma Gamma' A B C hpi).
  * exact (conj_intro_is_sound Gamma A B hpiA hpiB).
  * exact (conj_eliml_is_sound Gamma A B hpi).
  * exact (conj_elimr_is_sound Gamma A B hpi).
  * exact (disj_introl_is_sound Gamma A B hpi).
  * exact (disj_intror_is_sound Gamma A B hpi).
  * exact (disj_elim_is_sound Gamma A B C hpi hpiA hpiB).
  * exact (impl_intro_is_sound Gamma A B hpi).
  * exact (impl_elim_is_sound Gamma A B hpiAB hpiA).
  * exact (neg_intro_is_sound Gamma A hpi).
  * exact (neg_elim_is_sound Gamma A hpinA hpiA).
  * exact (dne_is_sound Gamma A hpi).
Qed.

Theorem general_weakening_is_admissble Gamma Gamma' A:
  Proof (seq Gamma A)
  -> Proof (seq (concat Gamma Gamma') A).
Proof.
  intro h. induction Gamma' as [| Gamma' ih B].
  * simpl concat. exact h.
  * simpl concat. apply Weakening. exact ih.
Qed.

