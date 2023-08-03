
(* Sequent natural deduction for *)
(* classical propositional calculus *)

(* Shown is soundness under classical semantics. *)
(* Furthermore, some admissible rules are shown. *)

Inductive Bool := false | true.
Definition notb (a: Bool) := match a with
  false => true | true => false end.
Definition andb (a b: Bool) := match a with
  false => false | true => b end.
Definition orb (a b: Bool) := match a with
  true => true | false => b end.
Definition is_true (a: Bool): Prop := match a with
  false => False | true => True end.

Theorem notb_to_not {a: Bool}:
  is_true (notb a) -> ~is_true a.
Proof.
  intro h. destruct a.
  * simpl. intro hFalse. exact hFalse.
  * simpl. intro hTrue. simpl in h. exact h.
Qed.

Theorem not_to_notb {a: Bool}:
  ~is_true a -> is_true (notb a).
Proof.
  intro h. destruct a.
  * simpl. trivial.
  * simpl. simpl in h. apply h. trivial.
Qed.

Theorem notb_dne {a: Bool}:
  is_true (notb (notb a)) -> is_true a.
Proof.
  intro h. destruct a.
  * simpl in h. simpl. exact h.
  * simpl. trivial.
Qed.

Theorem andb_to_conj {a b: Bool}:
  is_true (andb a b) -> is_true a /\ is_true b.
Proof.
  intro h. destruct a.
  * simpl in h. destruct b.
    - simpl. exact (conj h h).
    - simpl. split.
      -- exact h.
      -- trivial.
  * simpl in h. simpl. split.
    - trivial.
    - exact h.
Qed.

Theorem conj_to_andb {a b: Bool}:
  is_true a /\ is_true b -> is_true (andb a b).
Proof.
  intro h. destruct a.
  * simpl. simpl in h. exact (proj1 h).
  * simpl. exact (proj2 h).
Qed.

Theorem andb_proj1 {a b: Bool}:
  is_true (andb a b) -> is_true a.
Proof.
  intro h. destruct a.
  * simpl in h. simpl. exact h.
  * simpl. trivial. 
Qed.

Theorem andb_proj2 {a b: Bool}:
  is_true (andb a b) -> is_true b.
Proof.
  intro h. destruct a.
  * simpl in h. destruct b.
    - simpl. exact h.
    - simpl. trivial.
  * simpl in h. exact h.
Qed.

Theorem andb_intro {a b: Bool}:
  is_true a -> is_true b -> is_true (andb a b).
Proof.
  intro ha. intro hb. destruct a.
  * simpl. simpl in ha. exact ha.
  * simpl. exact hb.
Qed.

Theorem orb_introl {a b: Bool}:
  is_true a -> is_true (orb a b).
Proof.
  intro h. destruct a.
  * destruct b.
    - simpl. simpl in h. exact h.
    - simpl. trivial.
  * simpl. trivial.
Qed.

Theorem orb_intror {a b: Bool}:
  is_true b -> is_true (orb a b).
Proof.
  intro h. destruct a.
  * simpl. exact h.
  * simpl. trivial.
Qed.

Theorem orb_to_or {a b: Bool}:
  is_true (orb a b) -> (is_true a) \/ (is_true b).
Proof.
  intro h. destruct a.
  * simpl in h. right. exact h.
  * left. simpl. simpl in h. exact h.
Qed.

Theorem implb_to_impl {a b: Bool}:
  is_true (orb (notb a) b) -> is_true a -> is_true b.
Proof.
  intro h. intro ha. destruct a.
  * destruct b.
    - simpl. simpl in ha. exact ha.
    - simpl. simpl in h. exact h.
  * simpl in h. exact h.
Qed.

Theorem impl_to_implb {a b: Bool}:
  (is_true a -> is_true b) -> is_true (orb (notb a) b).
Proof.
  intro h. destruct a.
  * simpl. trivial.
  * simpl. apply h. simpl. trivial.
Qed.

(* The type of atomic variables *)
Inductive Var := var: nat -> Var.

(* Recursive definition of the type of *)
(* well-formed logical formulas *)
Inductive Formula: Set :=
| Atom: Var -> Formula
| FF: Formula
| TF: Formula
| Neg: Formula -> Formula
| Conj: Formula -> Formula -> Formula
| Disj: Formula -> Formula -> Formula
| Impl: Formula -> Formula -> Formula.

(* Satisfaction relation *)
Fixpoint sat (I: Var -> Bool) (A: Formula) :=
  match A with
  | Atom v => I v
  | FF => false
  | TF => true
  | Neg A => notb (sat I A)
  | Conj A B => andb (sat I A) (sat I B)
  | Disj A B => orb (sat I A) (sat I B)
  | Impl A B => orb (notb (sat I A)) (sat I B)
  end.

Definition tautology (A: Formula) :=
  forall I, is_true (sat I A).

Inductive List :=
| Empty
| Cons: List -> Formula -> List.

Fixpoint concat (Gamma Gamma': List) :=
  match Gamma' with
  | Empty => Gamma
  | (Cons Gamma' A) => Cons (concat Gamma Gamma') A
  end.

(* The type of sequents *)
Inductive Seq := seq: List -> Formula -> Seq.

Fixpoint sat_list (I: Var -> Bool) (Gamma: List) :=
  match Gamma with
  | Empty => true
  | Cons Gamma A => andb (sat I A) (sat_list I Gamma)
  end.

(* Logically valid sequents *)
Definition valid '(seq Gamma A) :=
  forall I, is_true (sat_list I Gamma) -> is_true (sat I A).

Theorem valid_empty_is_tautology (A: Formula):
  valid (seq Empty A) <-> tautology A.
Proof.
  split.
  * intro h. unfold tautology. intro I.
    unfold valid in h. simpl sat_list in h.
    apply (h I). simpl is_true. trivial.
  * intro h. unfold tautology in h.
    unfold valid. intro I. intro h0. clear h0.
    exact (h I).
Qed.

Lemma basic_seq_intro_is_sound A:
  valid (seq (Cons Empty A) A).
Proof.
  unfold valid. intro I. intro h.
  simpl sat_list in h.
  exact (andb_proj1 h).
Qed.

Lemma weakening_is_sound Gamma A B:
  valid (seq Gamma B) -> valid (seq (Cons Gamma A) B).
Proof.
  intro h. unfold valid. intro I. intro hI.
  simpl sat_list in hI. unfold valid in h.
  exact (h I (andb_proj2 hI)).
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
  exact (andb_intro hIA hIB).
Qed.

Lemma conj_eliml_is_sound Gamma A B:
  valid (seq Gamma (Conj A B)) -> valid (seq Gamma A).
Proof.
  intro h. unfold valid. intro I. intro hI.
  unfold valid in h. apply (h I) in hI. clear h.
  simpl sat in hI. exact (andb_proj1 hI).
Qed.

Lemma conj_elimr_is_sound Gamma A B:
  valid (seq Gamma (Conj A B)) -> valid (seq Gamma B).
Proof.
  intro h. unfold valid. intro I. intro hI.
  unfold valid in h. apply (h I) in hI. clear h.
  simpl sat in hI. exact (andb_proj2 hI).
Qed.

Lemma disj_introl_is_sound Gamma A B:
  valid (seq Gamma A) -> valid (seq Gamma (Disj A B)).
Proof.
  intro h. unfold valid. intro I. intro hI.
  unfold valid in h. apply (h I) in hI. clear h.
  simpl sat. apply orb_introl. exact hI.
Qed.

Lemma disj_intror_is_sound Gamma A B:
  valid (seq Gamma B) -> valid (seq Gamma (Disj A B)).
Proof.
  intro h. unfold valid. intro I. intro hI.
  unfold valid in h. apply (h I) in hI. clear h.
  simpl sat. apply orb_intror. exact hI.
Qed.

Lemma disj_elim_is_sound Gamma A B C:
  valid (seq Gamma (Disj A B)) -> valid (seq (Cons Gamma A) C)
  -> valid (seq (Cons Gamma B) C) -> valid (seq Gamma C).
Proof.
  intros hAB hA hB. unfold valid. intro I. intro hI.
  unfold valid in hAB. assert (hIAB := hAB I hI). clear hAB.
  simpl sat in hIAB. apply orb_to_or in hIAB.
  destruct hIAB as [hIA | hIB].
  * unfold valid in hA. simpl sat_list in hA.
    exact (hA I (andb_intro hIA hI)).
  * unfold valid in hB. simpl sat_list in hB.
    exact (hB I (andb_intro hIB hI)).
Qed.

Lemma impl_intro_is_sound Gamma A B:
  valid (seq (Cons Gamma A) B)
  -> valid (seq Gamma (Impl A B)).
Proof.
  intro h. unfold valid. intro I. intro hI.
  simpl sat. apply impl_to_implb. intro hIA.
  unfold valid in h. simpl sat_list in h.
  exact (h I (andb_intro hIA hI)).
Qed.

Lemma impl_elim_is_sound Gamma A B:
  valid (seq Gamma (Impl A B)) -> valid (seq Gamma A)
  -> valid (seq Gamma B).
Proof.
  intros hAB hA. unfold valid. intro I. intro hI.
  unfold valid in hAB. assert (h := hAB I hI). clear hAB.
  simpl sat in h. unfold valid in hA.
  assert (h' := implb_to_impl h).
  exact (h' (hA I hI)).
Qed.

Lemma neg_intro_is_sound Gamma A:
  valid (seq (Cons Gamma A) FF)
  -> valid (seq Gamma (Neg A)).
Proof.
  intro h. unfold valid. intro I. intro hI.
  simpl sat. apply not_to_notb.
  intro hIA. unfold valid in h.
  simpl sat_list in h. simpl sat in h.
  exact (h I (andb_intro hIA hI)).
Qed.

Lemma neg_elim_is_sound Gamma A:
  valid (seq Gamma (Neg A)) -> valid (seq Gamma A)
  -> valid (seq Gamma FF).
Proof.
  intros hnA hA. unfold valid. intro I. intro hI.
  simpl sat. unfold valid in hnA. unfold valid in hA.
  assert (hInA := hnA I hI). clear hnA.
  assert (hIA := hA I hI). clear hA.
  simpl sat in hInA. apply notb_to_not in hInA.
  exact (hInA hIA).
Qed.

Lemma contraction_is_sound Gamma Gamma' A B:
  valid (seq (concat (Cons (Cons Gamma A) A) Gamma') B)
  -> valid (seq (concat (Cons Gamma A) Gamma') B).
Proof.
  intro h. unfold valid. intro I. intro hI.
  unfold valid in h. apply (h I). clear h.
  induction Gamma' as [| Gamma' ih C].
  * simpl sat_list. simpl sat_list in hI.
    destruct (andb_to_conj hI) as (hIA, hIGamma).
    exact (andb_intro hIA (andb_intro hIA hIGamma)).
  * simpl sat_list. simpl sat_list in hI.
    destruct (andb_to_conj hI) as (hI1, hI2).
    apply conj_to_andb. split.
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
    apply andb_to_conj in hI.
    destruct hI as (hIA, htail).
    apply andb_to_conj in htail.
    destruct htail as (hIB, hIGamma).
    exact (andb_intro hIB (andb_intro hIA hIGamma)).
  * simpl sat_list. simpl sat_list in hI.
    destruct (andb_to_conj hI) as (hI1, hI2).
    apply conj_to_andb. split.
    - exact hI1.
    - apply ih. exact hI2.
Qed.

Lemma dne_is_sound Gamma A:
  valid (seq Gamma (Neg (Neg A)))
  -> valid (seq Gamma A).
Proof.
  intro h. unfold valid. intro I. intro hI.
  unfold valid in h. simpl sat in h.
  assert (hIA := notb_dne (h I hI)).
  exact hIA.
Qed.

Inductive Proof: Seq -> Prop :=
| BasicSeqIntro: forall A, Proof (seq (Cons Empty A) A)
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
  * exact (basic_seq_intro_is_sound A). 
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

Fixpoint is_in (A: Formula) (Gamma: List): Prop :=
  match Gamma with
  | Empty => False
  | (Cons Gamma B) => A = B \/ is_in A Gamma
  end.

Theorem basic_seq_intro_general1_is_admissible Gamma A:
  Proof (seq (Cons Gamma A) A).
Proof.
  induction Gamma as [| Gamma ih B].
  * exact (BasicSeqIntro A).
  * pose (Gamma' := (Cons (Cons Gamma A) B)).
    assert (h: Proof (seq (concat Gamma' Empty) A)). {
      simpl concat. unfold Gamma'.
      apply Weakening. exact ih.
    }
    assert (h' := Exchange Gamma Empty A B A h).
    simpl concat in h'. exact h'.
Qed.

