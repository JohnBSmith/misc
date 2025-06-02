
(* It is shown that the Gödel-McKinsey-Tarski translation of an
   intuitionistic formula into a formula of the modal logic S4
   preserves the validity of the formula. *)

Definition preorder (W: Type) (R: W -> W -> Prop) :=
  (forall x: W, R x x) /\
  (forall x y z: W, R x y -> R y z -> R x z).

Definition monotonic (W: Type) (R: W -> W -> Prop)
  (V: W -> nat -> Prop) :=
  forall P x y, R x y -> V x P -> V y P.

(* Intuitionistic formulas *)
Inductive Formula :=
| var: nat -> Formula
| falsum: Formula
| conj: Formula -> Formula -> Formula
| disj: Formula -> Formula -> Formula
| subj: Formula -> Formula -> Formula.

(* Intuitionistic Kripke semantics, satisfaction relation *)
Fixpoint sat (W: Type) (R: W -> W -> Prop)
  (V: W -> nat -> Prop) (w: W) (A: Formula) :=
  match A with
  | var P => V w P
  | falsum => False
  | conj A B => sat W R V w A /\ sat W R V w B
  | disj A B => sat W R V w A \/ sat W R V w B
  | subj A B => forall w', R w w' -> sat W R V w' A -> sat W R V w' B
  end.

(* Intuitionistic Kripke semantics, validity *)
Definition valid (A: Formula) :=
  forall W R V w, preorder W R -> monotonic W R V ->
    sat W R V w A.

(* S4 Formulas *)
Inductive MFormula :=
| mvar: nat -> MFormula
| mfalsum: MFormula
| mconj: MFormula -> MFormula -> MFormula
| mdisj: MFormula -> MFormula -> MFormula
| msubj: MFormula -> MFormula -> MFormula
| mnec: MFormula -> MFormula.

(* S4 Kripke semantics, satisfaction relation *)
Fixpoint msat (W: Type) (R: W -> W -> Prop)
  (V: W -> nat -> Prop) (w: W) (A: MFormula) :=
  match A with
  | mvar P => V w P
  | mfalsum => False
  | mconj A B => msat W R V w A /\ msat W R V w B
  | mdisj A B => msat W R V w A \/ msat W R V w B
  | msubj A B => msat W R V w A -> msat W R V w B
  | mnec A => forall w', R w w' -> msat W R V w' A
  end.

(* S4 Kripke semantics, validity *)
Definition S4_valid (A: MFormula) :=
  forall W R V w, preorder W R ->
    msat W R V w A.

(* The Gödel-McKinsey-Tarski translation *)
Fixpoint T (A: Formula): MFormula :=
  match A with
  | var P => mnec (mvar P)
  | falsum => mfalsum
  | conj A B => mconj (T A) (T B)
  | disj A B => mdisj (T A) (T B)
  | subj A B => mnec (msubj (T A) (T B))
  end.

Theorem lemma1 W R V: preorder W R -> monotonic W R V ->
  forall A w, sat W R V w A <-> msat W R V w (T A).
Proof.
  intros hR hV. intro A.
  induction A as [P | | A ihA B ihB | A ihA B ihB | A ihA B ihB].
  * intro w. split.
    - intro h. simpl T. simpl msat. simpl sat in h.
      intro w'. intro hww'. unfold monotonic in hV.
      exact (hV P w w' hww' h).
    - intro h. simpl sat. simpl T in h. simpl msat in h.
      apply (h w). unfold preorder in hR.
      destruct hR as (hrefl, _). exact (hrefl w).
  * intro w. simpl sat. simpl T. simpl msat.
    split; trivial.
  * intro w. split.
    - intro h. simpl sat in h.
      destruct h as (hA, hB).
      simpl msat. split.
      -- apply (ihA w). exact hA.
      -- apply (ihB w). exact hB.
    - intro h. simpl T in h. simpl msat in h.
      destruct h as (hA, hB).
      simpl sat. split.
      -- apply (ihA w). exact hA.
      -- apply (ihB w). exact hB.
  * intro w. split.
    - intro h. simpl T. simpl msat.
      simpl sat in h.
      destruct h as [hA | hB].
      -- left.  apply (ihA w). exact hA.
      -- right. apply (ihB w). exact hB.
    - intro h. simpl sat.
      simpl T in h. simpl msat in h.
      destruct h as [hA | hB].
      -- left.  apply (ihA w). exact hA.
      -- right. apply (ihB w). exact hB.
  * intro w. split.
    - intro h. simpl T. simpl msat. intros w' hww' hA.
      apply (ihA w') in hA. clear ihA. simpl sat in h.
      assert (hB := h w' hww' hA). clear h hww' hA. 
      apply (ihB w') in hB. exact hB.
    - intro h. simpl sat. intros w' hww' hA.
      apply (ihA w') in hA. clear ihA.
      simpl T in h. simpl msat in h.
      assert (hB := h w' hww' hA). clear h hww' hA.
      apply (ihB w') in hB. exact hB.
Qed.

Theorem lemma2 W R V: preorder W R ->
  let Vi w P := msat W R V w (mnec (mvar P)) in
    forall A w, sat W R Vi w A <-> msat W R V w (T A).
Proof.
  intro hR. intro Vi. intro A.
  induction A as [P | | A ihA B ihB | A ihA B ihB | A ihA B ihB].
  * intro w. split.
    - intro h. simpl T. simpl sat in h.
      unfold Vi in h. exact h.
    - intro h. simpl sat. unfold Vi.
      simpl T in h. exact h.
  * intro w. simpl sat. simpl T. simpl msat.
    split; trivial.
  * intro w. split.
    - intro h. simpl T. simpl msat.
      simpl sat in h. destruct h as (hA, hB).
      split.
      -- apply (ihA w). exact hA.
      -- apply (ihB w). exact hB.
    - intro h. simpl sat. simpl T in h. simpl msat in h.
      destruct h as (hA, hB). split.
      -- apply (ihA w). exact hA.
      -- apply (ihB w). exact hB.
  * intro w. split.
    - intro h. simpl T. simpl msat. simpl sat in h.
      destruct h as [hA | hB].
      -- left.  apply (ihA w). exact hA.
      -- right. apply (ihB w). exact hB.
    - intro h. simpl sat. simpl T in h. simpl msat in h.
      destruct h as [hA | hB].
      -- left.  apply (ihA w). exact hA.
      -- right. apply (ihB w). exact hB.
  * intro w. split.
    - intro h. simpl T. simpl msat. intros w' hww' hA.
      apply (ihA w') in hA. clear ihA. simpl sat in h.
      assert (hB := h w' hww' hA). clear h hww' hA.
      apply (ihB w') in hB. exact hB.
    - intro h. simpl sat. intros w' hww' hA.
      apply (ihA w') in hA. clear ihA.
      simpl T in h. simpl msat in h.
      assert (hB := h w' hww' hA). clear h hww' hA.
      apply (ihB w') in hB. exact hB.
Qed.

Theorem T_preserves_validity (A: Formula):
  valid A <-> S4_valid (T A).
Proof.
  split.
  * intro h. unfold S4_valid.
    intros W R V w. intro hR.
    pose (Vi w P := msat W R V w (mnec (mvar P))).
    assert (hVi: monotonic W R Vi). {
      unfold monotonic. intros P x y. intros hxy hx.
      unfold Vi. simpl msat. intros z hz.
      unfold Vi in hx. simpl msat in hx.
      apply (hx z). unfold preorder in hR.
      destruct hR as (_, htrans).
      exact (htrans x y z hxy hz).
    }
    unfold valid in h.
    assert (h := h W R Vi w hR hVi).
    apply (lemma2 W R V hR A w). exact h.
  * intro h. unfold valid.
    intros W R V w. intros hR hV.
    unfold S4_valid in h.
    assert (h := h W R V w hR).
    apply (lemma1 W R V hR hV). exact h.
Qed.
