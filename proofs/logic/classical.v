
Definition DNE := forall (A: Prop), ~~A -> A.
Definition LEM := forall (A: Prop), A \/ ~A.
Definition ExFalso := forall (A: Prop), False -> A.

Theorem dne_implies_lem: DNE -> LEM.
Proof.
  intro dne. intro A. apply dne.
  intro h. apply h. right.
  intro a. apply h. left.
  exact a.
Qed.

Theorem dne_implies_ex_falso: DNE -> ExFalso.
Proof.
  intro dne. intro A. intro contradiction.
  apply dne. intro na. exact contradiction.
Qed.

Theorem lem_and_ex_falso_implies_dne: LEM /\ ExFalso -> DNE.
Proof.
  intro h.
  destruct h as (lem, ex_falso).
 intro A. intro nna.
  assert (dana := lem A).
  destruct dana as [a | na].
  * exact a.
  * apply ex_falso. contradict nna. exact na.
Qed.

Theorem contraposition (A B: Prop):
  (A -> B) -> (~B -> ~A).
Proof.
  intros h nb a.
  destruct nb.
  apply h. exact a.
Qed.

Theorem reverse_contraposition (dne: DNE) (A B: Prop):
  (~B -> ~A) -> (A -> B).
Proof.
  assert (ex_falso := dne_implies_ex_falso dne).
  assert (lem := dne_implies_lem dne).
  intro h. intro a.
  assert (dbnb := lem B).
  destruct dbnb as [b | nb].
  * exact b. 
  * apply ex_falso. contradict a.
    apply h. exact nb.
Qed.

Theorem classical_contraposition (dne: DNE) (A B: Prop):
  (A -> B) <-> (~B -> ~A).
Proof.
  split.
  * apply contraposition.
  * apply (reverse_contraposition dne).
Qed.

