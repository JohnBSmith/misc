
Theorem ex_falso_quodlibet (A: Prop): False -> A.
Proof.
  intro h. exfalso. exact h.
Qed.

Theorem ex_falso_quodlibet_term (A: Prop): False -> A.
Proof.
  exact (fun h => match h with end).
Qed.

(* Modus tollendo ponens *)
Theorem disjunctive_syllogism (A B: Prop):
  A \/ B -> ~A -> B.
Proof.
  intro h. intro na.
  destruct h as [a | b].
  * exfalso. eapply na. exact a.
  * exact b.
Qed.

Theorem disjunctive_syllogism_forward (A B: Prop):
  A \/ B -> ~A -> B.
Proof.
  intro h. intro na.
  destruct h as [a | b].
  * exact (ex_falso_quodlibet B (na a)).
  * exact b.
Qed.

Theorem disjunctive_syllogism_term (A B: Prop):
  A \/ B -> ~A -> B.
Proof.
  exact (fun h => fun na =>
    match h with
    | or_introl a => match na a with end
    | or_intror b => b
    end).
Qed.
