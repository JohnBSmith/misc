
Theorem projl (A B: Prop): A /\ B -> A.
Proof.
  intro h.
  destruct h as (a, b).
  exact a.
Qed.

Theorem projl_term (A B: Prop): A /\ B -> A.
Proof.
  exact (fun '(conj a b) => a).
Qed.

Theorem projl_term_types (A B: Type): A*B -> A.
Proof.
  exact (fun '(a, b) => a).
Qed.

Theorem projl_term_ind (A B: Prop): A /\ B -> A.
Proof.
  exact (fun h => and_ind (fun a b => a) h).
Qed.

Theorem conj_commutes (A B: Prop): A /\ B -> B /\ A.
Proof.
  intro h.
  destruct h as (a, b).
  split.
  - exact b.
  - exact a.
Qed.

Theorem conj_commutes_term (A B: Prop): A /\ B -> B /\ A.
Proof.
  exact (fun '(conj a b) => conj b a).
Qed.

Theorem conj_commutes_term_types(A B: Type): A*B -> B*A.
Proof.
  exact (fun '(a, b) => (b, a)).
Qed.

Theorem conj_commutes_term_ind (A B: Prop): A /\ B -> B /\ A.
Proof.
  exact (fun h => and_ind (fun a b => conj b a) h).
Qed.

Theorem disj_commutes (A B: Prop): A \/ B -> B \/ A.
Proof.
  intro h.
  destruct h as [a | b].
  - right. exact a.
  - left.  exact b.
Qed.

Theorem disj_commutes_term (A B: Prop): A \/ B -> B \/ A.
Proof.
  exact (fun h =>
    match h with
    | or_introl a => or_intror a 
    | or_intror b => or_introl b
    end).
Qed.

Theorem disj_commutes_term_types (A B: Type): A + B -> B + A.
Proof.
  exact (fun h =>
    match h with
    | inl a => inr a 
    | inr b => inl b
    end).
Qed.

Theorem conj_distributes (A B C: Prop): A /\ (B \/ C) -> A /\ B \/ A /\ C.
Proof.
  intro h.
  destruct h as (a, bc).
  destruct bc as [b | c].
  - left.  split. exact a. exact b.
  - right. split. exact a. exact c.
Qed.

Theorem conj_distributes_term (A B C: Prop): A /\ (B \/ C) -> A /\ B \/ A /\ C.
Proof.
  exact (fun '(conj a bc) =>
    match bc with
    | or_introl b => or_introl (conj a b) 
    | or_intror c => or_intror (conj a c)
    end).
Qed.

Theorem conj_distributes_term_types (A B C: Prop): A*(B + C) -> A*B + A*C.
Proof.
  exact (fun '(a, bc) =>
    match bc with
    | inl b => inl (a, b) 
    | inr c => inr (a, c)
    end).
Qed.

Theorem modus_ponens (A B: Prop): A /\ (A -> B) -> B.
Proof.
  intro h.
  destruct h as (a, f).
  apply f. exact a.
Qed.

Theorem modus_ponens_term (A B: Prop): A /\ (A -> B) -> B.
Proof.
  exact (fun '(conj a f) => f a).
Qed.

Theorem modus_ponens_term_types (A B: Type): A*(A -> B) -> B.
Proof.
  exact (fun '(a, f) => f a).
Qed.

Theorem modus_ponens_term_ind (A B: Prop): A /\ (A -> B) -> B.
Proof.
  exact (fun h => and_ind (fun a f => f a) h).
Qed.

Theorem contraposition_tautology (A B: Prop):
  (A -> B) -> (~B -> ~A).
Proof.
  intros h nb a.
  destruct nb.
  apply h. exact a.
Qed.

Theorem contraposition_tautology_term (A B: Prop):
  (A -> B) -> (~B -> ~A).
Proof.
  exact (fun h nb a => nb (h a)).
Qed.

Theorem contraposition_tautology_term_types (A B: Type):
  (A -> B) -> ((B -> False) -> (A -> False)).
Proof.
  exact (fun h nb a => nb (h a)).
Qed.

Theorem intro_double_negation (A: Prop): A -> ~~A.
Proof.
  intros a na.
  apply na. exact a.
Qed.

Theorem intro_double_negation_term (A: Prop): A -> ~~A.
Proof.
  exact (fun a => fun na => na a).
Qed.

Theorem intro_double_negation_term_types (A: Type):
  A -> (A -> False) -> False.
Proof.
  exact (fun a => fun na => na a).
Qed.

Theorem bicond_reflexivity (A: Prop): (A <-> A).
Proof.
  split.
  - intro a. exact a.
  - intro a. exact a.
Qed.

Theorem bicond_reflexivity_term (A: Prop): (A <-> A).
Proof.
  exact (conj (fun a => a) (fun a => a)).
Qed.

Theorem bicond_symmetry (A B: Prop): (A <-> B) -> (B <-> A).
Proof.
  intro h.
  destruct h as (f, g).
  split.
  - exact g.
  - exact f.
Qed.

Theorem bicond_symmetry_term (A B: Prop): (A <-> B) -> (B <-> A).
Proof.
  exact (fun '(conj f g) => conj g f).
Qed.

Theorem bicond_transitivity (A B C: Prop):
  (A <-> B) /\ (B <-> C) -> (A <-> C).
Proof.
  intro h.
  destruct h as ((fab, fba), (fbc, fcb)).
  split.
  - apply (fun x => fbc (fab x)).
  - apply (fun x => fba (fcb x)).
Qed.

Theorem bicond_transitivity_term (A B C: Prop):
  (A <-> B) /\ (B <-> C) -> (A <-> C).
Proof.
  exact (fun '(conj (conj fab fba) (conj fbc fcb)) =>
    conj (fun x => fbc (fab x)) (fun x => fba (fcb x))).
Qed.
