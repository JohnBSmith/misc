
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

Theorem conj_commutes_forward (A B: Prop): A /\ B -> B /\ A.
Proof.
  intro h.
  destruct h as (a, b).
  assert (ba := conj b a).
  exact ba.
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

Theorem conj_distributes (A B C: Prop): A /\ (B \/ C) <-> A /\ B \/ A /\ C.
Proof.
  split.
  * intro h.
    destruct h as (a, bc).
    destruct bc as [b | c].
    - left.  split. exact a. exact b.
    - right. split. exact a. exact c.
  * intro h.
    destruct h as [(a, b) | (a, c)].
    - split. exact a. left.  exact b.
    - split. exact a. right. exact c.
Qed.

Theorem conj_distributes_term (A B C: Prop): A /\ (B \/ C) <-> A /\ B \/ A /\ C.
Proof.
  exact (conj
    (fun '(conj a bc) =>
      match bc with
      | or_introl b => or_introl (conj a b)
      | or_intror c => or_intror (conj a c)
      end)
    (fun h =>
      match h with
      | or_introl (conj a b) => (conj a (or_introl b))
      | or_intror (conj a c) => (conj a (or_intror c))
      end)).
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

Theorem modus_ponens_forward (A B: Prop): A /\ (A -> B) -> B.
Proof.
  intro h.
  destruct h as (a, f).
  assert (b := f a).
  exact b.
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

Theorem contraposition_tautology_forward (A B: Prop):
  (A -> B) -> (~B -> ~A).
Proof.
  unfold not.
  intro h. intro nb. intro a.
  assert (b := h a).
  assert (contradiction := nb b).
  exact contradiction.
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

Theorem intro_double_negation_forward (A: Prop): A -> ~~A.
Proof.
  unfold not.
  intro a. intro na.
  assert (contradiction := na a).
  exact contradiction.
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

Theorem non_contradiction (A: Prop): ~(A /\ ~A).
Proof.
  unfold not.
  intro h.
  destruct h as (a, na).
  apply na.
  exact a.
Qed.

Theorem non_contradiction_forward (A: Prop): ~(A /\ ~A).
Proof.
  unfold not.
  intro h.
  destruct h as (a, na).
  exact (na a).
Qed.

Theorem non_contradiction_term (A: Prop): ~(A /\ ~A).
Proof.
  exact (fun '(conj a na) => na a).
Qed.

Theorem bicond_reflexivity (A: Prop): (A <-> A).
Proof.
  split.
  - intro a. exact a.
  - intro a. exact a.
Qed.

Theorem bicond_reflexivity_forward (A: Prop): (A <-> A).
Proof.
  unfold iff.
  assert (f := fun a: A => a).
  exact (conj f f).
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

Theorem bicond_symmetry_forward (A B: Prop): (A <-> B) -> (B <-> A).
Proof.
  intro h.
  destruct h as (f, g).
  unfold iff.
  assert (gf := (conj g f)).
  exact gf.
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
  - intro a. apply fbc. apply fab. exact a.
  - intro c. apply fba. apply fcb. exact c.
Qed.

Theorem bicond_transitivity_forward (A B C: Prop):
  (A <-> B) /\ (B <-> C) -> (A <-> C).
Proof.
  unfold iff.
  intro h.
  destruct h as ((fab, fba), (fbc, fcb)).
  assert (fac := fun a => fbc (fab a)).
  assert (fca := fun c => fba (fcb c)).
  exact (conj fac fca).
Qed.

Theorem bicond_transitivity_term (A B C: Prop):
  (A <-> B) /\ (B <-> C) -> (A <-> C).
Proof.
  exact (fun '(conj (conj fab fba) (conj fbc fcb)) =>
    conj (fun a => fbc (fab a)) (fun c => fba (fcb c))).
Qed.

Theorem exportation (A B C: Prop):
  (A -> B -> C) <-> (A /\ B -> C).
Proof.
  split.
  * intro h. intro ab. destruct ab as (a, b).
    apply h. exact a. exact b.
  * intro h. intro a. intro b.
    apply h. split. exact a. exact b.
Qed.

Theorem exportation_forward (A B C: Prop):
  (A -> B -> C) <-> (A /\ B -> C).
Proof.
  split.
  * intro h. intro ab. destruct ab as (a, b).
    assert (bc := h a).
    exact (bc b).
  * intro h. intro a. intro b.
    assert (ab := conj a b).
    exact (h ab).
Qed.

Theorem exportation_term (A B C: Prop):
  (A -> B -> C) <-> (A /\ B -> C).
Proof.
  exact (conj
    (fun h => fun '(conj a b) => (h a) b)
    (fun h a b => h (conj a b))).
Qed.

Theorem cond_distributes_over_cond (A B C: Prop):
  (A -> B -> C) -> (A -> B) -> (A -> C).
Proof.
  intro f. intro g. intro a.
  apply f.
  * exact a.
  * apply g. exact a.
Qed.

Theorem cond_distributes_over_cond_forward (A B C: Prop):
  (A -> B -> C) -> (A -> B) -> (A -> C).
Proof.
  intro f. intro g. intro a.
  assert (b := g a).
  exact (f a b).
Qed.

Theorem cond_distributes_over_cond_term (A B C: Prop):
  (A -> B -> C) -> (A -> B) -> (A -> C).
Proof.
  exact (fun f g a => f a (g a)).
Qed.

Theorem conj_De_Morgan (A B: Prop):
  ~A \/ ~B -> ~(A /\ B).
Proof.
  intro h. intro ab.
  destruct ab as (a, b).
  destruct h as [na | nb].
  * apply na. exact a.
  * apply nb. exact b.
Qed.

Theorem conj_De_Morgan_forward (A B: Prop):
  ~A \/ ~B -> ~(A /\ B).
Proof.
  intro h. intro ab.
  destruct ab as (a, b).
  destruct h as [na | nb].
  * apply (na a).
  * apply (nb b).
Qed.

Theorem conj_De_Morgan_term (A B: Prop):
  ~A \/ ~B -> ~(A /\ B).
Proof.
  exact (fun h => fun '(conj a b) =>
    match h with
    | or_introl na => na a
    | or_intror nb => nb b
    end).
Qed.

Theorem disj_De_Morgan (A B: Prop):
  ~A /\ ~B -> ~(A \/ B).
Proof.
  intro h.
  destruct h as (na, nb).
  intro dab.
  destruct dab as [a | b].
  * apply na. exact a.
  * apply nb. exact b.
Qed.

Theorem disj_De_Morgan_forward (A B: Prop):
  ~A /\ ~B -> ~(A \/ B).
Proof.
  intro h.
  destruct h as (na, nb).
  intro dab.
  destruct dab as [a | b].
  * exact (na a).
  * exact (nb b).
Qed.

Theorem disj_De_Morgan_term (A B: Prop):
  ~A /\ ~B -> ~(A \/ B).
Proof.
  exact (fun '(conj na nb) => fun dab =>
    match dab with
    | or_introl a => na a
    | or_intror b => nb b
    end).
Qed.

Theorem constructive_dilemma (A B C D: Prop):
  (A -> B) /\ (C -> D) /\ (A \/ C) -> B \/ D.
Proof.
  intro h.
  destruct h as (fab, (fcd, dac)).
  destruct dac as [a | c].
  * left.  apply fab. exact a.
  * right. apply fcd. exact c.
Qed.

Theorem constructive_dilemma_forward (A B C D: Prop):
  (A -> B) /\ (C -> D) /\ (A \/ C) -> B \/ D.
Proof.
  intro h.
  destruct h as (fab, (fcd, dac)).
  destruct dac as [a | c].
  * assert (b := fab a). exact (or_introl b).
  * assert (d := fcd c). exact (or_intror d).
Qed.

Theorem constructive_dilemma_term (A B C D: Prop):
  (A -> B) /\ (C -> D) /\ (A \/ C) -> B \/ D.
Proof.
  exact (fun '(conj fab (conj fcd dac)) =>
    match dac with
    | or_introl a => (or_introl (fab a))
    | or_intror c => (or_intror (fcd c))
    end).
Qed.

Theorem cond_distributes_over_conj (A B C: Prop):
  (A -> B /\ C) <-> (A -> B) /\ (A -> C).
Proof.
  split.
  * intro h.
    split.
    - intro a. apply h. exact a.
    - intro a. apply h. exact a.
  * intro h. destruct h as (fab, fac).
    intro a.
    split.
    - apply fab. exact a.
    - apply fac. exact a.
Qed.

Theorem cond_distributes_over_conj_forward (A B C: Prop):
  (A -> B /\ C) <-> (A -> B) /\ (A -> C).
Proof.
  split.
  * intro h.
    assert (fab: A -> B). {
      intro a. assert (bc := h a). exact (proj1 bc).
    }
    assert (fac: A -> C). {
      intro a. assert (bc := h a). exact (proj2 bc).
    }
    exact (conj fab fac).
  * intro h. intro a. destruct h as (fab, fac).
    assert (b := fab a). assert (c := fac a).
    exact (conj b c).
Qed.

Theorem cond_distributes_over_conj_term (A B C: Prop):
  (A -> B /\ C) <-> (A -> B) /\ (A -> C).
Proof.
  exact (conj
    (fun h => conj (fun a => proj1 (h a)) (fun a => proj2 (h a)))
    (fun '(conj fab fac) => fun a => conj (fab a) (fac a))).
Qed.
