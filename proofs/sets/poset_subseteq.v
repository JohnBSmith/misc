
Require Import Coq.Sets.Ensembles.

Parameter U: Type.
Definition PU := Ensemble U.

Inductive IntersectSys (Asys: Ensemble PU): PU :=
  IntersectSys_intro:
  forall x: U, (forall A: PU, In PU Asys A -> In U A x)
    -> In U (IntersectSys Asys) x.

Inductive UnionSys (Asys: Ensemble PU): PU :=
  UnionSys_intro:
  forall x: U, (exists A: PU, In PU Asys A /\ In U A x)
    -> In U (UnionSys Asys) x.

Definition is_upper_bound (Asys: Ensemble PU) (S: PU)
  := (forall A: PU, In PU Asys A -> Included U A S).

Definition is_lower_bound (S: PU) (Asys: Ensemble PU)
  := (forall A: PU, In PU Asys A -> Included U S A).

Definition is_inf (A: PU) (Asys: Ensemble PU)
  := is_lower_bound A Asys /\
     (forall S, is_lower_bound S Asys -> Included U S A).

Definition is_sup (A: PU) (Asys: Ensemble PU)
  := is_upper_bound Asys A /\
     (forall S, is_upper_bound Asys S -> Included U A S).

Theorem intersection_is_inf (Asys: Ensemble PU):
  is_inf (IntersectSys Asys) Asys.
Proof.
  unfold is_inf. split.
  * unfold is_lower_bound. intro A. intro hA.
    unfold Included. intro x. intro hx.
    destruct hx as (x, hx). exact (hx A hA).
  * intro S. unfold is_lower_bound. intro h.
    unfold Included. intro x. intro hx.
    apply IntersectSys_intro.
    intro A. intro hA.
    assert (hSA := h A hA).
    unfold Included in hSA.
    exact (hSA x hx).
Qed.

Theorem union_is_sup (Asys: Ensemble PU):
  is_sup (UnionSys Asys) Asys.
Proof.
  unfold is_sup. split.
  * unfold is_upper_bound. intro A. intro hA.
    unfold Included. intro x. intro hx.
    apply UnionSys_intro. exists A.
    exact (conj hA hx).
  * intro S. unfold is_upper_bound. intro h.
    unfold Included. intro x. intro hx.
    destruct hx as (x, hx). destruct hx as (A, (hA, hx)).
    assert (hAS := h A hA). unfold Included in hAS.
    exact (hAS x hx).
Qed.

