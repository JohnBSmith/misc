
Require Import ZArith.ZArith.
Require Import Bool.Bool.

Definition Loc := nat.

Inductive Aexpr :=
| int (n: Z)
| loc (X: Loc)
| add (a1 a2: Aexpr)
| sub (a1 a2: Aexpr)
| mul (a1 a2: Aexpr).

Inductive Bexpr :=
| btrue
| bfalse
| beq (a1 a2: Aexpr)
| ble (a1 a2: Aexpr)
| bnot (b: Bexpr)
| band (b1 b2: Bexpr)
| bor (b1 b2: Bexpr).

Inductive Com :=
| Skip
| Assign (X: Loc) (a: Aexpr)
| Seq (c1 c2: Com)
| If (b: Bexpr) (c1 c2: Com)
| While (b: Bexpr) (c: Com).

Definition State := Loc -> Z.

Fixpoint evA (a: Aexpr) (s: State): Z :=
  match a with
  | int n => n
  | loc X => s X
  | add a1 a2 => evA a1 s + evA a2 s
  | sub a1 a2 => evA a1 s - evA a2 s
  | mul a1 a2 => evA a1 s * evA a2 s
  end.

Fixpoint evB (b: Bexpr) (s: State): bool :=
  match b with
  | btrue => true
  | bfalse => false
  | beq a1 a2 => Z.eqb (evA a1 s) (evA a2 s)
  | ble a1 a2 => Z.leb (evA a1 s) (evA a2 s)
  | bnot b => negb (evB b s)
  | band b1 b2 => andb (evB b1 s) (evB b2 s)
  | bor b1 b2 => orb (evB b1 s) (evB b2 s)
  end.

Definition reassign (s: State) (X: Loc) (n: Z): State :=
  fun Y => if Nat.eqb X Y then n else s Y.

Fixpoint iter (ev: State -> State -> Prop)
(N: nat) (b: Bexpr) (s s1: State): Prop :=
  match N with
  | 0 => False
  | S N => if evB b s then
      exists s0, ev s s0 /\ iter ev N b s0 s1
    else s1 = s
  end.

Fixpoint evC (c: Com) (s s1: State): Prop :=
  match c with
  | Skip => s1 = s
  | Assign X a => s1 = reassign s X (evA a s)
  | Seq c1 c2 => exists s0, evC c1 s s0 /\ evC c2 s0 s1
  | If b c1 c2 => if evB b s then evC c1 s s1 else evC c2 s s1
  | While b c => exists N, iter (evC c) N b s s1
  end.

Definition Assertion := State -> Prop.
Definition sat (s: State) (A: Assertion): Prop := A s.

Definition valid (A: Assertion) (c: Com) (B: Assertion) :=
  forall s, sat s A -> forall s', evC c s s' -> sat s' B.

Definition subst (A: Assertion) (X: Loc) (a: Aexpr): Assertion :=
  fun s => A (reassign s X (evA a s)).

Theorem rule_skip_is_valid A:
  valid A Skip A.
Proof.
  unfold valid. intros s hs. intros s1 hs1.
  simpl evC in hs1. rewrite hs1. exact hs.
Qed.

Theorem rule_assign_is_valid A X a:
  valid (subst A X a) (Assign X a) A.
Proof.
  unfold valid. intros s hs. intros s1 hs1.
  simpl evC in hs1.
  unfold sat in hs. unfold subst in hs.
  rewrite hs1. exact hs.
Qed.

Theorem rule_seq_is_valid A B C c1 c2:
  valid A c1 B -> valid B c2 C -> valid A (Seq c1 c2) C.
Proof.
  intros h1 h2. unfold valid. intros s hs. intros s2 hs2.
  simpl evC in hs2.
  destruct hs2 as (s1, (h11, h12)).
  unfold valid in h1. unfold valid in h2.
  assert (h1 := h1 s hs s1 h11).
  exact (h2 s1 h1 s2 h12).
Qed.

Definition Conj (A: Assertion) (b: Bexpr) :=
  fun s => sat s A /\ evB b s = true.

Theorem evB_bnot b s:
  negb (evB b s) = evB (bnot b) s.
Proof.
  simpl evB. reflexivity.
Qed.

Theorem rule_if_is_valid A b C c1 c2:
  valid (Conj A b) c1 C ->
  valid (Conj A (bnot b)) c2 C ->
  valid A (If b c1 c2) C.
Proof.
  intros h1 h2. unfold valid. intros s hs. intros s1 hs1.
  simpl evC in hs1.
  unfold valid in h1. unfold sat in h1. unfold Conj in h1.
  unfold valid in h2. unfold sat in h2. unfold Conj in h2.
  assert (h1 := h1 s). assert (h2 := h2 s).
  rewrite <- (evB_bnot b s) in h2.
  destruct (evB b s).
  * apply h1.
    - exact (conj hs (eq_refl true)).
    - exact hs1.
  * apply h2.
    - simpl. exact (conj hs (eq_refl true)).
    - exact hs1.
Qed.

Definition invariant ev A b := forall s s',
  sat s A /\ evB b s = true -> ev s s' -> sat s' A.

Theorem iter_lemma (ev: State -> State -> Prop) N b A:
  invariant ev A b ->
  (forall s s', sat s A -> iter ev N b s s' ->
    sat s' A /\ evB b s' = false).
Proof.
  intro h.
  induction N as [| N ih].
  * intros s s1. intros hsA hiter.
    simpl iter in hiter. exfalso. exact hiter.
  * intros s s1. intros hsA hiter.
    simpl iter in hiter.
    destruct (evB b s) eqn:heq.
    - destruct hiter as (s0, (h00, h01)).
      apply (ih s0 s1).
      -- unfold invariant in h. apply (h s s0).
         --- exact (conj hsA heq).
         --- exact h00.
      -- exact h01.
    - rewrite hiter. split.
      -- exact hsA.
      -- exact heq.
Qed.

Theorem rule_while_is_valid A b c:
  valid (Conj A b) c A ->
  valid A (While b c) (Conj A (bnot b)).
Proof.
  intro h. unfold valid. intros s hs. intros s2 hs2.
  simpl evC in hs2. destruct hs2 as (N, hiter).
  assert (h0: invariant (evC c) A b). {
    unfold invariant.
    intros s0 s1. intros (hs0A, hs0b) h01. unfold valid in h.
    apply (h s0).
    * unfold sat. unfold Conj. split.
      - exact hs0A.
      - exact hs0b.
    * exact h01.
  }
  assert (h1 := iter_lemma (evC c) N b A h0 s s2 hs hiter).
  destruct h1 as (hs2A, hbs2).
  unfold sat. unfold Conj. split.
  * exact hs2A.
  * simpl evB. rewrite hbs2. simpl. reflexivity.
Qed.
