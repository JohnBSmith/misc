
Require Import ZArith.ZArith.
Require Import Bool.Bool.

Definition Loc := nat.
Definition State := Loc -> Z.

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

Definition variant (s: State) (X: Loc) (n: Z): State :=
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
  | Assign X a => s1 = variant s X (evA a s)
  | Seq c1 c2 => exists s0, evC c1 s s0 /\ evC c2 s0 s1
  | If b c1 c2 => if evB b s then evC c1 s s1 else evC c2 s s1
  | While b c => exists N, iter (evC c) N b s s1
  end.

Definition Assertion := State -> Prop.
Definition sat (s: State) (A: Assertion): Prop := A s.

Definition valid (A: Assertion) (c: Com) (B: Assertion) :=
  forall s, sat s A -> forall s', evC c s s' -> sat s' B.

Definition subst (A: Assertion) (X: Loc) (a: Aexpr): Assertion :=
  fun s => A (variant s X (evA a s)).

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

Theorem rule_if_is_valid A b C c1 c2:
  valid (Conj A b) c1 C ->
  valid (Conj A (bnot b)) c2 C ->
  valid A (If b c1 c2) C.
Proof.
  intros h1 h2. unfold valid. intros s hs s1 hs1.
  simpl evC in hs1.
  destruct (evB b s) eqn:heq.
  * unfold valid in h1. apply (h1 s).
    - unfold sat. unfold Conj. rewrite heq.
      exact (conj hs (eq_refl true)).
    - exact hs1.
  * unfold valid in h2. apply (h2 s).
    - unfold sat. unfold Conj.
      simpl evB. rewrite heq. simpl.
      exact (conj hs (eq_refl true)).
    - exact hs1.
Qed.

Theorem rule_while_is_valid A b c:
  valid (Conj A b) c A ->
  valid A (While b c) (Conj A (bnot b)).
Proof.
  intro h. unfold valid. intros s hs. intros s2 hs2.
  simpl evC in hs2. destruct hs2 as (N, hiter).
  revert s s2 hs hiter.
  induction N as [| N ih].
  * intros s s2 hs hiter. simpl iter in hiter.
    exfalso. exact hiter.
  * intros s s2 hs hiter. simpl iter in hiter.
    destruct (evB b s) eqn:heq.
    - destruct hiter as (s1, (h11, h12)).
      apply (ih s1 s2). clear ih.
      -- unfold valid in h. apply (h s). clear h.
         --- unfold sat. unfold Conj. exact (conj hs heq).
         --- exact h11.
      -- exact h12.
    - rewrite hiter. unfold sat. unfold Conj. split.
      -- exact hs.
      -- simpl evB. rewrite heq. simpl. reflexivity.
Qed.
