
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

Inductive Term :=
| tint (n: Z)
| tloc (i: Loc)
| tadd (t1 t2: Term)
| tsub (t1 t2: Term)
| tmul (t1 t2: Term).

Inductive Formula :=
| Verum
| Falsum
| EQ (t1 t2: Term)
| LE (t1 t2: Term)
| Neg (b: Formula)
| Conj (A B: Formula)
| Disj (A B: Formula).

Fixpoint val (s: State) (t: Term): Z :=
  match t with
  | tint n => n
  | tloc i => s i
  | tadd t1 t2 => val s t1 + val s t2
  | tsub t1 t2 => val s t1 - val s t2
  | tmul t1 t2 => val s t1 * val s t2
  end.

Fixpoint sat (s: State) (A: Formula): bool :=
  match A with
  | Verum => true
  | Falsum => false
  | EQ t1 t2 => Z.eqb (val s t1) (val s t2)
  | LE t1 t2 => Z.leb (val s t1) (val s t2)
  | Neg A => negb (sat s A)
  | Conj A B => andb (sat s A) (sat s B)
  | Disj A B => orb (sat s A) (sat s B)
  end.

Definition valid (A: Formula) (c: Com) (B: Formula) :=
  forall s, sat s A = true ->
    forall s', evC c s s' -> sat s' B = true.

Fixpoint as_term (a: Aexpr): Term :=
  match a with
  | int n => tint n
  | loc i => tloc i
  | add a1 a2 => tadd (as_term a1) (as_term a2)
  | sub a1 a2 => tsub (as_term a1) (as_term a2)
  | mul a1 a2 => tmul (as_term a1) (as_term a2)
  end.

Fixpoint as_form (b: Bexpr): Formula :=
  match b with
  | btrue => Verum
  | bfalse => Falsum
  | beq t1 t2 => EQ (as_term t1) (as_term t2)
  | ble t1 t2 => LE (as_term t1) (as_term t2)
  | bnot b => Neg (as_form b)
  | band b1 b2 => Conj (as_form b1) (as_form b2)
  | bor b1 b2 => Disj (as_form b1) (as_form b2)
  end.

Fixpoint term_subst (t: Term) (X: Loc) (a: Aexpr): Term :=
  match t with
  | tint n => tint n
  | tloc Y => if Nat.eqb X Y then (as_term a) else tloc Y
  | tadd t1 t2 => tadd (term_subst t1 X a) (term_subst t2 X a)
  | tsub t1 t2 => tsub (term_subst t1 X a) (term_subst t2 X a)
  | tmul t1 t2 => tmul (term_subst t1 X a) (term_subst t2 X a)
  end.

Fixpoint subst (A: Formula) (X: Loc) (a: Aexpr): Formula :=
  match A with
  | Verum => Verum
  | Falsum => Falsum
  | EQ t1 t2 => EQ (term_subst t1 X a) (term_subst t2 X a)
  | LE t1 t2 => LE (term_subst t1 X a) (term_subst t2 X a)
  | Neg A => Neg (subst A X a)
  | Conj A B => Conj (subst A X a) (subst B X a)
  | Disj A B => Disj (subst A X a) (subst B X a)
  end.

Theorem val_eq_evA s a:
  val s (as_term a) = evA a s.
Proof.
  induction a as [| X | a1 ih1 a2 ih2 | a1 ih1 a2 ih2 | a1 ih1 a2 ih2].
  * simpl val. simpl evA. reflexivity.
  * simpl val. simpl evA. reflexivity.
  * simpl val. simpl evA. rewrite ih1. rewrite ih2.
    reflexivity.
  * simpl val. simpl evA. rewrite ih1. rewrite ih2.
    reflexivity.
  * simpl val. simpl evA. rewrite ih1. rewrite ih2.
    reflexivity.
Qed.

Theorem substitution_lemma_val s t X a:
  val s (term_subst t X a) = val (reassign s X (evA a s)) t.
Proof.
  induction t as [| Y | t1 ih1 t2 ih2 | t1 ih1 t2 ih2| t1 ih1 t2 ih2].
  * simpl val. reflexivity.
  * simpl val. unfold reassign.
    destruct (Nat.eqb X Y).
    - apply val_eq_evA.
    - simpl val. reflexivity.
  * simpl val. rewrite ih1. rewrite ih2. reflexivity.
  * simpl val. rewrite ih1. rewrite ih2. reflexivity.
  * simpl val. rewrite ih1. rewrite ih2. reflexivity.
Qed.

Theorem substitution_lemma s A X a:
  sat s (subst A X a) = sat (reassign s X (evA a s)) A.
Proof.
  induction A as [| | t1 t2 | t1 t2 | A ih | A ihA B ihB | A ihA B ihB].
  * simpl sat. reflexivity.
  * simpl sat. reflexivity.
  * simpl sat.
    rewrite (substitution_lemma_val s t1 X a).
    rewrite (substitution_lemma_val s t2 X a).
    reflexivity.
  * simpl sat.
    rewrite (substitution_lemma_val s t1 X a).
    rewrite (substitution_lemma_val s t2 X a).
    reflexivity.
  * simpl sat. rewrite ih. reflexivity.
  * simpl sat. rewrite ihA. rewrite ihB. reflexivity.
  * simpl sat. rewrite ihA. rewrite ihB. reflexivity.
Qed.

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
  rewrite (substitution_lemma s A X a) in hs.
  rewrite <- hs1 in hs. exact hs.
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

Theorem sat_eq_evB s b:
  sat s (as_form b) = evB b s.
Proof.
  induction b as [| | a1 a2 | a1 a2 | A ih | A ihA B ihB | A ihA B ihB].
  * simpl sat. simpl evB. reflexivity.
  * simpl sat. simpl evB. reflexivity.
  * simpl sat. simpl evB.
    rewrite (val_eq_evA s a1). rewrite (val_eq_evA s a2).
    reflexivity.
  * simpl sat. simpl evB.
    rewrite (val_eq_evA s a1). rewrite (val_eq_evA s a2).
    reflexivity.
  * simpl sat. simpl evB. rewrite ih. reflexivity.
  * simpl sat. simpl evB. rewrite ihA. rewrite ihB.
    reflexivity.
  * simpl sat. simpl evB. rewrite ihA. rewrite ihB.
    reflexivity.
Qed.

Theorem rule_if_is_valid A b C c1 c2:
  valid (Conj A (as_form b)) c1 C ->
  valid (Conj A (Neg (as_form b))) c2 C ->
  valid A (If b c1 c2) C.
Proof.
  intros h1 h2. unfold valid. intros s hs. intros s1 hs1.
  simpl evC in hs1.
  assert (heq := sat_eq_evB s b).
  destruct (evB b s).
  - unfold valid in h1. simpl sat in h1. apply (h1 s).
    -- rewrite hs. rewrite heq. simpl. reflexivity.
    -- exact hs1.
  - unfold valid in h2. simpl sat in h2. apply (h2 s).
    -- rewrite hs. rewrite heq. simpl. reflexivity.
    -- exact hs1.
Qed.

Definition invariant ev A b := forall s s',
  sat s A = true /\ evB b s = true -> ev s s' -> sat s' A = true.

Theorem iter_lemma (ev: State -> State -> Prop) N b A:
  invariant ev A b ->
  (forall s s', sat s A = true -> iter ev N b s s' ->
    sat s' A = true /\ evB b s' = false).
Proof.
  intro h.
  induction N as [| N ih].
  * intros s s1. intros hsA hiter.
    simpl iter in hiter. exfalso. exact hiter.
  * intros s s1. intros hsA hiter.
    simpl iter in hiter.
    assert (heq := sat_eq_evB s b).
    destruct (evB b s).
    - destruct hiter as (s0, (h00, h01)).
      rewrite (sat_eq_evB s b) in heq.
      assert (h := h s s0 (conj hsA heq) h00).
      apply (ih s0 s1 h). exact h01.
    - rewrite hiter. split.
      -- exact hsA.
      -- rewrite (sat_eq_evB s b) in heq. exact heq.
Qed.

Theorem rule_while_is_valid A b c:
  valid (Conj A (as_form b)) c A ->
  valid A (While b c) (Conj A (Neg (as_form b))).
Proof.
  intro h. unfold valid. intros s hs. intros s2 hs2.
  simpl evC in hs2. destruct hs2 as (N, hiter).
  simpl sat. apply andb_true_iff.
  assert (h0: invariant (evC c) A b). {
    unfold invariant.
    intros s0 s1. intros (hs0A, hs0b) h01. unfold valid in h.
    apply (h s0).
    * simpl sat. apply andb_true_iff. split.
      - exact hs0A.
      - rewrite (sat_eq_evB s0 b). exact hs0b.
    * exact h01.
  }
  assert (h1 := iter_lemma (evC c) N b A h0 s s2 hs hiter).
  destruct h1 as (hs2A, hbs2).
  split.
  * exact hs2A.
  * rewrite (sat_eq_evB s2 b). rewrite hbs2.
    simpl. reflexivity.
Qed.

