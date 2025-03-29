
(* Eine kurze Studie zum Rätsel »Wolf, Ziege und Kohlkopf«,
 * engl. »Wolf, goat, and cabbage problem«, ein Flussüber-
 * querungsrätsel, engl. River crossing puzzle
 * =============================================================
 * Ein Bauer mit einem Kohlkopf, einem Wolf und einer Ziege muss
 * mit einem Boot einen Fluss überqueren. Das Boot vermag nur
 * den Bauern und einen einzigen Gegenstand zu transportieren.
 * Wenn sie zusammen unbeaufsichtigt blieben, würde der Wolf
 * die Ziege fressen, oder die Ziege den Kohl. Wie können sie
 * den Fluss überqueren, ohne dass etwas gefressen wird? *)

Require Import Bool.Bool.

Inductive Loc := L0 | L1. (* Vor oder hinter der Querung *)
Inductive Object := B | K | W | Z.
Definition State: Type := Loc * Loc * Loc * Loc.
  (* Bauer, Kohl, Wolf, Ziege *)

Definition eqb (x y: Loc): bool :=
  match x with
  | L0 => match y with L0 => true | L1 => false end
  | L1 => match y with L1 => true | L0 => false end
  end.

Definition opposite (x: Loc): Loc :=
  match x with L0 => L1 | L1 => L0 end.

Definition proj (s: State) (A: Object) :=
  match A with
  | B => match s with (b, k, w, z) => b end
  | K => match s with (b, k, w, z) => k end
  | W => match s with (b, k, w, z) => w end
  | Z => match s with (b, k, w, z) => z end
  end.

(* Der Zustand s erfüllt »A befindet sich in x« *)
Definition sat (s: State) (A: Object) (x: Loc): bool :=
  eqb (proj s A) x.

Inductive Program :=
| transit (A: Object) (x: Loc)
| sec (p: Program) (q: Program).

Fixpoint eval (p: Program) (s: State) :=
  match p with
  | transit A y => let x := opposite y in
      if sat s B x && sat s A x then
        match A with
        | K => (y, y, proj s W, proj s Z)
        | W => (y, proj s K, y, proj s Z)
        | Z => (y, proj s K, proj s W, y)
        | B => (y, proj s K, proj s W, proj s Z)
        end
      else s
  | sec p q => eval q (eval p s)
  end.

Definition all (P: Loc -> bool) := P L0 && P L1.

(* Die Invarianten *)
Definition I1 s := all (fun x => all (fun y =>
  negb (sat s W x && sat s Z x && sat s B y) || eqb x y)).

Definition I2 s := all (fun x => all (fun y =>
  negb (sat s Z x && sat s K x && sat s B y) || eqb x y)).

Fixpoint valid (p: Program) (s: State): bool :=
  match p with
  | transit A y => let s' := eval (transit A y) s in
      negb (I1 s && I2 s) || I1 s' && I2 s'
  | sec p q => valid p s && valid q (eval p s)
  end.

Notation "p ; q" := (sec p q) (at level 40).
Definition s0 := (L0, L0, L0, L0).
Definition s1 := (L1, L1, L1, L1).

Definition p1 :=
  transit Z L1; (* Die Ziege überführen *)
  transit B L0; (* Mit leeren Händen zurückkommen *)
  transit W L1; (* Den Wolf überführen *)
  transit Z L0; (* Mit der Ziege zurückkehren *)
  transit K L1; (* Den Kohl überführen *)
  transit B L0; (* Mit leeren Händen zurückkehren *)
  transit Z L1. (* Die Ziege überführen *)

Goal valid p1 s0 = true /\ eval p1 s0 = s1.
Proof.
  split; reflexivity.
Qed.
