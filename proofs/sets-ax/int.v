
Require Import Coq.Unicode.Utf8.
Require Import axioms.
Require Import basic.
Require Import mappings.
Require nat.

Definition int_eq x y x' y' :=
  nat.add x y' = nat.add x' y.

Definition int_class x y :=
  {t | ∃x' y', x' ∈ ℕ ∧ y' ∈ ℕ ∧
    t = (x', y') ∧ int_eq x y x' y'}.

Definition ℤ :=
  {z | ∃x y, x ∈ ℕ ∧ y ∈ ℕ ∧ z = int_class x y}.

Definition add a b :=
  iota (fun c => ∃x y x' y', (x, y) ∈ a ∧ (x', y') ∈ b ∧
    c = int_class (nat.add x x') (nat.add y y')).

Theorem int_class_refl {x y}:
  x ∈ ℕ → y ∈ ℕ → (x, y) ∈ int_class x y.
Proof.
  intros hx hy. apply comp. split.
  * apply pair_is_set. split.
    - exact (set_intro hx).
    - exact (set_intro hy).
  * exists x. exists y.
    split; [| split; [| split]].
    - exact hx.
    - exact hy.
    - reflexivity.
    - unfold int_eq. reflexivity.
Qed.

Theorem int_eq_from_class {a b x y}:
  (a, b) ∈ int_class x y → int_eq a b x y.
Proof.
  intro h. apply comp_elim in h.
  destruct h as (a', (b', (ha, (hb, (hab, h))))).
  symmetry in hab.
  apply (pair_eq_from ha hb) in hab as (h1, h2).
  rewrite h1 in h. rewrite h2 in h.
  unfold int_eq in h. unfold int_eq.
  symmetry. exact h.
Qed.

Theorem nat_from_class {a b x y}:
  (a, b) ∈ int_class x y → a ∈ ℕ ∧ b ∈ ℕ.
Proof.
  intro h. apply comp_elim in h.
  destruct h as (a', (b', (ha, (hb, (heq, _))))).
  symmetry in heq.
  apply (pair_eq_from ha hb) in heq as (h1, h2).
  rewrite h1 in ha. rewrite h2 in hb.
  exact (conj ha hb).
Qed.

Theorem in_class_from_int_eq {a b x y}:
  a ∈ ℕ → b ∈ ℕ →
  int_eq a b x y → (a, b) ∈ int_class x y.
Proof.
  intros ha hb h. apply comp. split.
  * apply pair_is_set. split.
    - exact (set_intro ha).
    - exact (set_intro hb).
  * exists a. exists b.
    split; [| split; [| split]].
    - exact ha.
    - exact hb.
    - reflexivity.
    - unfold int_eq. unfold int_eq in h.
      symmetry. exact h.
Qed.

Theorem int_eq_sym {x y x' y'}:
  int_eq x y x' y' → int_eq x' y' x y.
Proof.
  unfold int_eq. intro h. symmetry. exact h.
Qed.

Theorem int_eq_trans {x y a b x' y'}:
  x ∈ ℕ → y ∈ ℕ → a ∈ ℕ → b ∈ ℕ → x' ∈ ℕ → y' ∈ ℕ →
  int_eq x y a b → int_eq a b x' y' →
  int_eq x y x' y'.
Proof.
  intros hx hy ha hb hx' hy'.
  unfold int_eq. intros h1 h2.
  apply (f_equal (fun t => nat.add t y')) in h1.
  rewrite (nat.add_assoc ha hy hy') in h1.
  rewrite (nat.add_comm hy hy') in h1.
  rewrite <- (nat.add_assoc ha hy' hy) in h1.
  rewrite h2 in h1. clear h2.
  rewrite (nat.add_assoc hx hb hy') in h1.
  rewrite (nat.add_comm hb hy') in h1.
  rewrite <- (nat.add_assoc hx hy' hb) in h1.
  rewrite (nat.add_assoc hx' hb hy) in h1.
  rewrite (nat.add_comm hb hy) in h1.
  rewrite <- (nat.add_assoc hx' hy hb) in h1.
  assert (hxy' := nat.add_in_nat hx hy').
  assert (hx'y := nat.add_in_nat hx' hy).
  exact (nat.add_cancel_r hxy' hx'y hb h1).
Qed.

Theorem class_eq {x y x' y'}:
  x ∈ ℕ → y ∈ ℕ → x' ∈ ℕ → y' ∈ ℕ →
  int_eq x y x' y' → int_class x y = int_class x' y'.
Proof.
  intros hx hy hx' hy'.
  intro h. apply ext. intro u. split.
  * intro hu. apply comp_elim in hu.
    destruct hu as (a, (b, (ha, (hb, (hu, heq))))).
    rewrite hu. clear hu.
    apply in_class_from_int_eq.
    - exact ha.
    - exact hb.
    - apply int_eq_sym in h.
      apply (int_eq_trans hx' hy' hx hy ha hb h) in heq.
      apply int_eq_sym in heq. exact heq.
  * intro hu. apply comp_elim in hu.
    destruct hu as (a, (b, (ha, (hb, (hu, heq))))).
    rewrite hu. clear hu.
    apply in_class_from_int_eq.
    - exact ha.
    - exact hb.
    - apply (int_eq_trans hx hy hx' hy' ha hb h) in heq.
      apply int_eq_sym in heq. exact heq.
Qed.

Theorem add_is_well_defined z1 z2: z1 ∈ ℤ → z2 ∈ ℤ →
  ∃!c, ∃x y x' y', (x, y) ∈ z1 ∧ (x', y') ∈ z2 ∧
    c = int_class (nat.add x x') (nat.add y y').
Proof.
  intros hz1 hz2. apply ex_uniq_equi2.
  apply comp_elim in hz1.
  apply comp_elim in hz2.
  destruct hz1 as (x, (y, (hx, (hy, hxy)))).
  destruct hz2 as (x', (y', (hx', (hy', hxy')))).
  pose (c := int_class (nat.add x x') (nat.add y y')).
  exists c. split.
  * exists x. exists y. exists x'. exists y'.
    split; [| split].
    - rewrite hxy. exact (int_class_refl hx hy).
    - rewrite hxy'. exact (int_class_refl hx' hy').
    - reflexivity.
  * intros c2 (a, (b, (a', (b', (hab, (hab', heq)))))).
    rewrite hxy in hab. clear hxy.
    rewrite hxy' in hab'. clear hxy'.
    assert (h := nat_from_class hab).
    destruct h as (ha, hb).
    assert (h := nat_from_class hab').
    destruct h as (ha', hb').
    apply int_eq_from_class in hab.
    apply int_eq_from_class in hab'.
    unfold c. rewrite heq. clear c c2 heq.
    assert (hxx' := nat.add_in_nat hx hx').
    assert (hyy' := nat.add_in_nat hy hy').
    assert (haa' := nat.add_in_nat ha ha').
    assert (hbb' := nat.add_in_nat hb hb').
    apply (class_eq hxx' hyy' haa' hbb').
    unfold int_eq.
    unfold int_eq in hab.
    unfold int_eq in hab'.
    rewrite <- (nat.add_assoc hxx' hb hb').
    rewrite (nat.add_comm hxx' hb).
    rewrite <- (nat.add_assoc hb hx hx').
    rewrite (nat.add_comm hb hx).
    rewrite (nat.add_assoc
      (nat.add_in_nat hx hb) hx' hb').
    rewrite <- hab. clear hab.
    rewrite <- hab'. clear hab'.
    rewrite <- (nat.add_assoc
      (nat.add_in_nat ha hy) ha' hy').
    rewrite (nat.add_assoc ha hy ha').
    rewrite (nat.add_comm hy ha').
    rewrite <- (nat.add_assoc ha ha' hy).
    rewrite (nat.add_assoc haa' hy hy').
    reflexivity. 
Qed.
