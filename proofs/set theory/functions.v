
Require Import Coq.Logic.FunctionalExtensionality.

Definition ID := forall X: Type, X -> X.
Definition id: ID := fun X x => x.

Definition composition {X Y Z: Type} (g: Y -> Z) (f: X -> Y)
  := fun x => g(f(x)).

Definition Injective {X Y: Type} (f: X -> Y)
  := forall a b, f a = f b -> a = b.

Definition DecideableImage {X Y: Type} (f: X -> Y)
  := forall y, {x & f x = y} + ~(exists x, f x = y).

Definition NonEmpty (X: Type) := (exists x: X, True).

Theorem composition_inj (X Y Z: Type) (f: X -> Y) (g: Y -> Z):
  Injective f /\ Injective g -> Injective (composition g f).
Proof.
  unfold Injective.
  unfold composition.
  intro h. destruct h as (hf, hg).
  intros a b.
  intro he.
  apply hf.
  apply hg.
  exact he.
Qed.

Theorem left_inverse_implies_inj (X Y: Type) (f: X -> Y):
  (exists g, composition g f = id X) -> Injective f.
Proof.
  unfold composition.
  unfold Injective.
  intro h.
  intros a b eq.
  destruct h as (g, p).
  apply (f_equal g) in eq.
  unfold id in p.
  assert (pa := f_equal (fun phi => phi a) p).
  assert (pb := f_equal (fun phi => phi b) p).
  simpl in pa. simpl in pb.
  apply eq_sym in pa.
  exact (eq_trans (eq_trans pa eq) pb).
Qed.

Theorem inj_implies_left_inverse (X Y: Type) (f: X -> Y)
  (w: NonEmpty X) (dec: DecideableImage f):
  Injective f -> (exists g, composition g f = id X).
Proof.
  intro injf.
  destruct w as (x0, _).
  exists (fun y =>
    match (dec y) with
    | inl (existT _ x _) => x
    | inr _ => x0
    end).
  unfold composition.
  unfold id.
  unfold Injective in injf.
  apply functional_extensionality.
  intro x.
  destruct (dec (f x)) as [hl | hr].
  * destruct hl as (a, p). apply injf in p. exact p.
  * exfalso. apply hr. exists x. exact (eq_refl (f x)). 
Qed.

Definition Surjective {X Y: Type} (f: X -> Y)
  := forall y, exists x, f x = y.

Definition SurjectiveChoice {X Y: Type} (f: X -> Y)
  := forall y, {x & f x = y}.

Theorem composition_sur (X Y Z: Type) (f: X -> Y) (g: Y -> Z):
  Surjective f /\ Surjective g -> Surjective (composition g f).
Proof.
  unfold Surjective.
  unfold composition.
  intro h. destruct h as (hf, hg).
  intro y.
  destruct (hg y) as (u, pg).
  destruct (hf u) as (x, pf).
  exists x.
  rewrite pf.
  rewrite pg.
  reflexivity.
Qed.

Theorem right_inverse_implies_sur (X Y: Type) (f: X -> Y):
  (exists g, composition f g = id Y) -> Surjective f.
Proof.
  unfold composition. unfold id.
  intro h. destruct h as (g, e).
  unfold Surjective.
  intro y.
  apply (f_equal (fun phi => phi y)) in e.
  exists (g y).
  exact e.
Qed.

Theorem sur_implies_right_inverse (X Y: Type) (f: X -> Y):
  SurjectiveChoice f -> exists g, composition f g = id Y.
Proof.
  intro h.
  unfold SurjectiveChoice in h.
  exists (fun y => match (h y) with existT _ x _ => x end).
  unfold composition.
  unfold id.
  apply functional_extensionality.
  intro y.
  destruct (h y) as (x, p).
  exact p.
Qed.

