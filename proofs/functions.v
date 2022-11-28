
Definition Injective {X Y} (f: X -> Y)
  := forall a b, f a = f b -> a = b.

Definition composition {X Y Z} (g: Y -> Z) (f: X -> Y)
  := fun x => g(f(x)).

Theorem comp_inj (X Y Z: Type) (f: X -> Y) (g: Y -> Z):
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

Definition Surjective {X Y} (f: X -> Y)
  := forall y, exists x, f x = y.

Theorem comp_sur (X Y Z: Type) (f: X -> Y) (g: Y -> Z):
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
