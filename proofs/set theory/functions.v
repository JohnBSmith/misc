
Definition ID := forall X: Type, X -> X.
Definition id: ID := fun X x => x.

Definition composition {X Y Z} (g: Y -> Z) (f: X -> Y)
  := fun x => g(f(x)).

Definition Injective {X Y} (f: X -> Y)
  := forall a b, f a = f b -> a = b.

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

Theorem left_inverse (X Y: Type) (f: X -> Y):
  (exists g, composition g f = id X) -> Injective f.
Proof.
  unfold composition.
  unfold Injective.
  intro h.
  intros a b eq.
  destruct h as (g, p).
  apply (f_equal g) in eq.
  replace (g (f a)) with a in eq.
  replace (g (f b)) with b in eq.
  apply eq.
Admitted.

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
