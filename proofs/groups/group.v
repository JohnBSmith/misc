
Record Group := {
  G: Type;
  e: G;
  mul: G -> G -> G;
  assoc: forall a b c, mul a (mul b c) = mul (mul a b) c;
  neutl: forall a, mul e a = a;
  neutr: forall a, mul a e = a;
  invl: forall a, exists b, mul b a = e;
  invr: forall a, exists b, mul a b = e;
}.

Theorem inv_is_uniq (G: Group):
  forall g a b, G.(mul) a g = G.(e) /\ G.(mul) g b = G.(e)
    -> a = b.
Proof.
  intros g a b.
  intros (ha, hb).
  rewrite <- (G.(neutr) a).
  rewrite <- hb.
  rewrite G.(assoc).
  rewrite ha.
  rewrite G.(neutl).
  exact (eq_refl b).
Qed.
