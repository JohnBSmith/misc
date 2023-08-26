
Require Import Coq.Unicode.Utf8.
Require Import axioms.
Require Import relations.
Require Import mappings.

Definition group_closed G mul :=
  ∀a b, a ∈ G → b ∈ G → mul a b ∈ G.

Definition group_assoc G mul :=
  ∀a b c, a ∈ G → b ∈ G → c ∈ G →
  mul (mul a b) c = mul a (mul b c).

Definition group_neut G mul e :=
  e ∈ G ∧ ∀a, a ∈ G →
  mul e a = a ∧ mul a e = a.

Definition group_inv G mul (e: Class) inv :=
  ∀a, a ∈ G → inv a ∈ G ∧
  mul (inv a) a = e ∧ mul a (inv a) = e.

Definition group G mul e inv :=
  group_closed G mul ∧
  group_assoc G mul ∧
  group_neut G mul e ∧
  group_inv G mul e inv.

Definition subgroup H G mul e inv :=
  H ⊆ G ∧ group H mul e inv.

Definition hom f := fun G mulG H mulH =>
  (∀a, a ∈ G → f a ∈ H) ∧
  (∀a b, a ∈ G → b ∈ G → f (mulG a b) = mulH (f a) (f b)).

Definition ker (f: Class → Class) G eH :=
  {g | g ∈ G ∧ f g = eH}.

Definition img f G :=
  {h | ∃g, g ∈ G ∧ h = f g}.

Lemma closed {G mul e inv a b}:
  group G mul e inv → a ∈ G → b ∈ G → mul a b ∈ G.
Proof.
  intro h. destruct h as (h, _).
  unfold group_closed in h.
  exact (h a b).
Qed.

Lemma assoc {G mul e inv a b c}:
  group G mul e inv → a ∈ G → b ∈ G → c ∈ G →
    mul (mul a b) c = mul a (mul b c).
Proof.
  intro h. destruct h as (_, (h, _)).
  unfold group_assoc in h.
  exact (h a b c).
Qed.

Lemma neut_in_group {G mul e inv}:
  group G mul e inv → e ∈ G.
Proof.
  intro hG. destruct hG as (_, (_, (h, _))).
  unfold group_neut in h. exact (proj1 h).
Qed.

Lemma neutl {G mul e inv a}:
  group G mul e inv → a ∈ G → mul e a = a.
Proof.
  intros hG ha. destruct hG as (_, (_, (h, _))).
  unfold group_neut in h. apply proj2 in h.
  exact (proj1 (h a ha)).
Qed.

Lemma neutr {G mul e inv a}:
  group G mul e inv → a ∈ G → mul a e = a.
Proof.
  intros hG ha. destruct hG as (_, (_, (h, _))).
  unfold group_neut in h. apply proj2 in h.
  exact (proj2 (h a ha)).
Qed.

Lemma invl {G mul e inv a}:
  group G mul e inv → a ∈ G →
  mul (inv a) a = e.
Proof.
  intros hG ha.
  destruct hG as (_, (_, (_, hinv))).
  unfold group_inv in hinv.
  exact (proj1 (proj2 (hinv a ha))).
Qed.

Lemma invr {G mul e inv a}:
  group G mul e inv → a ∈ G →
  mul a (inv a) = e.
Proof.
  intros hG ha.
  destruct hG as (_, (_, (_, hinv))).
  unfold group_inv in hinv.
  exact (proj2 (proj2 (hinv a ha))).
Qed.

Lemma inv_closed {G mul e inv a}:
  group G mul e inv → a ∈ G → inv a ∈ G.
Proof.
  intros hG ha. destruct hG as (_, (_, (_, hinv))).
  unfold group_inv in hinv.
  exact (proj1 (hinv a ha)).
Qed.

Theorem subgroup_test {H G mul e inv}:
  group G mul e inv → H ⊆ G → H ≠ ∅ →
  (∀a b, a ∈ H → b ∈ H → mul a b ∈ H) →
  (∀a, a ∈ H → inv a ∈ H) →
  subgroup H G mul e inv.
Proof.
  intro hG. intros hHG hH. intros hclosed hinv.
  assert (he: e ∈ H). {
    apply non_empty_class in hH.
    destruct hH as (x, hx).
    pose (y := inv x).
    assert (hy := hinv x hx). fold y in hy.
    assert (hxy := hclosed x y hx hy).
    unfold y in hxy.
    rewrite (invr hG (hHG x hx)) in hxy.
    exact hxy.
  }
  unfold subgroup. split.
  * exact hHG.
  * unfold group. split; [| split; [| split]].
    - exact hclosed.
    - intros a b c ha hb hc.
      apply hHG in ha. apply hHG in hb. apply hHG in hc.
      exact (assoc hG ha hb hc).
    - split.
      -- exact he.
      -- intros a ha. apply hHG in ha. split.
         --- exact (neutl hG ha).
         --- exact (neutr hG ha).
    - unfold group_inv.
      intros a ha. clear hclosed.
      repeat split.
      -- exact (hinv a ha).
      -- exact (invl hG (hHG a ha)).
      -- exact (invr hG (hHG a ha)).
Qed.

Definition Sym X := {f | mapping f X X ∧ bij X X f}.

Theorem id_in_symmetric_group {X}:
  set X → id X ∈ Sym X.
Proof.
  intro hsX. assert (hid := id_is_mapping X).
  apply comp. split.
  * exact (graph_is_set_from_dom_cod hid hsX hsX).
  * split.
    - exact hid.
    - exact (id_is_bijective X).
Qed.

Theorem symmetric_group_is_group X:
  set X → group (Sym X) composition (id X) inv.
Proof.
  intro hsX. split; [| split; [| split]].
  * intros g f hg hf.
    apply comp_elim in hf as (hf, hbf).
    apply comp_elim in hg as (hg, hbg).
    apply comp. split.
    - assert (h := composition_is_mapping hf hg).
      exact (graph_is_set_from_dom_cod h hsX hsX).
    - split.
      -- exact (composition_is_mapping hf hg).
      -- exact (composition_of_bijections hf hg hbf hbg).
  * intros h g f hh hg hf.
    apply comp_elim in hf as (hf, _).
    apply comp_elim in hg as (hg, _).
    apply comp_elim in hh as (hh, _).
    symmetry.
    exact (composition_assoc hf hg hh).
  * split.
    - exact (id_in_symmetric_group hsX).
    - intros f hf. apply comp_elim in hf as (hf, _).
      split.
      -- exact (id_is_left_neutral hf).
      -- exact (id_is_right_neutral hf).
  * intros f hf.
    apply comp_elim in hf as (hf, hbf).
    repeat split.
    - apply comp. split.
      -- apply proj_relation in hf.
         exact (inv_relation_is_set hf hsX hsX).
      -- split.
         --- exact (inv_of_bij_is_mapping hf hbf).
         --- exact (inv_of_bij_is_bij hf hbf).
    - rewrite (bij_invl hf hbf). reflexivity.
    - rewrite (bij_invr hf hbf). reflexivity.
Qed.

Theorem left_mul_inv {G mul e inv a b c}:
  group G mul e inv → a ∈ G → b ∈ G → c ∈ G →
  mul a b = c → b = mul (inv a) c.
Proof.
  intros hG ha hb hc h.
  assert (hai := inv_closed hG ha).
  apply (f_equal (fun x => mul (inv a) x)) in h.
  rewrite <- (assoc hG hai ha hb) in h.
  rewrite (invl hG ha) in h. rewrite (neutl hG hb) in h.
  exact h.
Qed.

Theorem prod_inv {G mul e inv a b}:
  group G mul e inv → a ∈ G → b ∈ G →
  inv (mul a b) = mul (inv b) (inv a).
Proof.
  intros hG ha hb.
  assert (hab := closed hG ha hb).
  assert (h := invr hG hab).
  assert (hiab := inv_closed hG hab).
  rewrite (assoc hG ha hb hiab) in h.
  assert (he := neut_in_group hG).
  assert (hbiab := closed hG hb hiab).
  apply (left_mul_inv hG ha hbiab he) in h.
  assert (hia := inv_closed hG ha).
  rewrite (neutr hG hia) in h.
  apply (left_mul_inv hG hb hiab hia) in h.
  exact h.
Qed.

Theorem inv_inv {G mul e inv a}:
  group G mul e inv → a ∈ G →
  inv (inv a) = a.
Proof.
  intros hG ha.
  assert (hia := inv_closed hG ha).
  assert (hiia := inv_closed hG hia).
  assert (h := invr hG hia).
  apply (f_equal (fun x => mul a x)) in h.
  assert (he := neut_in_group hG).
  rewrite <- (assoc hG ha hia hiia) in h.
  rewrite (invr hG ha) in h.
  rewrite (neutl hG hiia) in h.
  rewrite (neutr hG ha) in h.
  exact h.
Qed.

Theorem inv_neut {G mul e inv}:
  group G mul e inv → inv e = e.
Proof.
  intro hG.
  assert (he := neut_in_group hG).
  assert (hie := inv_closed hG he).
  assert (h := invl hG he).
  rewrite (neutr hG hie) in h.
  exact h.
Qed.

Theorem hom_neut {f G mulG eG invG H mulH eH invH}:
  group G mulG eG invG → group H mulH eH invH →
  hom f G mulG H mulH → f eG = eH.
Proof.
  intros hG hH hf. unfold hom in hf.
  destruct hf as (hfclosed, hf).
  assert (he := neut_in_group hG).
  assert (h := neutl hG he).
  apply (f_equal f) in h.
  rewrite (hf eG eG he he) in h. clear hf.
  assert (hfe := hfclosed eG he).
  apply (left_mul_inv hH hfe hfe hfe) in h.
  rewrite (invl hH hfe) in h.
  exact h.
Qed.

Theorem hom_inv {f g G mulG eG invG H mulH eH invH}:
  group G mulG eG invG → group H mulH eH invH →
  hom f G mulG H mulH → g ∈ G →
  f (invG g) = invH (f g).
Proof.
  intros hG hH hf hg.
  assert (h := invr hG hg).
  apply (f_equal f) in h.
  rewrite (hom_neut hG hH hf) in h.
  assert (hig := inv_closed hG hg).
  destruct hf as (hfclosed, hf).
  rewrite (hf g _ hg hig) in h. clear hf.
  assert (hfg := hfclosed g hg).
  assert (hfig := hfclosed _ hig).
  assert (he := neut_in_group hH).
  apply (left_mul_inv hH hfg hfig he) in h.
  clear he hg hig hfig hfclosed.
  assert (hifg := inv_closed hH hfg).
  rewrite (neutr hH hifg) in h.
  exact h.
Qed.

Theorem neut_in_ker {G mulG eG invG H mulH eH invH f}:
  group G mulG eG invG → group H mulH eH invH →
  hom f G mulG H mulH → eG ∈ ker f G eH.
Proof.
  intros hG hH hf. apply comp.
  assert (he := neut_in_group hG).
  repeat split.
  * exact (set_intro he).
  * exact he.
  * exact (hom_neut hG hH hf).
Qed.

Theorem ker_is_subgroup {G mulG eG invG H mulH eH invH f}:
  group G mulG eG invG → group H mulH eH invH →
  hom f G mulG H mulH →
  subgroup (ker f G eH) G mulG eG invG.
Proof.
  intros hG hH hf. apply (subgroup_test hG).
  * unfold subclass. intros g hg.
    apply comp_elim in hg. exact (proj1 hg).
  * intro h. apply subclass_from_eq in h.
    assert (he := neut_in_ker hG hH hf).
    apply h in he.
    exact (empty_set_property he).
  * intros a b ha hb.
    apply comp_elim in ha as (ha, hfa).
    apply comp_elim in hb as (hb, hfb).
    apply comp. repeat split.
    - assert (hab := closed hG ha hb).
      exact (set_intro hab).
    - exact (closed hG ha hb).
    - apply proj2 in hf.
      rewrite (hf a b ha hb). clear hf.
      rewrite hfa. rewrite hfb.
      exact (neutl hH (neut_in_group hH)).
  * intros g hg. apply comp_elim in hg as (hg, hfg).
    apply comp. assert (hig := inv_closed hG hg).
    repeat split.
    - exact (set_intro hig).
    - exact hig.
    - rewrite (hom_inv hG hH hf hg). rewrite hfg.
      rewrite (inv_neut hH). reflexivity.
Qed.
