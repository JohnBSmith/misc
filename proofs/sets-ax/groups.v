
Require Import Coq.Unicode.Utf8.
Require Import axioms.
Require Import relations.
Require Import mappings.

Definition neut G mul :=
  ⋂{x | x ∈ G ∧ ∀a, a ∈ G → mul x a = a ∧ mul a x = a}.

Definition inv G (mul: Class → Class → Class) a
  := let e := neut G mul in
    ⋂{b | b ∈ G ∧ mul b a = e ∧ mul a b = e}.

Record group G mul := {
  group_closed: ∀a b, a ∈ G → b ∈ G → mul a b ∈ G;
  group_assoc: ∀a b c, a ∈ G → b ∈ G → c ∈ G →
    mul (mul a b) c = mul a (mul b c);
  group_neut: ∃e, e ∈ G ∧ ∀a, a ∈ G →
    mul e a = a ∧ mul a e = a;
  group_inv: ∀a, a ∈ G → ∃b, b ∈ G ∧
    mul b a = neut G mul ∧ mul a b = neut G mul;
}.

Record group_explicit G mul e := {
  group_expl_closed: ∀a b, a ∈ G → b ∈ G → mul a b ∈ G;
  group_expl_assoc: ∀a b c, a ∈ G → b ∈ G → c ∈ G →
    mul (mul a b) c = mul a (mul b c);
  group_expl_neut: e ∈ G ∧ ∀a, a ∈ G →
    mul e a = a ∧ mul a e = a;
  group_expl_inv: ∀a, a ∈ G → ∃b, b ∈ G ∧
    mul b a = e ∧ mul a b = e;
}.

Definition subgroup mul H G :=
  H ⊆ G ∧ group H mul.

Lemma assoc {G mul a b c}:
  group G mul → a ∈ G → b ∈ G → c ∈ G →
    mul (mul a b) c = mul a (mul b c).
Proof.
  intro h. exact (group_assoc G mul h a b c).
Qed.

Theorem neutral_element_uniq G mul:
  group G mul → ∃!e, e ∈ G ∧ ∀a, a ∈ G →
    mul e a = a ∧ mul a e = a.
Proof.
  intro hG. unfold ex_uniq. split.
  * assert (h := group_neut G mul hG).
    destruct h as (e, (he, hneut)).
    exists e. split.
    - exact (set_intro he).
    - exact (conj he hneut).
  * intros e e' ((he, h), (he', h')).
    assert (h1 := proj2 (h' e he)).
    assert (h2 := proj1 (h e' he')).
    rewrite <- h1. rewrite h2.
    reflexivity.
Qed.

Lemma neutl {G mul a}:
  group G mul → a ∈ G → mul (neut G mul) a = a.
Proof.
  intros hG ha.
  set (e := neut G mul). assert (he := eq_refl e).
  unfold e in he at 2. unfold neut in he.
  assert (huniq := neutral_element_uniq G mul hG).
  assert (h := iota_property e huniq he).
  simpl in h. clear he huniq. apply proj2 in h.
  apply h in ha. exact (proj1 ha).
Qed.

Lemma neutr {G mul a}:
  group G mul → a ∈ G → mul a (neut G mul) = a.
Proof.
  intros hG ha.
  set (e := neut G mul). assert (he := eq_refl e).
  unfold e in he at 2. unfold neut in he.
  assert (huniq := neutral_element_uniq G mul hG).
  assert (h := iota_property e huniq he).
  simpl in h. clear he huniq. apply proj2 in h.
  apply h in ha. exact (proj2 ha).
Qed.

Theorem inv_uniq {G mul a}:
  group G mul → a ∈ G → ∃!b, b ∈ G ∧
    mul b a = neut G mul ∧ mul a b = neut G mul.
Proof.
  intros hG ha. set (e := neut G mul).
  unfold ex_uniq. split.
  * assert (hex := group_inv G mul hG a ha).
    destruct hex as (b, (hb, hinv)).
    exists b. split.
    - exact (set_intro hb).
    - split.
      -- exact hb.
      -- exact hinv.
  * intros b b' ((hb, h), (hb', h')).
    rewrite <- (neutr hG hb). fold e.
    rewrite <- (proj2 h').
    rewrite <- (assoc hG hb ha hb').
    rewrite (proj1 h). unfold e.
    rewrite (neutl hG hb').
    reflexivity.
Qed.

Theorem invlr {G mul a}: group G mul → a ∈ G →
  mul (inv G mul a) a = neut G mul ∧
  mul a (inv G mul a) = neut G mul.
Proof.
  intros hG ha.
  set (b := inv G mul a). assert (hb := eq_refl b).
  unfold b in hb at 2. unfold inv in hb.
  assert (huniq := inv_uniq hG ha).
  assert (h := iota_property b huniq hb).
  simpl in h. clear hb huniq. apply proj2 in h.
  exact h.
Qed.

Theorem invl {G mul a}: group G mul → a ∈ G →
  mul (inv G mul a) a = neut G mul.
Proof.
  intros hG ha. exact (proj1 (invlr hG ha)).
Qed.

Theorem invr {G mul a}: group G mul → a ∈ G →
  mul a (inv G mul a) = neut G mul.
Proof.
  intros hG ha. exact (proj2 (invlr hG ha)).
Qed.

Theorem group_from_explicit {G mul} e:
  group_explicit G mul e → group G mul.
Proof.
  intros (hclosed, hassoc, hneut, hinv).
  assert (he := proj1 hneut).
  assert (hex_uniq: ∃!e, e ∈ G ∧
    ∀a, a ∈ G → mul e a = a ∧ mul a e = a).
  {
    unfold ex_uniq. split.
    * exists e. split.
      - exact (set_intro he).
      - exact hneut.
    * intros x x' ((hx, h), (hx', h')).
      rewrite <- (proj1 (h x' hx')).
      rewrite (proj2 (h' x hx)).
      reflexivity.
  }
  assert (heq := iota_property_rev e hex_uniq hneut).
  simpl in heq. fold (neut G mul) in heq.
  split.
  * exact hclosed.
  * exact hassoc.
  * exists e. exact hneut.
  * rewrite <- heq. exact hinv.
Qed.

Theorem subclass_neut {H G mul}:
  group G mul → H ⊆ G → neut G mul ∈ H →
  neut G mul = neut H mul.
Proof.
  set (e := neut G mul).
  intros hG hHG he. apply ext. intro u.
  split.
  * intro hu. apply comp. split.
    - exact (set_intro hu).
    - intros e' he'. apply comp_elim in he'.
      destruct he' as (he', h).
      assert (h1 := neutl hG (hHG e' he')).
      fold e in h1.
      assert (h2 := proj2 (h e he)).
      rewrite <- h1. rewrite h2.
      exact hu.
  * intro hu. apply comp_elim in hu.
    apply hu. clear hu. apply comp. split.
    - exact (set_intro he). 
    - split.
      -- exact he.
      -- intros a ha. split.
         --- exact (neutl hG (hHG a ha)).
         --- exact (neutr hG (hHG a ha)).
Qed.

Theorem subgroup_test H G mul:
  group G mul → H ⊆ G → H ≠ ∅ →
  (∀a b, a ∈ H → b ∈ H → mul a b ∈ H) →
  (∀a, a ∈ H → inv G mul a ∈ H) →
  subgroup mul H G.
Proof.
  intro hG. intros hHG hH. intros hclosed hinv.
  pose (e := neut G mul).
  assert (he: e ∈ H). {
    apply non_empty_class in hH.
    destruct hH as (x, hx).
    pose (y := inv G mul x).
    assert (hy := hinv x hx). fold y in hy.
    assert (hxy := hclosed x y hx hy).
    unfold y in hxy.
    rewrite (invr hG (hHG x hx)) in hxy.
    fold e in hxy. exact hxy.
  }
  unfold subgroup. split.
  * exact hHG.
  * apply (group_from_explicit e). split.
    - exact hclosed.
    - intros a b c ha hb hc.
      apply hHG in ha. apply hHG in hb. apply hHG in hc.
      exact (assoc hG ha hb hc).
    - split.
      -- exact he.
      -- intros a ha. apply hHG in ha. split.
         --- exact (neutl hG ha).
         --- exact (neutr hG ha).
    - intros a ha. clear hclosed.
      pose (b := inv G mul a).
      assert (hab := invlr hG (hHG a ha)).
      fold b in hab. fold e in hab.
      exists b.
      assert (hb := hinv a ha). fold b in hb.
      split.
      -- exact hb.
      -- exact hab.
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
  set X → group (Sym X) composition.
Proof.
  intro hsX.
  apply (group_from_explicit (id X)).
  split.
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
  * intros f hf. exists (axioms.inv f).
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
