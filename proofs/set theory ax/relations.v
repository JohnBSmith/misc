
Load "axioms.v".
Load "logic.v".

Definition Pair (x: set) (y: set) :=
  PairSet (PairSet x x) (PairSet x y).

Theorem singleton_eq_pair_set (x y: set):
  PairSet x x = PairSet x y → x = y.
Proof.
  intro h.
  assert (hy: y ∈ PairSet x y). {
    apply pair_set_axiom. right. reflexivity.
  }
  rewrite <- h in hy.
  apply pair_set_axiom in hy.
  apply disj_idem in hy.
  apply eq_sym. exact hy.
Qed.

Theorem pair_set_diff_singleton (x y: set):
  x ≠ y → (PairSet x y) \ (PairSet x x) = (PairSet y y).
Proof.
  intro hxy. apply set_ext. intro u. split.
  * intro h. apply pair_set_axiom. left.
    apply diff_elim in h.
    rewrite pair_set_axiom in h.
    rewrite pair_set_axiom in h.
    destruct h as (hl, hr).
    rewrite disj_idem_eq in hr.
    destruct hl as [hx | hy].
    - exfalso. exact (hr hx). 
    - exact hy.
  * intro h. apply pair_set_axiom in h.
    apply disj_idem in h.
    apply diff_intro. split.
    - apply pair_set_axiom. right. exact h.
    - intro hu. apply pair_set_axiom in hu.
      apply disj_idem in hu.
      rewrite hu in h. exact (hxy h).
Qed.

Theorem union_pair (x y: set):
  ⋃(Pair x y) = PairSet x y.
Proof.
  apply set_ext. intro u. split.
  * intro h. apply pair_set_axiom.
    apply union_axiom in h.
    destruct h as (A, (hu, hA)).
    unfold Pair in hA. apply pair_set_axiom in hA.
    destruct hA as [hx | hy].
    - rewrite hx in hu. apply pair_set_axiom in hu.
      apply disj_idem in hu. left. exact hu.
    - rewrite hy in hu. apply pair_set_axiom in hu.
      exact hu.
  * intro h. apply union_axiom.
    apply pair_set_axiom in h. destruct h as [hx | hy].
    - exists (PairSet x x). split.
      -- apply pair_set_axiom. left. exact hx.
      -- unfold Pair. apply pair_set_axiom.
         left. reflexivity.
    - exists (PairSet x y). split.
      -- apply pair_set_axiom. right. exact hy.
      -- unfold Pair. apply pair_set_axiom.
         right. reflexivity.
Qed.

Theorem intersection_pair (x y: set):
  ⋂(Pair x y) = PairSet x x.
Proof.
  apply set_ext. intro u. unfold Pair.
  rewrite intersection_pair_set.
  split.
  * intro h. apply intersection2_elim in h.
    destruct h as (hx, hy).
    exact hx.
  * intro h. apply pair_set_axiom in h.
    apply disj_idem in h.
    apply intersection2_intro. rewrite h.
    split.
    - apply pair_set_axiom. left. reflexivity.
    - apply pair_set_axiom. left. reflexivity.
Qed.

Theorem union_singleton (x: set):
  x = ⋃(PairSet x x).
Proof.
  apply set_ext. intro u. split.
  * intro h. apply union_axiom.
    exists x. split.
    - exact h.
    - apply pair_set_axiom. left. reflexivity.
  * intro h. apply union_axiom in h.
    destruct h as (A, (hu, hA)).
    apply pair_set_axiom in hA.
    apply disj_idem in hA.
    rewrite hA in hu. exact hu.
Qed.

Theorem pair_proj1 (x y: set):
  x = ⋃⋂(Pair x y).
Proof.
  rewrite intersection_pair.
  exact (union_singleton x).
Qed.

Theorem pair_proj2 (x y: set):
  x ≠ y → y = ⋃(⋃(Pair x y) \ ⋂(Pair x y)).
Proof.
  rewrite union_pair.
  rewrite intersection_pair.
  intro hxy. apply set_ext. intro u. split.
  * intro h. apply union_axiom.
    exists y. split.
    - exact h.
    - apply diff_intro. split.
      -- apply pair_set_axiom. right. reflexivity.
      -- intro hy. apply pair_set_axiom in hy.
         apply disj_idem in hy. exact (hxy (eq_sym hy)).
  * intro h. apply union_axiom in h.
    destruct h as (A, (hu, hA)).
    apply diff_elim in hA.
    destruct hA as (hAxy, hAnxx).
    apply pair_set_axiom in hAxy.
    destruct hAxy as [hx | hy].
    - rewrite hx in hAnxx. contradiction hAnxx.
      apply pair_set_axiom. left. reflexivity.
    - rewrite hy in hu. exact hu.
Qed.

Theorem pair_eq (x y x' y': set):
  Pair x y = Pair x' y' ↔ x = x' ∧ y = y'.
Proof.
  split.
  * intro h. assert (hx := h).
    apply (f_equal (fun u => ⋃⋂u)) in hx.
    rewrite <- (pair_proj1 x y) in hx.
    rewrite <- (pair_proj1 x' y') in hx.
    split.
    - exact hx.
    - rewrite <- hx in h. clear hx x'.
      apply (f_equal (fun u => ⋃u)) in h.
      rewrite (union_pair x y) in h.
      rewrite (union_pair x y') in h.
      destruct (classic (x = y)) as [hxy | hnxy].
      -- rewrite hxy in h.
         exact (singleton_eq_pair_set y y' h).
      -- assert (h0 := h).
         apply (f_equal (fun u => u \ (PairSet x x))) in h0.
         rewrite (pair_set_diff_singleton x y hnxy) in h0.
         assert (hy: y ∈ PairSet y y). {
           apply pair_set_axiom. left. reflexivity.
         }
         rewrite h0 in hy.
         apply diff_elim in hy.
         destruct hy as (hy1, hy2).
         rewrite pair_set_axiom in hy1.
         rewrite pair_set_axiom in hy2.
         rewrite disj_idem_eq in hy2.
         destruct hy1 as [hr | hl].
         --- exfalso. exact (hy2 hr).
         --- exact hl.
  * intros (hx, hy). rewrite hx. rewrite hy.
    reflexivity.
Qed.

Definition Prod (X Y: set) :=
  {t ∈ 𝓟(𝓟(X ∪ Y)) | ∃x, ∃y, x ∈ X ∧ y ∈ Y ∧ t = Pair x y}.

Lemma prod_elim {X Y t: set}:
  t ∈ Prod X Y → ∃x, ∃y, x ∈ X ∧ y ∈ Y ∧ t = Pair x y.
Proof.
  intro h. apply sep in h. exact (proj2 h).
Qed.

Lemma prod_intro {X Y: set} (x y t: set):
  x ∈ X → y ∈ Y → t = Pair x y → t ∈ Prod X Y.
Proof.
  intros hx hy ht.
  apply sep. split.
  * apply power_set_axiom. unfold Subset. intro u. intro hu.
    apply power_set_axiom. unfold Subset. intro a. intro ha.
    apply union2_intro.
    rewrite ht in hu. clear ht t.
    unfold Pair in hu. apply pair_set_axiom in hu.
    destruct hu as [hux | huy].
    - rewrite hux in ha. apply pair_set_axiom in ha.
      apply disj_idem in ha. rewrite ha. left. exact hx.
    - rewrite huy in ha. apply pair_set_axiom in ha.
      clear huy. destruct ha as [hax | hay].
      -- rewrite hax. left. exact hx.
      -- rewrite hay. right. exact hy.
  * exists x. exists y. split.
    - exact hx.
    - split.
      -- exact hy.
      -- exact ht.
Qed.

Lemma prod_intro_term {X Y x y: set}:
  x ∈ X → y ∈ Y → Pair x y ∈ Prod X Y.
Proof.
  intros hx hy. apply (prod_intro x y (Pair x y)).
  * exact hx.
  * exact hy.
  * reflexivity.
Qed.

Theorem prod_left_empty (Y: set): Prod ∅ Y = ∅.
Proof.
  apply set_ext. intro y. split.
  * intro h. apply prod_elim in h.
    destruct h as (u, (v, (hu, (hv, huv)))).
    apply (empty_set_axiom u) in hu.
    exfalso. exact hu.
  * intro h. apply (empty_set_axiom y) in h.
    exfalso. exact h.
Qed.

Theorem prod_empty_right (X: set): Prod X ∅ = ∅.
Proof.
  apply set_ext. intro x. split.
  * intro h. apply prod_elim in h.
    destruct h as (u, (v, (hu, (hv, huv)))).
    apply (empty_set_axiom v) in hv.
    exfalso. exact hv.
  * intro h. apply (empty_set_axiom x) in h.
    exfalso. exact h.
Qed.

Theorem pair_in_relation (X Y x y R: set):
  (Pair x y) ∈ R → R ⊆ (Prod X Y) → x ∈ X ∧ y ∈ Y.
Proof.
  intro hxy. intro hR.
  unfold Subset in hR.
  assert (h := hR (Pair x y) hxy).
  apply sep in h. apply proj2 in h.
  destruct h as (x', (y', (hx', (hy', heq)))).
  apply pair_eq in heq. destruct heq as (hx, hy).
  rewrite hx. rewrite hy.
  exact (conj hx' hy').
Qed.

