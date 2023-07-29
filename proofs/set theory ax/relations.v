
Load "axioms.v".

Theorem disj_idem {A: Prop}:
  A ∨ A → A.
Proof.
  intro h. destruct h as [hl | hr].
  * exact hl.
  * exact hr.
Qed.

Theorem disj_idem_eq {A: Prop}:
  A ∨ A ↔ A.
Proof.
  split.
  * intro h. destruct h as [hl | hr].
    - exact hl.
    - exact hr.
  * intro h. left. exact h.
Qed.

Definition Pair (x: set) (y: set) :=
  PairSet (PairSet x x) (PairSet x y).

Theorem singleton_eq_pair_set (x y: set):
  PairSet x x = PairSet x y → x = y.
Proof.
  intro h.
  assert (hy: y ∈ PairSet x y). {
    apply pair_set_ext. right. reflexivity.
  }
  rewrite <- h in hy.
  apply pair_set_ext in hy.
  apply disj_idem in hy.
  apply eq_sym. exact hy.
Qed.

Theorem pair_set_diff_singleton (x y: set):
  x ≠ y → (PairSet x y) \ (PairSet x x) = (PairSet y y).
Proof.
  intro hxy. apply set_ext. intro u. split.
  * intro h. apply pair_set_ext. left.
    apply diff_elim in h.
    rewrite pair_set_ext in h.
    rewrite pair_set_ext in h.
    destruct h as (hl, hr).
    rewrite disj_idem_eq in hr.
    destruct hl as [hx | hy].
    - exfalso. exact (hr hx). 
    - exact hy.
  * intro h. apply pair_set_ext in h.
    apply disj_idem in h.
    apply diff_intro. split.
    - apply pair_set_ext. right. exact h.
    - intro hu. apply pair_set_ext in hu.
      apply disj_idem in hu.
      rewrite hu in h. exact (hxy h).
Qed.

Theorem union_pair (x y: set):
  ⋃(Pair x y) = PairSet x y.
Proof.
  apply set_ext. intro u. split.
  * intro h. apply pair_set_ext.
    apply union_system_ext in h.
    destruct h as (A, (hu, hA)).
    unfold Pair in hA. apply pair_set_ext in hA.
    destruct hA as [hx | hy].
    - rewrite hx in hu. apply pair_set_ext in hu.
      apply disj_idem in hu. left. exact hu.
    - rewrite hy in hu. apply pair_set_ext in hu.
      exact hu.
  * intro h. apply union_system_ext.
    apply pair_set_ext in h. destruct h as [hx | hy].
    - exists (PairSet x x). split.
      -- apply pair_set_ext. left. exact hx.
      -- unfold Pair. apply pair_set_ext.
         left. reflexivity.
    - exists (PairSet x y). split.
      -- apply pair_set_ext. right. exact hy.
      -- unfold Pair. apply pair_set_ext.
         right. reflexivity.
Qed.

Theorem intersection_pair (x y: set):
  ⋂(Pair x y) = PairSet x x.
Proof.
  apply set_ext. intro u. unfold Pair.
  rewrite intersection_pair_set.
  split.
  * intro h. apply intersection_elim in h.
    destruct h as (hx, hy).
    exact hx.
  * intro h. apply pair_set_ext in h.
    apply disj_idem in h.
    apply intersection_intro. rewrite h.
    split.
    - apply pair_set_ext. left. reflexivity.
    - apply pair_set_ext. left. reflexivity.
Qed.

Theorem union_singleton (x: set):
  x = ⋃(PairSet x x).
Proof.
  apply set_ext. intro u. split.
  * intro h. apply union_system_ext.
    exists x. split.
    - exact h.
    - apply pair_set_ext. left. reflexivity.
  * intro h. apply union_system_ext in h.
    destruct h as (A, (hu, hA)).
    apply pair_set_ext in hA.
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
  * intro h. apply union_system_ext.
    exists y. split.
    - exact h.
    - apply diff_intro. split.
      -- apply pair_set_ext. right. reflexivity.
      -- intro hy. apply pair_set_ext in hy.
         apply disj_idem in hy. exact (hxy (eq_sym hy)).
  * intro h. apply union_system_ext in h.
    destruct h as (A, (hu, hA)).
    apply diff_elim in hA.
    destruct hA as (hAxy, hAnxx).
    apply pair_set_ext in hAxy.
    destruct hAxy as [hx | hy].
    - rewrite hx in hAnxx. contradiction hAnxx.
      apply pair_set_ext. left. reflexivity.
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
           apply pair_set_ext. left. reflexivity.
         }
         rewrite h0 in hy.
         apply diff_elim in hy.
         destruct hy as (hy1, hy2).
         rewrite pair_set_ext in hy1.
         rewrite pair_set_ext in hy2.
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
  * apply power_set_ext. unfold Subset. intro u. intro hu.
    apply power_set_ext. unfold Subset. intro a. intro ha.
    apply union_intro.
    rewrite ht in hu. clear ht t.
    unfold Pair in hu. apply pair_set_ext in hu.
    destruct hu as [hux | huy].
    - rewrite hux in ha. apply pair_set_ext in ha.
      apply disj_idem in ha. rewrite ha. left. exact hx.
    - rewrite huy in ha. apply pair_set_ext in ha.
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

Definition left_total (f X: set) :=
  ∀x, x ∈ X → ∃y, (Pair x y) ∈ f.

Definition right_uniq (f: set) :=
  ∀x y y', (Pair x y) ∈ f → (Pair x y') ∈ f → y = y'.

Definition Abb (X Y: set) :=
  {f ∈ 𝓟 (Prod X Y) | left_total f X ∧ right_uniq f}.

Definition Preimg (X f B: set) :=
  {x ∈ X | ∃y, y ∈ B ∧ Pair x y ∈ f}.

Theorem preimg_intersection (X Y f A B: set):
  f ∈ Abb X Y → A ⊆ Y → B ⊆ Y →
    Preimg X f (A ∩ B) = (Preimg X f A) ∩ (Preimg X f B).
Proof.
  intros context hAY hBY.
  apply sep in context.
  destruct context as (_, (_, huniq)).
  apply set_ext. intro x. split.
  * intro h. apply sep in h.
    destruct h as (hx, (y, (hyAB, hxyf))).
    apply intersection_elim in hyAB.
    destruct hyAB as (hyA, hyB).
    apply intersection_intro. split.
    - apply sep. split.
      -- exact hx.
      -- exists y. exact (conj hyA hxyf). 
    - apply sep. split.
      -- exact hx.
      -- exists y. exact (conj hyB hxyf).
  * intro h. apply intersection_elim in h.
    destruct h as (hA, hB).
    apply sep in hA. destruct hA as (hx, (y, (hy, hf))).
    apply sep in hB. destruct hB as (_, (y', (hy', hf'))).
    apply sep. split.
    - exact hx.
    - exists y. unfold right_uniq in huniq.
      assert (hyY := hAY y hy). clear hAY.
      assert (hy'Y := hBY y' hy'). clear hBY.
      assert (hyy' := huniq x y y' hf hf').
      clear huniq. rewrite <- hyy' in hy'. clear hyy'.
      split.
      -- apply intersection_intro. exact (conj hy hy').
      -- exact hf.
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

Definition app (Y f x: set): set :=
  ⋃{y ∈ Y | (Pair x y) ∈ f}.

Theorem application_iff (X Y f x y: set):
  x ∈ X → f ∈ Abb X Y → (y = app Y f x ↔ (Pair x y) ∈ f).
Proof.
  intro hx. intro hf.
  split.
  * intro h. apply sep in hf.
    assert (hft := proj1 (proj2 hf)).
    assert (hfr := proj2 (proj2 hf)).
    unfold left_total in hft.
    destruct (hft x hx) as (y', hy').
    assert (heq: y' = app Y f x). {
      apply set_ext. intro u. split.
      * intro hu. apply union_system_ext.
        exists y'. split.
        - exact hu.
        - apply sep. split.
          -- apply proj1 in hf.
             apply power_set_ext in hf.
             apply (pair_in_relation X Y x y' f hy') in hf.
             exact (proj2 hf).
          -- exact hy'.
      * intro hu. apply union_system_ext in hu.
        destruct hu as (y'', (hu, hy'')).
        apply sep in hy''. apply proj2 in hy''.
        unfold right_uniq in hfr.
        assert (heq := hfr x y' y'' hy' hy'').
        rewrite heq. exact hu.
    }
    rewrite <- h in heq. rewrite heq in hy'.
    exact hy'.
  * intro h. apply set_ext. intro u. split.
    - intro hu. unfold app.
      apply union_system_ext. exists y.
      split.
      -- exact hu.
      -- apply sep. split.
         --- apply sep in hf. apply proj1 in hf.
             apply power_set_ext in hf.
             apply (pair_in_relation X Y x y f h) in hf.
             exact (proj2 hf).
         --- exact h.
    - intro hu. unfold app in hu.
      apply union_system_ext in hu.
      destruct hu as (y', (hu, hy')).
      apply sep in hy'. destruct hy' as (hy', hxy').
      apply sep in hf. apply proj2 in hf.
      apply proj2 in hf. unfold right_uniq in hf.
      assert (heq := hf x y y' h hxy').
      rewrite heq. exact hu.
Qed.

