
Load "axioms.v".

Definition left_total X f :=
  ∀x, x ∈ X → ∃y, (x, y) ∈ f.

Definition right_uniq f :=
  ∀x y y', (x, y) ∈ f → (x, y') ∈ f → y = y'.

Definition app f x := ⋃ {y | (x, y) ∈ f}.

Definition Abb (X Y: set) :=
  {f | f ⊆ X × Y ∧ left_total X f ∧ right_uniq f}.

Lemma proj_right_uniq {f X Y}: f ∈ Abb X Y
  → ∀x y y', (x, y) ∈ f → (x, y') ∈ f → y = y'.
Proof.
  intro h. unfold Abb in h. apply comp_elim in h.
  simpl in h. exact (proj2 (proj2 h)).
Qed.

Lemma proj_left_total {f X Y}: f ∈ Abb X Y
  → ∀x, x ∈ X → ∃y, (x, y) ∈ f.
Proof.
  intro h. unfold Abb in h. apply comp_elim in h.
   simpl in h. exact (proj1 (proj2 h)).
Qed.

Lemma proj_relation {f X Y}:
  f ∈ Abb X Y → f ⊆ X × Y.
Proof.
  intro h. unfold Abb in h. apply comp_elim in h.
  simpl in h. exact (proj1 h).
Qed.

Theorem app_iff {f X Y x y}:
  x ∈ X → f ∈ Abb X Y → ((x, y) ∈ f ↔ y = app f x).
Proof.
  intro hx. intro hf. split.
  * intro h. unfold app. apply set_ext. intro u. split.
    - intro hu. apply union_intro. exists y. split.
      -- apply comp_intro. exact h. 
      -- exact hu.
    - intro hu. apply union_elim in hu.
      destruct hu as (y', (h', huy')).
      apply comp_elim in h'. simpl in h'.
      assert (hyy' := proj_right_uniq hf x y y' h h').
      rewrite <- hyy' in huy'. exact huy'.
  * intro h. assert (hflt := proj_left_total hf x hx).
    destruct hflt as (y', hy').
    assert (heq: y' = app f x). {
      apply set_ext. intro u. split.
      * intro hu. unfold app. apply union_intro.
        exists y'. split.
        - apply comp_intro. exact hy'.
        - exact hu.
      * intro hu. apply union_elim in hu.
        destruct hu as (y'', (hy'', huy'')).
        apply comp_elim in hy''. simpl in hy''.
        assert (hyy'' := proj_right_uniq
          hf x y' y'' hy' hy'').
        rewrite <- hyy'' in huy''.
        exact huy''.
    }
    rewrite <- heq in h. rewrite <- h in hy'.
    exact hy'.
Qed.

Lemma mapping_ext_lemma {X Y f g}:
  f ∈ Abb X Y → g ∈ Abb X Y
  → (∀x, app f x = app g x) → f ⊆ g.
Proof.
  intro hf. intro hg. intro h. unfold Subset. intro t.
  intro ht. assert (hrel := proj_relation hf).
  unfold Subset in hrel. assert (h0 := hrel t ht).
  clear hrel. apply prod_elim in h0.
  destruct h0 as (x, (y, (hx, (hy, htxy)))).
  assert (h := h x). rewrite htxy in ht.
  apply (app_iff hx hf) in ht.
  rewrite h in ht.
  apply (app_iff hx hg) in ht.
  rewrite <- htxy in ht. exact ht.
Qed.

Theorem mapping_ext {X Y f g}:
  f ∈ Abb X Y → g ∈ Abb X Y
  → (∀x, app f x = app g x) → f = g.
Proof.
  intro hf. intro hg. intro h.
  assert (hfg := mapping_ext_lemma hf hg h).
  assert (h': ∀x, app g x = app f x). {
    intro x. apply eq_sym. exact (h x).
  }
  assert (hgf := mapping_ext_lemma hg hf h').
  apply set_ext. intro x. split.
  * intro hx. exact (hfg x hx). 
  * intro hx. exact (hgf x hx).
Qed.

Definition composition g f :=
  {t | ∃x y, t = (x, y) ∧ y = app g (app f x)}.

