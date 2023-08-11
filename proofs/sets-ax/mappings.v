
Load "axioms.v".

Definition left_total X f :=
  ∀x, x ∈ X → ∃y, (x, y) ∈ f.

Definition right_uniq f :=
  ∀x y y', (x, y) ∈ f → (x, y') ∈ f → y = y'.

Definition app f x := ⋃ {y | (x, y) ∈ f}.

Definition mapping f X Y :=
  f ⊆ X × Y ∧ left_total X f ∧ right_uniq f.

Lemma proj_right_uniq {f X Y}: mapping f X Y
  → ∀x y y', (x, y) ∈ f → (x, y') ∈ f → y = y'.
Proof.
  intro h. unfold mapping in h.
  exact (proj2 (proj2 h)).
Qed.

Lemma proj_left_total {f X Y}: mapping f X Y
  → ∀x, x ∈ X → ∃y, (x, y) ∈ f.
Proof.
  intro h. unfold mapping in h.
  exact (proj1 (proj2 h)).
Qed.

Lemma proj_relation {f X Y}:
  mapping f X Y → f ⊆ X × Y.
Proof.
  intro h. unfold mapping in h. exact (proj1 h).
Qed.

Theorem pair_in_mapping {f X Y x y}:
  mapping f X Y → (x, y) ∈ f → x ∈ X ∧ y ∈ Y.
Proof.
  intro hf. intro hxy. apply proj_relation in hf.
  unfold Subclass in hf. apply hf in hxy. clear hf.
  apply prod_elim_term in hxy. exact hxy.
Qed.

Theorem app_iff {f X Y x y}:
  mapping f X Y → x ∈ X → ((x, y) ∈ f ↔ y = app f x).
Proof.
  intros hf hx. split.
  * intro h. unfold app. apply ext. intro u. split.
    - intro hu. apply union_intro. exists y. split.
      -- apply -> comp. split.
         --- assert (hxy := pair_in_mapping hf h).
             exact (set_intro (proj2 hxy)).
         --- exact h.
      -- exact hu.
    - intro hu. apply union_elim in hu.
      destruct hu as (y', (h', huy')).
      apply comp in h'. apply proj2 in h'.
      assert (hyy' := proj_right_uniq hf x y y' h h').
      rewrite <- hyy' in huy'. exact huy'.
  * intro h. assert (hflt := proj_left_total hf x hx).
    destruct hflt as (y', hy').
    assert (heq: y' = app f x). {
      apply ext. intro u. split.
      * intro hu. unfold app. apply union_intro.
        exists y'. split.
        - apply -> comp. split.
          --- assert (hxy' := pair_in_mapping hf hy').
              exact (set_intro (proj2 hxy')).
          --- exact hy'.
        - exact hu.
      * intro hu. apply union_elim in hu.
        destruct hu as (y'', (hy'', huy'')).
        apply comp in hy''. apply proj2 in hy''.
        assert (hyy'' := proj_right_uniq
          hf x y' y'' hy' hy'').
        rewrite <- hyy'' in huy''.
        exact huy''.
    }
    rewrite <- heq in h. rewrite <- h in hy'.
    exact hy'.
Qed.

Lemma mapping_ext_lemma {X Y f g}:
  mapping f X Y → mapping g X Y
  → (∀x, app f x = app g x) → f ⊆ g.
Proof.
  intro hf. intro hg. intro h. unfold Subclass. intro t.
  intro ht. assert (hrel := proj_relation hf).
  unfold Subclass in hrel. assert (h0 := hrel t ht).
  clear hrel. apply prod_elim in h0.
  destruct h0 as (x, (y, (hx, (hy, htxy)))).
  assert (h := h x). rewrite htxy in ht.
  apply (app_iff hf hx) in ht.
  rewrite h in ht.
  apply (app_iff hg hx) in ht.
  rewrite <- htxy in ht. exact ht.
Qed.

Theorem mapping_ext {X Y f g}:
  mapping f X Y → mapping g X Y
  → (∀x, app f x = app g x) → f = g.
Proof.
  intro hf. intro hg. intro h.
  assert (hfg := mapping_ext_lemma hf hg h).
  assert (h': ∀x, app g x = app f x). {
    intro x. apply eq_sym. exact (h x).
  }
  assert (hgf := mapping_ext_lemma hg hf h').
  apply ext. intro x. split.
  * intro hx. exact (hfg x hx). 
  * intro hx. exact (hgf x hx).
Qed.

Definition composition g f :=
  {t | ∃x y, t = (x, y) ∧ y = app g (app f x)}.

