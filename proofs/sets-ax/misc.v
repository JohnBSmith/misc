
Require Import Coq.Unicode.Utf8.
Require Import axioms.
Require Import mappings.

Definition uapp f x :=
  ⋃{y | (x, y) ∈ f}.

Theorem uapp_iff {f X Y x y}:
  mapping f X Y → x ∈ X → ((x, y) ∈ f ↔ y = uapp f x).
Proof.
  intros hf hx. split.
  * intro h. unfold app. apply ext. intro u. split.
    - intro hu. apply union_intro. exists y. split.
      -- apply comp. split.
         --- assert (hxy := pair_in_mapping hf h).
             exact (set_intro (proj2 hxy)).
         --- exact h.
      -- exact hu.
    - intro hu. apply union_elim in hu.
      destruct hu as (y', (h', huy')).
      apply comp_elim in h'.
      assert (hyy' := proj_right_uniq hf x y y' h h').
      rewrite <- hyy' in huy'. exact huy'.
  * intro h. assert (hflt := proj_left_total hf x hx).
    destruct hflt as (y', hy').
    assert (heq: y' = uapp f x). {
      apply ext. intro u. split.
      * intro hu. unfold uapp. apply union_intro.
        exists y'. split.
        - apply comp. split.
          --- assert (hxy' := pair_in_mapping hf hy').
              exact (set_intro (proj2 hxy')).
          --- exact hy'.
        - exact hu.
      * intro hu. apply union_elim in hu.
        destruct hu as (y'', (hy'', huy'')).
        apply comp_elim in hy''.
        assert (hyy'' := proj_right_uniq
          hf x y' y'' hy' hy'').
        rewrite <- hyy'' in huy''.
        exact huy''.
    }
    rewrite <- heq in h. rewrite <- h in hy'.
    exact hy'.
Qed.

Theorem uapp_graph X f x:
  x ∈ X → set (f x) → uapp (graph_from X f) x = f x.
Proof.
  intros hx hsfx. apply ext. intro u. split.
  * intro h. apply comp_elim in h.
    destruct h as (y, (hy, hu)).
    apply comp_elim in hy.
    apply comp in hy. destruct hy as (hxy, hy).
    destruct hy as (x0, (hx0, heq)).
    apply pair_is_set_rev in hxy.
    destruct hxy as (hsx, hsy).
    apply (pair_eq _ _ _ _ hsx hsy) in heq.
    destruct heq as (h1, h2).
    rewrite h1. rewrite <- h2. exact hu.
  * intro h. apply comp. split.
    - exact (set_intro h).
    - exists (f x). split.
      -- apply comp. split.
         --- exact hsfx.
         --- apply comp. split.
             ---- apply pair_is_set.
                  exact (conj (set_intro hx) hsfx).
             ---- exists x. split.
                  ----- exact hx.
                  ----- reflexivity.
      -- exact h.
Qed.

Theorem uapp_outside_of_domain X Y f x:
  mapping f X Y → x ∉ X → uapp f x = ∅.
Proof.
  intro hf. intro hnx. apply ext. intro u. split.
  * intro h. apply comp in h.
    destruct h as (hsu, (y, (hy, hu))).
    apply comp in hy. destruct hy as (hsy, hxy).
    apply proj_relation in hf. unfold subclass in hf.
    apply hf in hxy. clear hf.
    apply prod_elim_term in hxy.
    destruct hxy as (hx, _). exfalso.
    exact (hnx hx).
  * intro hu. exfalso. exact (empty_set_property hu).
Qed.
