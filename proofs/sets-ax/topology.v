
Require Import Coq.Unicode.Utf8.
Require Import axioms.
Require Import basic.
Require Import mappings.

Local Definition class_ext := ext.

Record topology X T := {
  top_empty_set_in: ∅ ∈ T;
  top_self_in: X ∈ T;
  top_closed_intersection2:
    ∀A B, A ∈ T → B ∈ T → A ∩ B ∈ T;
  top_closed_union:
    ∀M, M ⊆ T → ⋃M ∈ T;
}.

Definition nh_filter X T x :=
  {U | U ⊆ X ∧ ∃A, A ∈ T ∧ x ∈ A ∧ A ⊆ U}.

Definition int X T M :=
  {x | x ∈ M ∧ M ∈ nh_filter X T x}.

Definition ext X T M :=
  int X T (X \ M).

Definition cl X T M :=
  X \ ext X T M.

Definition bd X T M :=
  cl X T M \ int X T M.

Definition subsp_top T M :=
  {B | ∃A, A ∈ T ∧ B = A ∩ M}.

Definition cont Y TX TY f :=
  ∀A, A ∈ TY → inv_img f Y ∈ TX.

Theorem restr_cont X Y TX TY f M:
  topology X TX → topology Y TY →
  mapping f X Y → cont Y TX TY f →
  M ⊆ X → cont Y (subsp_top TX M) TY (restr f M).
Proof.
  intros hX hY hf hcf hMX. unfold cont. intros B hB.
  apply top_self_in in hX. apply set_intro in hX.
  apply top_self_in in hY. apply set_intro in hY.
  apply comp. split.
  * assert (hrf := restr_is_mapping hf hMX).
    apply (inv_img_is_set_from_graph Y hrf).
    exact (restr_is_set hX hY hf hMX).
  * unfold cont in hcf. apply hcf in hB as h.
    clear hcf hB.
    pose (A := inv_img f Y). fold A in h.
    exists A. split.
    - exact h.
    - rewrite inv_img_restr. fold A.
      rewrite intersection2_com.
      reflexivity.
Qed.
