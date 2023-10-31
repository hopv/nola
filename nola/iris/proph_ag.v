(** * Prophetic agreement *)

From nola.iris Require Export proph.
From iris.bi Require Import fractional.
From iris.base_logic.lib Require Import ghost_var.
From iris.proofmode Require Import proofmode.

(** Existential type over a syntactic type *)
#[projections(primitive)]
Record anyty (TY : synty) := Anyty {
  anyty_ty : TY;
  anyty_val : anyty_ty;
}.
Add Printing Constructor anyty.
Arguments Anyty {_} _ _. Arguments anyty_ty {_} _. Arguments anyty_val {_} _.

(** Ghost state *)
Class proph_agG TY Σ := proph_agG_in :: ghost_varG Σ (anyty TY).
Definition proph_agΣ TY := ghost_varΣ (anyty TY).
#[export] Instance subG_proph_agΣ `{!subG (proph_agΣ TY) Σ} : proph_agG TY Σ.
Proof. solve_inG. Qed.

Implicit Type γ : gname.
Section proph_ag.
  Context `{!proph_agG TY Σ, !prophGS TY Σ}.
  Implicit Type X : TY.

  (** Value observer *)
  Local Definition val_obs_def γ X x : iProp Σ := ghost_var γ (1/2) (Anyty X x).
  Local Lemma val_obs_aux : seal val_obs_def. Proof. by eexists. Qed.
  Definition val_obs := val_obs_aux.(unseal).
  Local Lemma val_obs_unseal : val_obs = val_obs_def.
  Proof. exact: seal_eq. Qed.

  (** Double value observer *)
  Local Definition val_obs2 γ X x : iProp Σ := ghost_var γ 1 (Anyty X x).

  (** Prophecy controller *)
  Local Definition proph_ctrl_def γ X x (ξ : prvar X) : iProp Σ :=
    (val_obs_def γ X x ∗ 1:[ξ]) ∨
    ((∃ x', val_obs2 γ X x') ∗ ⟨π, π ξ = x⟩).
  Local Lemma proph_ctrl_aux : seal proph_ctrl_def. Proof. by eexists. Qed.
  Definition proph_ctrl := proph_ctrl_aux.(unseal).
  Local Lemma proph_ctrl_unseal : proph_ctrl = proph_ctrl_def.
  Proof. exact: seal_eq. Qed.

  (** [val_obs] and [proph_ctrl] are timeless *)
  #[export] Instance val_obs_timeless {γ X x} : Timeless (val_obs γ X x).
  Proof. rewrite val_obs_unseal. exact _. Qed.
  #[export] Instance proph_ctrl_timeless {γ X x ξ} :
    Timeless (proph_ctrl γ X x ξ).
  Proof. rewrite proph_ctrl_unseal. exact _. Qed.

  (** [val_obs] and [val_obs2] can't coexist *)
  Local Lemma vo_vo2 {γ X x x'} : val_obs_def γ X x -∗ val_obs2 γ X x' -∗ False.
  Proof.
    iIntros "vo vo'". by iDestruct (ghost_var_valid_2 with "vo vo'") as %[? _].
  Qed.

  (** Allocate [val_obs] and [proph_ctrl] *)
  Lemma vo_pc_alloc {X x} {ξ : prvar X} :
    1:[ξ] ==∗ ∃ γ, val_obs γ X x ∗ proph_ctrl γ X x ξ.
  Proof.
    rewrite val_obs_unseal proph_ctrl_unseal. iIntros "ξ".
    iMod ghost_var_alloc as (γ) "[vo vo']". iModIntro. iExists _. iFrame "vo".
    iLeft. iFrame.
  Qed.

  (** Agreement between [val_obs] and [proph_ctrl] *)
  Lemma vo_pc_agree {γ X x x' ξ} :
    val_obs γ X x -∗ proph_ctrl γ X x' ξ -∗ ⌜x = x'⌝.
  Proof.
    rewrite val_obs_unseal proph_ctrl_unseal.
    iIntros "vo [[vo' _]|[[% vo2] _]]"; last first.
    { iDestruct (vo_vo2 with "vo vo2") as %[]. }
    iDestruct (ghost_var_agree with "vo vo'") as %?. by simplify_eq.
  Qed.

  (** Update the value of [val_obs] and [proph_ctrl] *)
  Lemma vo_pc_update {γ X x x' y ξ} :
    val_obs γ X x -∗ proph_ctrl γ X x' ξ ==∗ val_obs γ X y ∗ proph_ctrl γ X y ξ.
  Proof.
    rewrite val_obs_unseal proph_ctrl_unseal.
    iIntros "vo [[vo' ξ]|[[% vo2] _]]"; last first.
    { iDestruct (vo_vo2 with "vo vo2") as %[]. }
    iMod (ghost_var_update_2 with "vo vo'") as "[$ vo]"; [by rewrite Qp.div_2|].
    iModIntro. iLeft. iFrame.
  Qed.

  (** Resolve the prophecy of [proph_ctrl] with [val_obs],
    retaining [proph_ctrl] *)
  Lemma vo_pc_preresolve {γ X x x' ξ} aπ ηl q : aπ ./ ηl →
    q:∗[ηl] -∗ val_obs γ X x -∗ proph_ctrl γ X x' ξ =[proph_wsat]=∗
      q:∗[ηl] ∗ ⟨π, π ξ = aπ π⟩ ∗ (∀ y, ⟨π, aπ π = y⟩ -∗ proph_ctrl γ X y ξ).
  Proof.
    rewrite val_obs_unseal proph_ctrl_unseal.
    iIntros "% ηl vo [[vo' ξ]|[[% vo2] _]]"; last first.
    { iDestruct (vo_vo2 with "vo vo2") as %[]. }
    iMod (proph_resolve_dep with "ξ ηl") as "[$ #obs]"; [done|]. iModIntro.
    iFrame "obs". iIntros "%y obs'". iRight. iCombine "vo vo'" as "vo2".
    iSplit; [by iExists _|]. by iApply (proph_obs_impl2 with "obs obs'")=> ?->.
  Qed.
  Lemma vo_pc_resolve {γ X x x'} {y : X} {ξ} :
    val_obs γ X x -∗ proph_ctrl γ X x' ξ =[proph_wsat]=∗
      ⟨π, π ξ = y⟩ ∗ proph_ctrl γ X y ξ.
  Proof.
    iIntros "vo pc".
    iMod (vo_pc_preresolve (λ _, y) [] 1 with "[//] vo pc") as "[_[$ →pc]]".
    { done. } iModIntro. iApply "→pc". by iApply proph_obs_true.
  Qed.

  (** Resolve the prophecy of [proph_ctrl] *)
  Lemma pc_resolve {γ X x} ξ :
    proph_ctrl γ X x ξ =[proph_wsat]=∗ ⟨π, π ξ = x⟩.
  Proof.
    rewrite proph_ctrl_unseal. iIntros "[[_ ξ]|[_ $]]"; [|done].
    iApply (proph_resolve with "ξ").
  Qed.
End proph_ag.
