(** * Prophetic agreement *)

From nola.iris Require Export proph.
From iris.bi Require Import fractional.
From iris.base_logic.lib Require Import ghost_var.
From iris.proofmode Require Import proofmode.

(** Ghost state *)
Class proph_agG TY Σ := proph_agG_in :: ghost_varG Σ (anyty TY id).
Definition proph_agΣ TY := ghost_varΣ (anyty TY id).
#[export] Instance subG_proph_agΣ `{!subG (proph_agΣ TY) Σ} : proph_agG TY Σ.
Proof. solve_inG. Qed.

Implicit Type γ : gname.
Section proph_ag.
  Context `{!proph_agG TY Σ, !prophGS TY Σ}.
  Implicit Type X : TY.

  (** Value observer *)
  Local Definition val_obs_def {X} γ x : iProp Σ :=
    ghost_var γ (1/2) (Anyty X x).
  Local Lemma val_obs_aux : seal (@val_obs_def). Proof. by eexists. Qed.
  Definition val_obs {X} := val_obs_aux.(unseal) X.
  Local Lemma val_obs_unseal : @val_obs = @val_obs_def.
  Proof. exact: seal_eq. Qed.

  (** Double value observer *)
  Local Definition val_obs2 {X} γ x : iProp Σ := ghost_var γ 1 (Anyty X x).

  (** Prophecy controller *)
  Local Definition proph_ctrl_def {X} γ x (ξ : prvar X) : iProp Σ :=
    (val_obs γ x ∗ 1:[ξ]) ∨
    ((∃ x' : X, val_obs2 γ x') ∗ ⟨π, π ξ = x⟩).
  Local Lemma proph_ctrl_aux : seal (@proph_ctrl_def). Proof. by eexists. Qed.
  Definition proph_ctrl {X} := proph_ctrl_aux.(unseal) X.
  Local Lemma proph_ctrl_unseal : @proph_ctrl = @proph_ctrl_def.
  Proof. exact: seal_eq. Qed.

  (** [val_obs] and [proph_ctrl] are timeless *)
  #[export] Instance val_obs_timeless {X γ x} : Timeless (val_obs (X:=X) γ x).
  Proof. rewrite val_obs_unseal. exact _. Qed.
  #[export] Instance proph_ctrl_timeless {X γ x ξ} :
    Timeless (proph_ctrl (X:=X) γ x ξ).
  Proof. rewrite proph_ctrl_unseal. exact _. Qed.

  (** Allocate two [val_obs]s *)
  Lemma vo_vo_alloc {X x} :
    ⊢ |==> ∃ γ, val_obs (X:=X) γ x ∗ val_obs γ x.
  Proof.
    rewrite val_obs_unseal. iMod ghost_var_alloc as (γ) "[??]". iExists _.
    by iFrame.
  Qed.

  (** Agreement between two [val_obs]s *)
  Lemma vo_vo_agree {X γ x x'} :
    val_obs (X:=X) γ x -∗ val_obs γ x' -∗ ⌜x = x'⌝.
  Proof.
    rewrite val_obs_unseal. iIntros "vo vo'".
    iDestruct (ghost_var_agree with "vo vo'") as %?. by simplify_eq.
  Qed.

  (** Update the value of two [val_obs]s *)
  Lemma vo_vo_update {X γ x x' y} :
    val_obs (X:=X) γ x -∗ val_obs (X:=X) γ x' ==∗
      val_obs (X:=X) γ y ∗ val_obs γ y.
  Proof.
    rewrite val_obs_unseal. iIntros "vo vo'".
    iApply (ghost_var_update_2 with "vo vo'"). by rewrite Qp.div_2.
  Qed.

  (** Get [proph_ctrl] out of [val_obs] and a prophecy token *)
  Lemma vo_proph_pc {X γ x ξ} :
    ⊢ val_obs (X:=X) γ x -∗ 1:[Aprvar _ ξ] -∗ proph_ctrl γ x ξ.
  Proof.
    rewrite proph_ctrl_unseal. iIntros "vo ξ". iLeft. iFrame.
  Qed.

  (** Allocate [val_obs] and [proph_ctrl] *)
  Lemma vo_pc_alloc {X x} {ξ : prvar X} :
    1:[ξ] ==∗ ∃ γ, val_obs γ x ∗ proph_ctrl γ x ξ.
  Proof.
    iIntros "ξ". iMod vo_vo_alloc as (γ) "[vo vo']". iModIntro. iExists _.
    iFrame "vo". iApply (vo_proph_pc with "vo' ξ").
  Qed.

  (** Turn two [val_obs] into [val_obs2] *)
  Local Lemma vo_vo_vo2 {X γ x x'} :
    val_obs (X:=X) γ x -∗ val_obs (X:=X) γ x' -∗ val_obs2 γ x.
  Proof.
    rewrite val_obs_unseal. iIntros "vo vo'". iCombine ("vo vo'") as "$".
  Qed.

  (** [val_obs] and [val_obs2] can't co-exist *)
  Local Lemma vo_vo2_no {X γ x x'} :
    val_obs (X:=X) γ x -∗ val_obs2 (X:=X) γ x' -∗ False.
  Proof.
    rewrite val_obs_unseal. iIntros "vo vo2".
    by iDestruct (ghost_var_valid_2 with "vo vo2") as %[? _].
  Qed.

  (** Agreement between [val_obs] and [proph_ctrl] *)
  Lemma vo_pc_agree {X γ x x' ξ} :
    val_obs (X:=X) γ x -∗ proph_ctrl γ x' ξ -∗ ⌜x = x'⌝.
  Proof.
    rewrite proph_ctrl_unseal. iIntros "vo [[vo' _]|[[% vo2]_]]".
    - iApply (vo_vo_agree with "vo vo'").
    - iDestruct (vo_vo2_no with "vo vo2") as %[].
  Qed.

  (** Turn [proph_ctrl] into [val_obs] and a prophecy token under [val_obs] *)
  Lemma vo_pc_vo_proph {X γ x x' ξ} :
    ⊢ val_obs (X:=X) γ x -∗ proph_ctrl (X:=X) γ x' ξ -∗
      val_obs γ x ∗ val_obs γ x ∗ 1:[Aprvar _ ξ].
  Proof.
    iIntros "vo pc". iDestruct (vo_pc_agree with "vo pc") as %<-.
    rewrite proph_ctrl_unseal. iDestruct "pc" as "[$|[[% vo2]_]]"; [done|].
    iDestruct (vo_vo2_no with "vo vo2") as %[].
  Qed.

  (** Update the value of [val_obs] and [proph_ctrl] *)
  Lemma vo_pc_update {X γ x x' y ξ} :
    val_obs (X:=X) γ x -∗ proph_ctrl γ x' ξ ==∗
      val_obs (X:=X) γ y ∗ proph_ctrl γ y ξ.
  Proof.
    iIntros "vo pc". iDestruct (vo_pc_vo_proph with "vo pc") as "[vo[vo' ξ]]".
    iMod (vo_vo_update with "vo vo'") as "[$ vo']". iModIntro.
    iApply (vo_proph_pc with "vo' ξ").
  Qed.

  (** Resolve the prophecy of [proph_ctrl] with [val_obs],
    retaining [proph_ctrl] *)
  Lemma vo_pc_preresolve {X γ x x' ξ} aπ ηl q : aπ ./ ηl →
    q:∗[ηl] -∗ val_obs (X:=X) γ x -∗ proph_ctrl (X:=X) γ x' ξ ==∗
      q:∗[ηl] ∗ ⟨π, π ξ = aπ π⟩ ∗
      (∀ x'', ⟨π, aπ π = x''⟩ -∗ proph_ctrl γ x'' ξ).
  Proof.
    iIntros "% ηl vo pc".
    iDestruct (vo_pc_vo_proph with "vo pc") as "[vo[vo' ξ]]".
    iMod (proph_resolve_dep with "ξ ηl") as "[$ #obs]"; [done|]. iModIntro.
    iFrame "obs". iIntros "%y obs'". rewrite proph_ctrl_unseal. iRight.
    iDestruct (vo_vo_vo2 with "vo vo'") as "vo2". iSplit; [by iExists _|].
    by iApply (proph_obs_impl2 with "obs obs'")=> ?->.
  Qed.
  Lemma vo_pc_resolve {X γ} {x x' x'' : X} {ξ} :
    val_obs (X:=X) γ x -∗ proph_ctrl γ x' ξ ==∗
      ⟨π, π ξ = x''⟩ ∗ proph_ctrl γ x'' ξ.
  Proof.
    iIntros "vo pc".
    iMod (vo_pc_preresolve (λ _, x'') [] 1 with "[//] vo pc") as "[_[$ →pc]]".
    { done. } iModIntro. iApply "→pc". by iApply proph_obs_true.
  Qed.

  (** Resolve the prophecy of [proph_ctrl] *)
  Lemma pc_resolve {X γ x} ξ : proph_ctrl (X:=X) γ x ξ ==∗ ⟨π, π ξ = x⟩.
  Proof.
    rewrite proph_ctrl_unseal. iIntros "[[_ ξ]|[_ $]]"; [|done].
    iApply (proph_resolve with "ξ").
  Qed.
End proph_ag.
