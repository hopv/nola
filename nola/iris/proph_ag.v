(** * Prophetic agreement *)

From nola.iris Require Export proph.
From nola.util Require Import prod.
From nola.bi Require Import modw.
From iris.bi Require Import fractional.
From iris.base_logic.lib Require Import ghost_var.
From iris.proofmode Require Import proofmode.
Import ProdNotation ProphNotation ModwNotation.

Implicit Type (A : Type) (TY : synty).

(** Ghost state *)
Class proph_agG A TY Σ :=
  proph_agG_in :: ghost_varG Σ (A *' sigT' (λ X : TY, clair TY X)).
Definition proph_agΣ A TY := ghost_varΣ (A *' sigT' (λ X : TY, clair TY X)).
#[export] Instance subG_proph_agΣ `{!subG (proph_agΣ A TY) Σ} :
  proph_agG A TY Σ.
Proof. solve_inG. Qed.

Implicit Type γ : gname.
Section proph_ag.
  Context `{!proph_agG A TY Σ, !prophGS TY Σ}.
  Implicit Type X : TY.

  (** Value observer *)
  Local Definition val_obs_def {X} γ a xπ : iProp Σ :=
    ghost_var γ (1/2) (a, existT' X xπ)'.
  Local Lemma val_obs_aux : seal (@val_obs_def). Proof. by eexists. Qed.
  Definition val_obs {X} := val_obs_aux.(unseal) X.
  Local Lemma val_obs_unseal : @val_obs = @val_obs_def.
  Proof. exact: seal_eq. Qed.

  (** Double value observer *)
  Local Definition val_obs2 {X} γ a xπ : iProp Σ :=
    ghost_var γ 1 (a, existT' X xπ)'.

  (** Prophecy controller *)
  Local Definition proph_ctrl_def {X} γ a xπ (ξ : prvar X) : iProp Σ :=
    (val_obs γ a xπ ∗ 1:[ξ]) ∨
      ((∃ a' xπ', @val_obs2 X γ a' xπ') ∗ proph_eqz (λ π, π ξ) xπ).
  Local Lemma proph_ctrl_aux : seal (@proph_ctrl_def). Proof. by eexists. Qed.
  Definition proph_ctrl {X} := proph_ctrl_aux.(unseal) X.
  Local Lemma proph_ctrl_unseal : @proph_ctrl = @proph_ctrl_def.
  Proof. exact: seal_eq. Qed.

  (** [val_obs] is timeless *)
  #[export] Instance val_obs_timeless {X γ a xπ} : Timeless (@val_obs X γ a xπ).
  Proof. rewrite val_obs_unseal. exact _. Qed.

  (** Allocate two [val_obs]s *)
  Lemma vo_vo_alloc {X a xπ} : ⊢ |==> ∃ γ, @val_obs X γ a xπ ∗ val_obs γ a xπ.
  Proof.
    rewrite val_obs_unseal. iMod ghost_var_alloc as (γ) "[??]". iExists _.
    by iFrame.
  Qed.

  (** Agreement between two [val_obs]s *)
  Lemma vo_vo_agree {X γ a xπ a' xπ'} :
    @val_obs X γ a xπ -∗ val_obs γ a' xπ' -∗ ⌜a = a' ∧ xπ = xπ'⌝.
  Proof.
    rewrite val_obs_unseal. iIntros "vo vo'".
    iDestruct (ghost_var_agree with "vo vo'") as %?. by simplify_eq.
  Qed.

  (** Update the value of two [val_obs]s *)
  Lemma vo_vo_update {X γ a xπ a' xπ' a'' xπ''} :
    @val_obs X γ a xπ -∗ @val_obs X γ a' xπ' ==∗
      @val_obs X γ a'' xπ'' ∗ val_obs γ a'' xπ''.
  Proof.
    rewrite val_obs_unseal. iIntros "vo vo'".
    iApply (ghost_var_update_2 with "vo vo'"). apply Qp.div_2.
  Qed.

  (** Construct [proph_ctrl] out of [val_obs] and a prophecy token *)
  Lemma vo_proph_pc {X γ a xπ ξ} :
    @val_obs X γ a xπ -∗ 1:[Aprvar _ ξ] -∗ proph_ctrl γ a xπ ξ.
  Proof. rewrite proph_ctrl_unseal. iIntros "vo ξ". iLeft. iFrame. Qed.

  (** Allocate [val_obs] and [proph_ctrl] *)
  Lemma vo_pc_alloc {X a xπ} {ξ : prvar X} :
    1:[ξ] ==∗ ∃ γ, val_obs γ a xπ ∗ proph_ctrl γ a xπ ξ.
  Proof.
    iIntros "ξ". iMod vo_vo_alloc as (γ) "[vo vo']". iModIntro. iExists _.
    iFrame "vo". iApply (vo_proph_pc with "vo' ξ").
  Qed.

  (** Turn two [val_obs] into [val_obs2] *)
  Local Lemma vo_vo_vo2 {X γ a xπ a' xπ'} :
    @val_obs X γ a xπ -∗ @val_obs X γ a' xπ' -∗ val_obs2 γ a xπ.
  Proof.
    rewrite val_obs_unseal. iIntros "vo vo'". iCombine ("vo vo'") as "$".
  Qed.

  (** [val_obs] and [val_obs2] can't co-exist *)
  Local Lemma vo_vo2_no {X γ a xπ a' xπ'} :
    @val_obs X γ a xπ -∗ val_obs2 (X:=X) γ a' xπ' -∗ False.
  Proof.
    rewrite val_obs_unseal. iIntros "vo vo2".
    by iDestruct (ghost_var_valid_2 with "vo vo2") as %[? _].
  Qed.

  (** Turn [proph_ctrl] into a prophecy equalizer *)
  Lemma pc_eqz {X γ a xπ ξ} :
    proph_ctrl (X:=X) γ a xπ ξ ⊢ proph_eqz (λ π, π ξ) xπ.
  Proof.
    rewrite proph_ctrl_unseal. iIntros "[[_ ξ]|[_ $]]".
    iApply (proph_eqz_tok with "ξ").
  Qed.

  (** Agreement between [val_obs] and [proph_ctrl] *)
  Lemma vo_pc_agree {X γ a xπ a' xπ' ξ} :
    @val_obs X γ a xπ -∗ proph_ctrl γ a' xπ' ξ -∗ ⌜a = a' ∧ xπ = xπ'⌝.
  Proof.
    rewrite proph_ctrl_unseal. iIntros "vo [[vo' _]|[(% & % & vo2) _]]".
    - iApply (vo_vo_agree with "vo vo'").
    - iDestruct (vo_vo2_no with "vo vo2") as %[].
  Qed.

  (** Turn [proph_ctrl] into [val_obs] and a prophecy token under [val_obs] *)
  Lemma vo_pc_proph {X γ a xπ a' xπ' ξ} :
    @val_obs X γ a xπ -∗ proph_ctrl (X:=X) γ a' xπ' ξ -∗
      val_obs γ a xπ ∗ val_obs γ a' xπ' ∗ 1:[Aprvar _ ξ].
  Proof.
    rewrite proph_ctrl_unseal. iIntros "vo [$|[(% & % & vo2) _]]"; [done|].
    iDestruct (vo_vo2_no with "vo vo2") as %[].
  Qed.

  (** Update the value of [val_obs] and [proph_ctrl] *)
  Lemma vo_pc_update {X γ a xπ a' xπ' a'' xπ'' ξ} :
    @val_obs X γ a xπ -∗ proph_ctrl γ a' xπ' ξ ==∗
      @val_obs X γ a'' xπ'' ∗ proph_ctrl γ a'' xπ'' ξ.
  Proof.
    iIntros "vo pc". iDestruct (vo_pc_proph with "vo pc") as "[vo [vo' ξ]]".
    iMod (vo_vo_update with "vo vo'") as "[$ vo']". iModIntro.
    iApply (vo_proph_pc with "vo' ξ").
  Qed.

  (** Resolve the prophecy of [proph_ctrl] with [val_obs], retaining
    [proph_ctrl] *)
  Lemma vo_pc_preresolve {X γ a0 xπ0 a1 xπ1 ξ} xπ ηl q :
    proph_dep xπ ηl →
    @val_obs X γ a0 xπ0 -∗ proph_ctrl (X:=X) γ a1 xπ1 ξ =[q:∗[ηl]]=∗
      ⟨π, π ξ = xπ π⟩ ∗ (∀ a' xπ', proph_eqz xπ xπ' -∗ proph_ctrl γ a' xπ' ξ).
  Proof.
    iIntros "% vo pc ηl".
    iDestruct (vo_pc_proph with "vo pc") as "(vo & vo' & ξ)".
    iMod (proph_resolve_dep with "ξ ηl") as "[$ #obs]"; [done|]. iModIntro.
    iFrame "obs". iIntros "% % eqz". rewrite proph_ctrl_unseal. iRight.
    iDestruct (vo_vo_vo2 with "vo vo'") as "$".
    iApply (proph_eqz_modify with "obs eqz").
  Qed.
End proph_ag.
