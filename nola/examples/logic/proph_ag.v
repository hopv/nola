(** * Prophetic agreement *)

From nola.examples.logic Require Import synty.
From iris.bi Require Export fractional.
From iris.base_logic.lib Require Export ghost_var.
From iris.proofmode Require Import proofmode.

(** Existential type over a syntactic type *)
#[projections(primitive)]
Record anyty := Anyty {
  anyty_ty : nsynty;
  anyty_val : anyty_ty;
}.
Add Printing Constructor anyty.

(** Ghost state *)
Class proph_agG Σ := proph_agG_in :: ghost_varG Σ anyty.
Definition proph_agΣ := ghost_varΣ anyty.
#[export] Instance subG_proph_agΣ `{!subG proph_agΣ Σ} : proph_agG Σ.
Proof. solve_inG. Qed.

Section proph_ag.
  Context `{!proph_agG Σ, !prophGS nsynty Σ}.

  (** Value observer *)
  Definition vo γ X x : iProp Σ := (ghost_var γ (1/2) (Anyty X x)).
  (** Double value observer *)
  Definition vo2 γ X x : iProp Σ := (ghost_var γ 1 (Anyty X x)).
  (** Prophecy controller *)
  Definition pc γ X x (ξ : prvar X) : iProp Σ :=
    (vo γ X x ∗ 1:[ξ]) ∨
    ((∃ x', vo2 γ X x') ∗ ⟨π, π ξ = x⟩).

  (** [vo] and [vo2] can't coexist *)
  Lemma vo_vo2 {γ X x x'} : vo γ X x -∗ vo2 γ X x' -∗ False.
  Proof.
    iIntros "vo vo'". by iDestruct (ghost_var_valid_2 with "vo vo'") as %[? _].
  Qed.

  (** Allocate [vo] and [pc] *)
  Lemma vo_pc_alloc {X x} {ξ : prvar X} : 1:[ξ] ==∗ ∃ γ, vo γ X x ∗ pc γ X x ξ.
  Proof.
    iIntros "ξ". iMod ghost_var_alloc as (γ) "[vo vo']". iModIntro. iExists _.
    iFrame "vo". iLeft. iFrame.
  Qed.

  (** Agreement between [vo] and [pc] *)
  Lemma vo_pc_agree {γ X x x' ξ} : vo γ X x -∗ pc γ X x' ξ -∗ ⌜x = x'⌝.
  Proof.
    iIntros "vo [[vo' _]|[[% vo2] _]]"; last first.
    { iDestruct (vo_vo2 with "vo vo2") as %[]. }
    iDestruct (ghost_var_agree with "vo vo'") as %?. by simplify_eq.
  Qed.

  (** Update the value of [vo] and [pc] *)
  Lemma vo_pc_update {γ X x x' y ξ} :
    vo γ X x -∗ pc γ X x' ξ ==∗ vo γ X y ∗ pc γ X y ξ.
  Proof.
    iIntros "vo [[vo' ξ]|[[% vo2] _]]"; last first.
    { iDestruct (vo_vo2 with "vo vo2") as %[]. }
    iMod (ghost_var_update_2 with "vo vo'") as "[$ vo]"; [by rewrite Qp.div_2|].
    iModIntro. iLeft. iFrame.
  Qed.

  (** Resolve the prophecy of [pc] *)
  Lemma vo_pc_preresolve {γ X x x'} ξ aπ ηl q : aπ ./ ηl →
    q:∗[ηl] -∗ vo γ X x -∗ pc γ X x' ξ =[proph_wsat]=∗
      q:∗[ηl] ∗ ⟨π, π ξ = aπ π⟩ ∗ (∀ y, ⟨π, aπ π = y⟩ -∗ pc γ X y ξ).
  Proof.
    iIntros "% ηl vo [[vo' ξ]|[[% vo2] _]]"; last first.
    { iDestruct (vo_vo2 with "vo vo2") as %[]. }
    iMod (proph_resolve_dep with "ξ ηl") as "[$ #obs]"; [done|]. iModIntro.
    iFrame "obs". iIntros "%y obs'". iRight. iCombine "vo vo'" as "vo2".
    iSplit; [by iExists _|]. by iApply (proph_obs_impl2 with "obs obs'")=> ?->.
  Qed.
  Lemma pc_resolve {γ X x} ξ :
    pc γ X x ξ =[proph_wsat]=∗ ⟨π, π ξ = x⟩.
  Proof.
    iIntros "[[_ ξ]|[_ $]]"; [|done]. iApply (proph_resolve with "ξ").
  Qed.
End proph_ag.
