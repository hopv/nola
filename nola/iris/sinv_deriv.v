(** * Simple invariant machinery relaxed with derivability *)

From nola.util Require Import tagged.
From nola.bi Require Export deriv.
From nola.iris Require Export sinv.
From iris.proofmode Require Import proofmode.
Import FunNPNotation iPropAppNotation UpdwNotation DsemNotation.

(** ** [sinv_judgty]: Judgment type for [sinv] *)
Variant sinv_judg_id := .
Definition sinv_judgty (FM : ofe) : ofe :=
  (** Accessor judgment *) tagged sinv_judg_id (FM * FM).

(** ** [SinvJudg]: Judgment structure for [sinv] *)
Notation SinvJudg FM JUDG := (Ejudg (sinv_judgty FM) JUDG).

Section sinv_deriv.
  Context `{!sinvGS FML Σ, sinv_judg : !SinvJudg (FML $oi Σ) JUDG}.
  Implicit Type δ : JUDG -n> iProp Σ.

  (** Accessor judgment *)
  Local Definition sinv_jacsr (Px Qx : FML $oi Σ) : JUDG :=
    sinv_judg (Tagged (Px, Qx)).
  Local Instance sinv_jacsr_ne : NonExpansive2 sinv_jacsr.
  Proof. solve_proper. Qed.

  (** [sinv]: Relaxed simple invariant *)
  Local Definition sinv_def δ (Px : FML $oi Σ) : iProp Σ :=
    ∃ Qx, □ δ (sinv_jacsr Qx Px) ∗ sinv_tok Qx.
  Local Lemma sinv_aux : seal sinv_def. Proof. by eexists. Qed.
  Definition sinv := sinv_aux.(unseal).
  Local Lemma sinv_unseal : sinv = sinv_def. Proof. exact: seal_eq. Qed.

  (** [sinv] is persistent *)
  #[export] Instance sinv_persistent {δ Px} : Persistent (sinv δ Px).
  Proof. rewrite sinv_unseal. exact _. Qed.

  (** [sinv] is non-expansive *)
  #[export] Instance sinv_ne {δ} : NonExpansive (sinv δ).
  Proof. rewrite sinv_unseal. solve_proper. Qed.
  #[export] Instance sinv_proper {δ} :
    Proper ((≡) ==> (⊣⊢)) (sinv δ).
  Proof. apply ne_proper, _. Qed.
End sinv_deriv.

(** Notation *)
Notation sinvd := (sinv der).

Section sinv_deriv.
  Context `{!SinvJudg (FML $oi Σ) JUDG, !Jsem JUDG (iProp Σ),
    !Dsem JUDG (FML $oi Σ) (iProp Σ)}.
  Implicit Type (δ : JUDG -n> iProp Σ).

  (** ** [sinv_judg_sem]: Semantics of [sinv_judgty] *)
  Definition sinv_judg_sem δ '(PQx : sinv_judgty (FML $oi Σ)) : iProp Σ :=
    mod_acsr bupd ⟦ PQx.(untag).1 ⟧(δ) ⟦ PQx.(untag).2 ⟧(δ).
  (** [sinv_judg_sem] is non-expansive *)
  #[export] Instance sinv_judg_sem_ne {δ} :
    NonExpansive (sinv_judg_sem δ).
  Proof. solve_proper. Qed.
  (** [Dsem] over [sinv_judgty] *)
  #[export] Instance sinv_judg_dsem
    : Dsem JUDG (sinv_judgty (FML $oi Σ)) (iProp Σ) := DSEM sinv_judg_sem _.
End sinv_deriv.

(** ** [SinvJsem]: Judgment semantics for [sinv] *)
Notation SinvJsem FML Σ JUDG :=
  (Ejsem (sinv_judgty (FML $oi Σ)) JUDG (iProp Σ)).

Section sinv_deriv.
  Context `{!sinvGS FML Σ, !SinvJudg (FML $oi Σ) JUDG, !Jsem JUDG (iProp Σ),
    !Dsem JUDG (FML $oi Σ) (iProp Σ), !SinvJsem FML Σ JUDG}.
  Implicit Type Px Qx : FML $oi Σ.

  (** Access [sinv] *)
  Lemma sinv_acc {Px} :
    sinvd Px -∗ sinv_wsat ⟦⟧ ==∗ (⟦ Px ⟧ ∗ (⟦ Px ⟧ ==∗ sinv_wsat ⟦⟧)).
  Proof.
    rewrite sinv_unseal. iIntros "[%Qx[QPQ s]] W".
    iDestruct (der_sound with "QPQ") as "QPQ". rewrite sem_ejudg /=.
    iDestruct (sinv_tok_acc with "s W") as "[Qx cl]".
    iMod ("QPQ" with "Qx") as "[$ PQx]". iIntros "!> Px".
    iMod ("PQx" with "Px") as "Qx". iModIntro. by iApply "cl".
  Qed.

  Context `{!Deriv (JUDG:=JUDG) ih δ}.

  (** Turn [sinv_tok] into [sinv] *)
  Lemma sinv_tok_sinv {Px} : sinv_tok Px ⊢ sinv δ Px.
  Proof.
    rewrite sinv_unseal. iIntros "$ !>". iApply Deriv_factor. iIntros (? _ _ _).
    rewrite sem_ejudg. iApply (mod_acsr_refl (M:=bupd)).
  Qed.

  (** Allocate [sinv] *)
  Lemma sinv_alloc Px :
    sinv_wsat ⟦⟧(δ) ==∗ sinv δ Px ∗ (⟦ Px ⟧(δ) -∗ sinv_wsat ⟦⟧(δ)).
  Proof. rewrite -sinv_tok_sinv. exact: sinv_tok_alloc. Qed.

  (** Convert [sinv] with [mod_acsr] *)
  Lemma sinv_acsr {Px Qx} :
    □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      mod_acsr bupd ⟦ Px ⟧(δ') ⟦ Qx ⟧(δ')) -∗
      sinv δ Px -∗ sinv δ Qx.
  Proof.
    rewrite sinv_unseal. iIntros "#PQP [%R[#RPR $]] !>". iApply Deriv_factor.
    iIntros (??? to). rewrite sem_ejudg.
    iApply (mod_acsr_trans (M:=bupd)). { by rewrite to sem_ejudg. }
    by iApply "PQP".
  Qed.

  (** Split [sinv] over [∗] *)
  Local Lemma sinv_sep' {PQx Px Qx} :
    (∀ δ', ⟦ PQx ⟧(δ') ≡ (⟦ Px ⟧(δ') ∗ ⟦ Qx ⟧(δ'))%I) → sinv δ PQx ⊢ sinv δ Px.
  Proof.
    move=> eq. iApply sinv_acsr. iIntros "!>" (????). rewrite eq.
    iApply (mod_acsr_sep_l (M:=bupd)).
  Qed.
  Lemma sinv_sep {PQx Px Qx} :
    (∀ δ', ⟦ PQx ⟧(δ') ≡ (⟦ Px ⟧(δ') ∗ ⟦ Qx ⟧(δ'))%I) →
    sinv δ PQx ⊢ sinv δ Px ∗ sinv δ Qx.
  Proof.
    iIntros (eq) "#s". iSplit; [by iApply sinv_sep'|].
    iApply (sinv_sep' with "s"). iIntros (?). by rewrite eq comm.
  Qed.
End sinv_deriv.
