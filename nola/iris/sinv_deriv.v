(** * Simple invariant machinery relaxed with derivability *)

From nola.bi Require Export deriv.
From nola.iris Require Export sinv.
From iris.proofmode Require Import proofmode.
Import iPropAppNotation PsemNotation SemNotation UpdwNotation.

(** Notation *)
Notation sinv_wsati δ := (sinv_wsat ⟦⟧(δ)).
Notation sinv_wsatid := (sinv_wsati der).

(** Derivability pre-data for [sinv] *)
Class SinvPreDeriv (FM JUDG : ofe) := SINV_PRE_DERIV {
  (** Accessor judgment *)
  sinv_jacsr : FM → FM → JUDG;
  (** [sinv_jacsr] is non-expansive *)
  sinv_jacsr_ne :: NonExpansive2 sinv_jacsr;
}.
Hint Mode SinvPreDeriv ! - : typeclass_instances.
Arguments SINV_PRE_DERIV {_ _} _ {_}.

Section sinv_deriv.
  Context `{!sinvGS FML Σ, !SinvPreDeriv (FML $oi Σ) JUDG}.
  Implicit Type δ : JUDG → iProp Σ.

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
  #[export] Instance sinv_ne `{!NonExpansive δ} : NonExpansive (sinv δ).
  Proof. rewrite sinv_unseal. solve_proper. Qed.
  #[export] Instance sinv_proper `{!NonExpansive δ} :
    Proper ((≡) ==> (⊣⊢)) (sinv δ).
  Proof. apply ne_proper, _. Qed.
End sinv_deriv.
Notation sinvd := (sinv der).

Section sinv_deriv.
  Context `{!SinvPreDeriv (FML $oi Σ) (JUDGI : judgi (iProp Σ)),
    !Dsem JUDGI (FML $oi Σ) (iProp Σ)}.
  Implicit Type (δ : JUDGI → iProp Σ) (Px Qx : FML $oi Σ).

  (** Derivability data for [sinv] *)
  Class SinvDeriv := SINV_DERIV {
    (** Modality for accessing the simple invariant *)
    sinv_mod : iProp Σ → iProp Σ;
    (** [sinv_mod] is [GenUpd] *)
    sinv_mod_gen_upd :: GenUpd sinv_mod;
    (** Interpreting [sinv_jacsr] *)
    sinv_jacsr_sem {δ Px Qx} :
      ⟦ sinv_jacsr Px Qx ⟧(δ) ⊣⊢ mod_acsr sinv_mod ⟦ Px ⟧(δ) ⟦ Qx ⟧(δ);
  }.

  Context `{!sinvGS FML Σ, !SinvDeriv}.

  (** Access [sinv] *)
  Lemma sinv_acc {Px} :
    sinvd Px -∗ sinv_wsatid -∗ sinv_mod
      (⟦ Px ⟧ ∗ (⟦ Px ⟧ -∗ sinv_mod (sinv_wsatid))).
  Proof.
    rewrite sinv_unseal. iIntros "[%Qx[QPQ s]] W".
    iDestruct (der_sound with "QPQ") as "QPQ". rewrite sinv_jacsr_sem.
    iDestruct (sinv_tok_acc with "s W") as "[Qx cl]".
    iMod ("QPQ" with "Qx") as "[$ PQx]". iIntros "!> Px".
    iMod ("PQx" with "Px") as "Qx". iModIntro. by iApply "cl".
  Qed.

  Context `{!Deriv (JUDGI:=JUDGI) ih δ}.

  (** Turn [sinv_tok] into [sinv] *)
  Lemma sinv_tok_sinv {Px} : sinv_tok Px ⊢ sinv δ Px.
  Proof.
    rewrite sinv_unseal. iIntros "$ !>". iApply Deriv_factor. iIntros (? _ _ _).
    rewrite sinv_jacsr_sem. iApply (mod_acsr_refl (M:=sinv_mod)).
  Qed.

  (** Allocate [sinv] *)
  Lemma sinv_alloc Px : sinv_wsati δ ==∗ sinv δ Px ∗ (⟦ Px ⟧(δ) -∗ sinv_wsati δ).
  Proof. rewrite -sinv_tok_sinv. exact: sinv_tok_alloc. Qed.

  (** Convert [sinv] with [mod_acsr] *)
  Lemma sinv_acsr {Px Qx} :
    □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      mod_acsr sinv_mod ⟦ Px ⟧(δ') ⟦ Qx ⟧(δ')) -∗
      sinv δ Px -∗ sinv δ Qx.
  Proof.
    rewrite sinv_unseal. iIntros "#PQP [%R[#RPR $]] !>". iApply Deriv_factor.
    iIntros (??? to). rewrite sinv_jacsr_sem.
    iApply (mod_acsr_trans (M:=sinv_mod)). { by rewrite to sinv_jacsr_sem. }
    by iApply "PQP".
  Qed.

  (** Split [sinv] over [∗] *)
  Local Lemma sinv_sep' {PQx Px Qx} :
    (∀ δ', ⟦ PQx ⟧(δ') ≡ (⟦ Px ⟧(δ') ∗ ⟦ Qx ⟧(δ'))%I) → sinv δ PQx ⊢ sinv δ Px.
  Proof.
    move=> eq. iApply sinv_acsr. iIntros "!>" (????). rewrite eq.
    iApply (mod_acsr_sep_l (M:=sinv_mod)).
  Qed.
  Lemma sinv_sep {PQx Px Qx} :
    (∀ δ', ⟦ PQx ⟧(δ') ≡ (⟦ Px ⟧(δ') ∗ ⟦ Qx ⟧(δ'))%I) →
    sinv δ PQx ⊢ sinv δ Px ∗ sinv δ Qx.
  Proof.
    iIntros (eq) "#s". iSplit; [by iApply sinv_sep'|].
    iApply (sinv_sep' with "s"). iIntros (?). by rewrite eq comm.
  Qed.
End sinv_deriv.
Arguments SinvDeriv FML Σ JUDGI {_ _}.
Hint Mode SinvDeriv ! - - - - : typeclass_instances.
