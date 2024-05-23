(** * Relaxed [sinv] with [deriv] *)

From nola.bi Require Export deriv.
From nola.iris Require Export sinv.
From iris.proofmode Require Import proofmode.
Import iPropAppNotation PintpNotation IntpNotation UpdwNotation.

Implicit Type PRO JUDG : ofe.

(** Notation *)
Notation sinv_wsati δ := (sinv_wsat ⟦⟧(δ)).
Notation sinv_wsatid := (sinv_wsati der).

(** Derivability pre-data for [sinv] *)
Class SinvPreDeriv PRO JUDG := SINV_PRE_DERIV {
  sinv_jacsr : PRO → PRO → JUDG;
  sinv_jacsr_ne :: NonExpansive2 sinv_jacsr;
}.
Hint Mode SinvPreDeriv ! - : typeclass_instances.
Arguments SINV_PRE_DERIV {_ _} _ {_}.

Section sinv_deriv.
  Context `{!sinvGS PROP Σ, !SinvPreDeriv (PROP $oi Σ) JUDG}.
  Implicit Type δ : JUDG → iProp Σ.

  (** [sinv]: Relaxed simple invariant *)
  Local Definition sinv_def δ (P : PROP $oi Σ) : iProp Σ :=
    ∃ Q, □ δ (sinv_jacsr Q P) ∗ sinv_tok Q.
  Local Lemma sinv_aux : seal sinv_def. Proof. by eexists. Qed.
  Definition sinv := sinv_aux.(unseal).
  Local Lemma sinv_unseal : sinv = sinv_def. Proof. exact: seal_eq. Qed.

  (** [sinv] is persistent *)
  #[export] Instance sinv_persistent {δ P} : Persistent (sinv δ P).
  Proof. rewrite sinv_unseal. exact _. Qed.

  (** [sinv] is non-expansive *)
  #[export] Instance sinv_ne `{!NonExpansive δ} : NonExpansive (sinv δ).
  Proof. rewrite sinv_unseal. solve_proper. Qed.
End sinv_deriv.

Section sinv_deriv.
  Context `{!sinvGS PROP Σ,
    !SinvPreDeriv (PROP $oi Σ) (JUDGI : judgi (iProp Σ)),
    !Dintp JUDGI (PROP $oi Σ) (iProp Σ)}.
  Implicit Type (δ : JUDGI → iProp Σ) (P Q : PROP $oi Σ).

  (** Derivability data for [sinv] *)
  Class SinvDeriv := SINV_DERIV {
    sinv_mod : iProp Σ → iProp Σ;
    sinv_mod_gen_upd :: GenUpd sinv_mod;
    sinv_jacsr_intp {δ P Q} :
      ⟦ sinv_jacsr P Q ⟧(δ) ≡ acsr sinv_mod ⟦ P ⟧(δ) ⟦ Q ⟧(δ);
  }.

  Context `{!SinvDeriv}.

  (** Access [sinv] *)
  Lemma sinv_acc {P} :
    sinv der P -∗ sinv_wsatid -∗ sinv_mod
      (⟦ P ⟧ ∗ (⟦ P ⟧ -∗ sinv_mod (sinv_wsatid))).
  Proof.
    rewrite sinv_unseal. iIntros "[%Q[QPQ s]] W".
    iDestruct (der_sound with "QPQ") as "QPQ". rewrite sinv_jacsr_intp.
    iDestruct (sinv_tok_acc with "s W") as "[Q cl]".
    iMod ("QPQ" with "Q") as "[$ PQ]". iIntros "!> P".
    iMod ("PQ" with "P") as "Q". iModIntro. by iApply "cl".
  Qed.

  Context `{!Deriv (JUDGI:=JUDGI) ih δ}.

  (** Turn [sinv_tok] into [sinv] *)
  Lemma sinv_tok_sinv {P} : sinv_tok P ⊢ sinv δ P.
  Proof.
    rewrite sinv_unseal. iIntros "$ !>". iApply Deriv_to. iIntros (? _ _ _).
    rewrite sinv_jacsr_intp. iApply (acsr_refl (M:=sinv_mod)).
  Qed.

  (** Allocate [sinv] *)
  Lemma sinv_alloc P : sinv_wsati δ ==∗ sinv δ P ∗ (⟦ P ⟧(δ) -∗ sinv_wsati δ).
  Proof. rewrite -sinv_tok_sinv. exact: sinv_tok_alloc. Qed.

  (** Convert [sinv] with [acsr] *)
  Lemma sinv_acsr {P Q} :
    □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜∀ J, δ J ⊢ ⟦ J ⟧(δ')⌝ →
      acsr sinv_mod ⟦ P ⟧(δ') ⟦ Q ⟧(δ')) -∗
      sinv δ P -∗ sinv δ Q.
  Proof.
    rewrite sinv_unseal. iIntros "#PQP [%R[#RPR $]] !>". iApply Deriv_to.
    iIntros (??? to). rewrite sinv_jacsr_intp.
    iApply (acsr_trans (M:=sinv_mod)). { by rewrite to sinv_jacsr_intp. }
    by iApply "PQP".
  Qed.

  (** Split [sinv] over [∗] *)
  Local Lemma sinv_sep' {PQ P Q} :
    (∀ δ', ⟦ PQ ⟧(δ') ≡ (⟦ P ⟧(δ') ∗ ⟦ Q ⟧(δ'))%I) → sinv δ PQ ⊢ sinv δ P.
  Proof.
    move=> eq. iApply sinv_acsr. iIntros "!>" (????). unfold acsr. rewrite eq.
    iApply (acsr_sep_l (M:=sinv_mod)).
  Qed.
  Lemma sinv_sep {PQ P Q} : (∀ δ', ⟦ PQ ⟧(δ') ≡ (⟦ P ⟧(δ') ∗ ⟦ Q ⟧(δ'))%I) →
    sinv δ PQ ⊢ sinv δ P ∗ sinv δ Q.
  Proof.
    iIntros (eq) "#s". iSplit; [by iApply sinv_sep'|].
    iApply (sinv_sep' with "s"). iIntros (?). by rewrite eq comm.
  Qed.
End sinv_deriv.
Arguments SinvDeriv PROP Σ JUDGI {_ _}.
Hint Mode SinvDeriv ! - - - - : typeclass_instances.
