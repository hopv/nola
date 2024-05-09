(** * Relaxed [sinv] with [deriv] *)

From nola.iris Require Export util deriv sinv.
From iris.proofmode Require Import proofmode.
Import IntpNotation DerivNotation.

Section sinv_deriv.
  Context `{!sinvGS PROP Σ}.

  (** Derivability data for [sinv] *)
  Class DerivSinv (DER : derivst (iProp Σ)) := DERIV_SINV {
    deriv_sinv_intp : deriv_ty DER (iProp Σ) → PROP $o iProp Σ → iProp Σ;
    deriv_sinv_ne {δ} :: NonExpansive (deriv_sinv_intp δ);
    deriv_sinv_acsr : PROP $o iProp Σ → PROP $o iProp Σ → DER;
    deriv_sinv_mod : iProp Σ → iProp Σ;
    deriv_sinv_gen_upd :: GenUpd deriv_sinv_mod;
    deriv_sinv_acsr_intp {δ P Q} :
      ⟦ deriv_sinv_acsr P Q ⟧(δ) ≡
        acsr deriv_sinv_mod (deriv_sinv_intp δ P) (deriv_sinv_intp δ Q);
  }.
  Local Notation "⟦ P ⟧' ( δ )" := (deriv_sinv_intp δ P)
    (format "'[' ⟦  P  ⟧' '/  ' ( δ ) ']'") : nola_scope.
  Local Notation "⟦ P ⟧'" := (⟦ P ⟧'(der)).

  Context `{!DerivSinv DER}.

  (** Simple invariant *)
  Local Definition sinv_def δ P : iProp Σ :=
    ∃ Q, □ ⸨ deriv_sinv_acsr P Q ⸩(δ) ∗ sinv_tok Q.
  Local Lemma sinv_aux : seal sinv_def. Proof. by eexists. Qed.
  Definition sinv := sinv_aux.(unseal).
  Local Lemma sinv_unseal : sinv = sinv_def. Proof. exact: seal_eq. Qed.

  (** [sinv] is persistent *)
  #[export] Instance sinv_persistent {δ P} : Persistent (sinv δ P).
  Proof. rewrite sinv_unseal. exact _. Qed.

  (** World satisfaction *)
  Definition sinv_wsatd δ := sinv_wsat (deriv_sinv_intp δ).

  (** Access [sinv] *)
  Lemma sinv_acc {P} :
    sinv der P -∗ sinv_wsatd der -∗
      deriv_sinv_mod (⟦ P ⟧' ∗ (⟦ P ⟧' -∗ deriv_sinv_mod (sinv_wsatd der))).
  Proof.
    rewrite sinv_unseal. iIntros "[%Q[QPQ s]] W".
    iDestruct (der_sound with "QPQ") as "QPQ". rewrite deriv_sinv_acsr_intp.
    iDestruct (sinv_tok_acc with "s W") as "[Q cl]".
    iMod ("QPQ" with "Q") as "[$ PQ]". iIntros "!> P".
    iMod ("PQ" with "P") as "Q". iModIntro. by iApply "cl".
  Qed.

  Context `{!Deriv (DER:=DER) ih δ}.

  (** Turn [sinv_tok] into [sinv] *)
  Local Lemma sinv_tok_sinv {P} : sinv_tok P ⊢ sinv δ P.
  Proof.
    rewrite sinv_unseal. iIntros "$ !>". iApply Deriv_intro. iIntros (? _ _).
    rewrite deriv_sinv_acsr_intp. iApply acsr_refl.
  Qed.
  (** Allocate [sinv] *)
  Lemma sinv_alloc P : sinv_wsatd δ ==∗ sinv δ P ∗ (⟦ P ⟧'(δ) -∗ sinv_wsatd δ).
  Proof. rewrite -sinv_tok_sinv. exact: sinv_tok_alloc. Qed.

  (** Transform [sinv] *)
  Lemma sinv_acsr {P Q} : □ ⸨ deriv_sinv_acsr P Q ⸩(δ) -∗ sinv δ Q -∗ sinv δ P.
  Proof.
    rewrite sinv_unseal. iIntros "#QPQ [%R[#RQR $]] !>".
    iApply (Deriv_map2 with "[] QPQ RQR"). iIntros (? _ _).
    rewrite !deriv_sinv_acsr_intp. iApply acsr_trans.
  Qed.

  (** Split [sinv] over [∗] *)
  Local Lemma sinv_sep' {PQ P Q} :
    (∀ δ, ⟦ PQ ⟧'(δ) ≡ (⟦ P ⟧'(δ) ∗ ⟦ Q ⟧'(δ))%I) →
    sinv δ PQ -∗ sinv δ P.
  Proof.
    move=> eq. iApply sinv_acsr. iModIntro. iApply Deriv_intro.
    iIntros (? _ _). rewrite deriv_sinv_acsr_intp. unfold acsr. rewrite !eq.
    iApply acsr_sep_l.
  Qed.
  Lemma sinv_sep {PQ P Q} : (∀ δ, ⟦ PQ ⟧'(δ) ≡ (⟦ P ⟧'(δ) ∗ ⟦ Q ⟧'(δ))%I) →
    sinv δ PQ -∗ sinv δ P ∗ sinv δ Q.
  Proof.
    iIntros (eq) "#s". iSplit; [by iApply sinv_sep'|].
    iApply (sinv_sep' with "s"). iIntros (?). by rewrite eq comm.
  Qed.
End sinv_deriv.
