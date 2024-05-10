(** * Relaxed [sinv] with [deriv] *)

From nola.iris Require Export util deriv sinv.
From iris.proofmode Require Import proofmode.
Import PintpNotation DerivNotation.

(** Derivability data for [sinv] *)
Class DerivSinv {PROP Σ} (JUDG : judg (iProp Σ)) := DERIV_SINV {
  deriv_sinv_intp ::
    Pintp (deriv JUDG (iProp Σ)) (PROP $o iProp Σ) (iProp Σ);
  deriv_sinv_ne {δ} :: NonExpansive (deriv_sinv_intp δ);
  deriv_sinv_acsr : PROP $o iProp Σ → PROP $o iProp Σ → JUDG;
  deriv_sinv_mod : iProp Σ → iProp Σ;
  deriv_sinv_mod_gen_upd :: GenUpd deriv_sinv_mod;
  deriv_sinv_acsr_intp {δ P Q} :
    ⟦ deriv_sinv_acsr P Q ⟧(δ) ≡ acsr deriv_sinv_mod ⟦ P ⟧(δ) ⟦ Q ⟧(δ);
}.
(** Notation *)
Notation sinv_wsatd δ := (sinv_wsat ⟦⟧(δ)).

Section sinv_deriv.
  Context `{!sinvGS PROP Σ, !DerivSinv (PROP:=PROP) (Σ:=Σ) JUDG}.
  Implicit Type P Q : PROP $o iProp Σ.

  (** [sinv]: Relaxed simple invariant *)
  Definition sinv δ P : iProp Σ :=
    ∃ Q, □ ⸨ deriv_sinv_acsr P Q ⸩(δ) ∗ sinv_tok Q.

  (** [sinv] is persistent *)
  Fact sinv_persistent {δ P} : Persistent (sinv δ P).
  Proof. exact _. Qed.

  (** Access [sinv] *)
  Lemma sinv_acc {P} :
    sinv der P -∗ sinv_wsatd der -∗ deriv_sinv_mod
      (⟦ P ⟧(der) ∗ (⟦ P ⟧(der) -∗ deriv_sinv_mod (sinv_wsatd der))).
  Proof.
    iIntros "[%Q[QPQ s]] W". iDestruct (der_sound with "QPQ") as "QPQ".
    rewrite deriv_sinv_acsr_intp.
    iDestruct (sinv_tok_acc with "s W") as "[Q cl]".
    iMod ("QPQ" with "Q") as "[$ PQ]". iIntros "!> P".
    iMod ("PQ" with "P") as "Q". iModIntro. by iApply "cl".
  Qed.

  Context `{!Deriv (JUDG:=JUDG) ih δ}.

  (** Turn [sinv_tok] into [sinv] *)
  Lemma sinv_tok_sinv {P} : sinv_tok P ⊢ sinv δ P.
  Proof.
    iIntros "$ !>". iApply Deriv_intro. iIntros (? _ _).
    rewrite deriv_sinv_acsr_intp. iApply acsr_refl.
  Qed.

  (** Allocate [sinv] *)
  Lemma sinv_alloc P : sinv_wsatd δ ==∗ sinv δ P ∗ (⟦ P ⟧(δ) -∗ sinv_wsatd δ).
  Proof. rewrite -sinv_tok_sinv. exact: sinv_tok_alloc. Qed.

  (** Convert [sinv] with [acsr] *)
  Lemma sinv_acsr' {P Q} : □ ⸨ deriv_sinv_acsr P Q ⸩(δ) -∗ sinv δ Q -∗ sinv δ P.
  Proof.
    iIntros "#QPQ [%R[#RQR $]] !>". iApply (Deriv_map2 with "[] QPQ RQR").
    iIntros (? _ _). rewrite !deriv_sinv_acsr_intp. iApply acsr_trans.
  Qed.
  Lemma sinv_acsr {P Q} :
    □ (∀ δ, acsr deriv_sinv_mod ⟦ P ⟧(δ) ⟦ Q ⟧(δ)) -∗ sinv δ Q -∗ sinv δ P.
  Proof.
    iIntros "#PQP". iApply sinv_acsr'. iModIntro. iApply Deriv_intro.
    iIntros (? _ _). rewrite deriv_sinv_acsr_intp. by iApply "PQP".
  Qed.

  (** Split [sinv] over [∗] *)
  Local Lemma sinv_sep' {PQ P Q} :
    (∀ δ, ⟦ PQ ⟧(δ) ≡ (⟦ P ⟧(δ) ∗ ⟦ Q ⟧(δ))%I) → sinv δ PQ ⊢ sinv δ P.
  Proof.
    move=> eq. iApply sinv_acsr. iIntros "!>" (?). unfold acsr. rewrite eq.
    iApply acsr_sep_l.
  Qed.
  Lemma sinv_sep {PQ P Q} : (∀ δ, ⟦ PQ ⟧(δ) ≡ (⟦ P ⟧(δ) ∗ ⟦ Q ⟧(δ))%I) →
    sinv δ PQ ⊢ sinv δ P ∗ sinv δ Q.
  Proof.
    iIntros (eq) "#s". iSplit; [by iApply sinv_sep'|].
    iApply (sinv_sep' with "s"). iIntros (?). by rewrite eq comm.
  Qed.
End sinv_deriv.
