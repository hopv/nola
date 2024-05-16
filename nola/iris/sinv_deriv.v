(** * Relaxed [sinv] with [deriv] *)

From nola.bi Require Export deriv.
From nola.iris Require Export sinv.
From iris.proofmode Require Import proofmode.
Import iPropAppNotation PintpNotation UpdwNotation.

(** Notation *)
Notation sinv_wsatd δ := (sinv_wsat ⟦⟧(δ)).

(** Derivability pre-data for [sinv] *)
Class SinvPreDeriv PRO JUD := sinv_jacsr : PRO → PRO → JUD.
Hint Mode SinvPreDeriv ! - : typeclass_instances.

Section sinv_deriv.
  Context `{!sinvGS PROP Σ, !SinvPreDeriv (PROP $oi Σ) JUD}.

  (** [sinv]: Relaxed simple invariant *)
  Definition sinv (δ : JUD → _) (P : PROP $oi Σ) : iProp Σ :=
    ∃ Q, □ δ (sinv_jacsr P Q) ∗ sinv_tok Q.

  (** [sinv] is persistent *)
  Fact sinv_persistent {δ P} : Persistent (sinv δ P).
  Proof. exact _. Qed.
End sinv_deriv.

Section sinv_deriv.
  Context `{!sinvGS PROP Σ, !SinvPreDeriv (PROP $oi Σ) (JUDG : judg (iProp Σ)),
    !Dintp JUDG (PROP $oi Σ) (iProp Σ)}.
  Implicit Type P Q : PROP $oi Σ.

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
    sinv der P -∗ sinv_wsatd der -∗ sinv_mod
      (⟦ P ⟧(der) ∗ (⟦ P ⟧(der) -∗ sinv_mod (sinv_wsatd der))).
  Proof.
    iIntros "[%Q[QPQ s]] W". iDestruct (der_sound with "QPQ") as "QPQ".
    rewrite sinv_jacsr_intp.
    iDestruct (sinv_tok_acc with "s W") as "[Q cl]".
    iMod ("QPQ" with "Q") as "[$ PQ]". iIntros "!> P".
    iMod ("PQ" with "P") as "Q". iModIntro. by iApply "cl".
  Qed.

  Context `{!Deriv (JUDG:=JUDG) ih δ}.

  (** Turn [sinv_tok] into [sinv] *)
  Lemma sinv_tok_sinv {P} : sinv_tok P ⊢ sinv δ P.
  Proof.
    iIntros "$ !>". iApply Deriv_to. iIntros (? _ _ _).
    rewrite sinv_jacsr_intp. iApply acsr_refl.
  Qed.

  (** Allocate [sinv] *)
  Lemma sinv_alloc P : sinv_wsatd δ ==∗ sinv δ P ∗ (⟦ P ⟧(δ) -∗ sinv_wsatd δ).
  Proof. rewrite -sinv_tok_sinv. exact: sinv_tok_alloc. Qed.

  (** Convert [sinv] with [acsr] *)
  Lemma sinv_acsr' {P Q} : □ δ (sinv_jacsr P Q) -∗ sinv δ Q -∗ sinv δ P.
  Proof.
    iIntros "#QPQ [%R[#RQR $]] !>". iApply (Deriv_map2 with "[] QPQ RQR").
    iIntros (? _ _). rewrite !sinv_jacsr_intp. iApply acsr_trans.
  Qed.
  Lemma sinv_acsr {P Q} :
    □ (∀ δ, acsr sinv_mod ⟦ P ⟧(δ) ⟦ Q ⟧(δ)) -∗ sinv δ Q -∗ sinv δ P.
  Proof.
    iIntros "#PQP". iApply sinv_acsr'. iModIntro. iApply Deriv_to.
    iIntros (? _ _ _). rewrite sinv_jacsr_intp. by iApply "PQP".
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
Arguments SinvDeriv PROP Σ JUDG {_ _}.
Hint Mode SinvDeriv ! - - - - : typeclass_instances.
