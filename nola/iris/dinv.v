(** * Direct invariants *)

From nola.bi Require Export internal modw.
From nola.iris Require Export iprop.
From nola.iris Require Import sinv.
From iris.proofmode Require Import proofmode.
Import iPropAppNotation ModwNotation.

Implicit Type (FML : oFunctor) (i : positive).

(** Ghost state for direct invariants *)
Class dinvGpreS FML Σ := dinvGpreS_sinv : sinvGpreS FML Σ.
Local Existing Instance dinvGpreS_sinv.
Class dinvGS FML Σ := dinvGS_sinv : sinvGS FML Σ.
Local Existing Instance dinvGS_sinv.
Definition dinvΣ FML `{!oFunctorContractive FML} := sinvΣ FML.
#[export] Instance subG_dinvΣ
  `{!oFunctorContractive FML, !subG (dinvΣ FML) Σ} : dinvGpreS FML Σ.
Proof. solve_inG. Qed.

Section dinv.
  Context `{!dinvGS FML Σ}.
  Implicit Type Px : FML $oi Σ.

  (** [dinv_tok]: Direct invariant token *)
  Local Definition dinv_tok_def (Px : FML $oi Σ) : iProp Σ :=
    ∃ i, sinv_tok i Px.
  Local Definition dinv_tok_aux : seal dinv_tok_def. Proof. by eexists. Qed.
  Definition dinv_tok := dinv_tok_aux.(unseal).
  Local Lemma dinv_tok_unseal : dinv_tok = dinv_tok_def.
  Proof. exact: seal_eq. Qed.

  (** [dinv_tok] is non-expansive *)
  #[export] Instance dinv_tok_ne : NonExpansive dinv_tok.
  Proof. rewrite dinv_tok_unseal. solve_proper. Qed.
  #[export] Instance dinv_tok_proper : Proper ((≡) ==> (⊣⊢)) dinv_tok.
  Proof. apply ne_proper, _. Qed.
  (** [dinv_tok] is persistent *)
  #[export] Instance dinv_tok_persistent {Px} : Persistent (dinv_tok Px).
  Proof. rewrite dinv_tok_unseal. exact _. Qed.
  (** [dinv_tok] is timeless for discrete formulas *)
  #[export] Instance dinv_tok_timeless `{!Discrete Px} : Timeless (dinv_tok Px).
  Proof. rewrite dinv_tok_unseal. exact _. Qed.

  (** World satisfaction *)
  Local Definition dinv_wsat_def (sm : FML $oi Σ -d> iProp Σ) : iProp Σ :=
    sinv_wsat (λ _, sm).
  Local Definition dinv_wsat_aux : seal dinv_wsat_def. Proof. by eexists. Qed.
  Definition dinv_wsat := dinv_wsat_aux.(unseal).
  Local Lemma dinv_wsat_unseal : dinv_wsat = dinv_wsat_def.
  Proof. exact: seal_eq. Qed.

  (** [dinv_wsat] is non-expansive *)
  #[export] Instance dinv_wsat_ne : NonExpansive dinv_wsat.
  Proof. rewrite dinv_wsat_unseal. solve_proper. Qed.
  #[export] Instance dinv_wsat_proper : Proper ((≡) ==> (≡)) dinv_wsat.
  Proof. apply ne_proper, _. Qed.

  (** [dinv_wsat] is timeless if [sm] is always timeless
    and the underlying ofe is discrete *)
  #[export] Instance dinv_wsat_timeless
    `{!OfeDiscrete (FML $oi Σ), !∀ Px, Timeless (sm Px)} :
    Timeless (dinv_wsat sm).
  Proof. rewrite dinv_wsat_unseal. exact _. Qed.

  (** Allocate [dinv_tok] suspending the world satisfaction *)
  Lemma dinv_tok_alloc_suspend {sm} Px :
    dinv_wsat sm ==∗ dinv_tok Px ∗ (sm Px -∗ dinv_wsat sm).
  Proof.
    rewrite dinv_tok_unseal dinv_wsat_unseal. iIntros "W".
    iDestruct (sinv_tok_alloc_suspend Px with "W") as (I) "big".
    iMod ("big" $! (fresh I) with "[%]") as "[#inv →W]". { apply is_fresh. }
    iModIntro. iFrame "inv". iIntros "?". by iApply "→W".
  Qed.
  (** Allocate [dinv_tok] *)
  Lemma dinv_tok_alloc {sm} Px : sm Px =[dinv_wsat sm]=∗ dinv_tok Px.
  Proof.
    iIntros "? W". iMod (dinv_tok_alloc_suspend with "W") as "[$ →W]".
    iModIntro. by iApply "→W".
  Qed.

  (** Access the content of [dinv_tok] *)
  Lemma dinv_tok_acc {sm Px} :
    dinv_tok Px -∗ dinv_wsat sm -∗ sm Px ∗ (sm Px -∗ dinv_wsat sm).
  Proof.
    rewrite dinv_tok_unseal dinv_wsat_unseal. iIntros "[% i] W".
    iDestruct (sinv_tok_acc with "i W") as "[$$]".
  Qed.
  (** Access the content of [dinv_tok] for persistent propositions *)
  Lemma dinv_tok_acc_persistent {sm Px} : Persistent (sm Px) →
    dinv_tok Px -∗[dinv_wsat sm] sm Px.
  Proof.
    iIntros (?) "i W". iDestruct (dinv_tok_acc with "i W") as "[#Px cl]".
    iFrame "Px". by iApply "cl".
  Qed.
End dinv.

(** Allocate [dinv_wsat] *)
Lemma dinv_wsat_alloc `{!dinvGpreS FML Σ} :
  ⊢ |==> ∃ _ : dinvGS FML Σ, ∀ sm, internal_ne sm -∗ dinv_wsat sm.
Proof.
  iMod sinv_wsat_alloc as (γ) "W". iModIntro. iExists _. iIntros (?) "Ne".
  rewrite dinv_wsat_unseal. iApply "W". by iIntros.
Qed.
