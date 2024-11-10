(** * Simple invariants *)

From nola.bi Require Export internal modw.
From nola.iris Require Export iprop.
From iris.algebra Require Import agree gmap_view.
From iris.base_logic.lib Require Export own.
From iris.proofmode Require Import proofmode.
Import iPropAppNotation.

Implicit Type FML : oFunctor.

(** Ghost state for simple invariants *)
Class sinvGpreS FML Σ : Type :=
  sinvGpreS_in : inG Σ (gmap_viewR positive (agreeR (FML $oi Σ))).
Local Existing Instance sinvGpreS_in.
Class sinvGS FML Σ : Type := SinvGS {
  sinvGS_pre : sinvGpreS FML Σ;
  sinv_name : gname;
}.
Local Existing Instance sinvGS_pre.
Definition sinvΣ FML `{!oFunctorContractive FML} : gFunctors :=
  GFunctor (gmap_viewRF positive (agreeRF FML)).
#[export] Instance subG_sinvΣ
  `{!oFunctorContractive FML, !subG (sinvΣ FML) Σ} : sinvGpreS FML Σ.
Proof. solve_inG. Qed.

Section sinv.
  Context `{!sinvGS FML Σ}.
  Implicit Type (Px : FML $oi Σ) (sm : positive → FML $oi Σ → iProp Σ)
    (i : positive).

  (** Simple invariant token *)
  Local Definition sinv_tok_def i Px : iProp Σ :=
    own sinv_name (gmap_view_frag i DfracDiscarded (to_agree Px)).
  Local Lemma sinv_tok_aux : seal sinv_tok_def. Proof. by eexists. Qed.
  Definition sinv_tok := sinv_tok_aux.(unseal).
  Local Lemma sinv_tok_unseal : sinv_tok = sinv_tok_def.
  Proof. exact: seal_eq. Qed.

  (** Authoritative token *)
  Local Definition sinv_auth_tok M :=
    own sinv_name (gmap_view_auth (DfracOwn 1) (to_agree <$> M)).
  (** World satisfaction *)
  Definition sinv_wsat_def sm : iProp Σ :=
    (∀ i, internal_ne (sm i)) ∗
    ∃ M, sinv_auth_tok M ∗ [∗ map] i ↦ Px ∈ M, sm i Px.
  Local Lemma sinv_wsat_aux : seal sinv_wsat_def. Proof. by eexists. Qed.
  Definition sinv_wsat := sinv_wsat_aux.(unseal).
  Local Lemma sinv_wsat_unseal : sinv_wsat = sinv_wsat_def.
  Proof. exact: seal_eq. Qed.

  (** [sinv_tok] is non-expansive *)
  #[export] Instance sinv_tok_ne {i} : NonExpansive (sinv_tok i).
  Proof. rewrite sinv_tok_unseal. solve_proper. Qed.
  #[export] Instance sinv_tok_proper {i} : Proper ((≡) ==> (⊣⊢)) (sinv_tok i).
  Proof. apply ne_proper, _. Qed.
  (** [sinv_tok] is persistent *)
  #[export] Instance sinv_tok_persistent {i Px} : Persistent (sinv_tok i Px).
  Proof. rewrite sinv_tok_unseal. exact _. Qed.
  (** [sinv_tok] is timeless for discrete formulas *)
  #[export] Instance sinv_tok_timeless `{!Discrete Px} {i} :
    Timeless (sinv_tok i Px).
  Proof. rewrite sinv_tok_unseal /sinv_tok_def /gmap_view_frag. exact _. Qed.

  (** [sinv_wsat] is non-expansive *)
  #[export] Instance sinv_wsat_ne {n} :
    Proper (pointwise_relation _ (pointwise_relation _ (≡{n}≡)) ==> (≡{n}≡))
      sinv_wsat.
  Proof.
    rewrite sinv_wsat_unseal /sinv_wsat_def=> ?? eqv. repeat f_equiv. apply eqv.
  Qed.
  #[export] Instance sinv_wsat_proper :
    Proper (pointwise_relation _ (pointwise_relation _ (≡)) ==> (≡))
      sinv_wsat.
  Proof.
    rewrite sinv_wsat_unseal /sinv_wsat_def=> ?? eqv. repeat f_equiv. apply eqv.
  Qed.

  (** [sinv_wsat] is timeless if [sm] is always timeless
    and the underlying ofe is discrete *)
  #[export] Instance sinv_wsat_timeless
    `{!OfeDiscrete (FML $oi Σ), !∀ i Px, Timeless (sm i Px)} :
    Timeless (sinv_wsat sm).
  Proof. rewrite sinv_wsat_unseal. exact _. Qed.

  (** Lemma for [sinv_tok_alloc_suspend] *)
  Local Lemma sinv_auth_tok_alloc {M i Px} : i ∉ dom M →
    sinv_auth_tok M ==∗ sinv_auth_tok (<[i:=Px]> M) ∗ sinv_tok i Px.
  Proof.
    move=> /not_elem_of_dom eq. iIntros "●". rewrite sinv_tok_unseal -own_op.
    iApply own_update; [|done]. rewrite fmap_insert.
    apply gmap_view_alloc; [|done..]. by rewrite lookup_fmap eq.
  Qed.
  (** Allocate [sinv_tok] suspending the world satisfaction *)
  Lemma sinv_tok_alloc_suspend {sm} Px :
    sinv_wsat sm -∗ ∃ I : gset positive, ∀ i, ⌜i ∉ I⌝ ==∗
      sinv_tok i Px ∗ (sm i Px -∗ sinv_wsat sm).
  Proof.
    rewrite sinv_wsat_unseal. iIntros "[Ne[%M[● M]]]". iExists (dom M).
    iIntros (i ?). iMod (sinv_auth_tok_alloc with "●") as "[● #i]"; [done|].
    iModIntro. iSplitR; [by rewrite sinv_tok_unseal|]. iIntros "Px".
    iFrame "Ne ●". iApply (big_sepM_insert_2 with "Px M").
  Qed.

  (** Lemma for [sinv_tok_acc] *)
  Local Lemma sinv_auth_tok_lookup {M i Px} :
    sinv_auth_tok M -∗ sinv_tok i Px -∗ ∃ Px', ⌜M !! i = Some Px'⌝ ∧ Px ≡ Px'.
  Proof.
    rewrite sinv_tok_unseal. iIntros "● i".
    iDestruct (own_valid_2 with "● i") as "✓".
    rewrite gmap_view_both_validI_total. iDestruct "✓" as (? _ _ eq) "[_ in]".
    move: eq. rewrite lookup_fmap. case: (M !! i); [|done]=> Px' [<-].
    iExists Px'. iSplit; [done|]. by rewrite to_agree_includedI.
  Qed.
  (** Access via [sinv_tok] *)
  Lemma sinv_tok_acc {i sm Px} :
    sinv_tok i Px -∗ sinv_wsat sm -∗ sm i Px ∗ (sm i Px -∗ sinv_wsat sm).
  Proof.
    rewrite sinv_wsat_unseal. iIntros "i [#Ne[%M[● M]]]".
    iDestruct (sinv_auth_tok_lookup with "● i") as (Px' eq) "#≡".
    iRewrite ("Ne" $! i with "≡").
    iDestruct (big_sepM_lookup_acc with "M") as "[$ →M]"; [done|]. iIntros "Px".
    iFrame "Ne ●". by iApply "→M".
  Qed.
End sinv.

(** Lemma for [sinv_wsat_alloc] *)
Local Lemma sinv_auth_tok_alloc_empty `{!sinvGpreS FML Σ} :
  ⊢ |==> ∃ _ : sinvGS FML Σ, sinv_auth_tok ∅.
Proof.
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅)) as (γ) "●".
  { apply gmap_view_auth_valid. } { iModIntro. by iExists (SinvGS _ _ _ γ). }
Qed.
(** Allocate [sinv_wsat] *)
Lemma sinv_wsat_alloc `{!sinvGpreS FML Σ} :
  ⊢ |==> ∃ _ : sinvGS FML Σ, ∀ sm, (∀ i, internal_ne (sm i)) -∗ sinv_wsat sm.
Proof.
  iMod sinv_auth_tok_alloc_empty as (?) "●". iModIntro. iExists _.
  iIntros (?) "Ne". rewrite sinv_wsat_unseal. by iFrame.
Qed.
