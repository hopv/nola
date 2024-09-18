(** * Simple invariant *)

From nola.bi Require Export updw.
From nola.iris Require Export iprop.
From iris.algebra Require Import agree gmap_view.
From iris.base_logic.lib Require Export own.
From iris.proofmode Require Import proofmode.
Import iPropAppNotation.

Implicit Type FML : oFunctor.

Class sinvGpreS FML Σ :=
  sinvGpreS_in : inG Σ (gmap_viewR positive (agreeR (FML $oi Σ))).
Local Existing Instance sinvGpreS_in.
Class sinvGS FML Σ := SinvGS {
  sinvGS_pre : sinvGpreS FML Σ;
  sinv_name : gname;
}.
Local Existing Instance sinvGS_pre.
Definition sinvΣ FML `{!oFunctorContractive FML} :=
  #[GFunctor (gmap_viewRF positive (agreeRF FML))].
#[export] Instance subG_sinvΣ
  `{!oFunctorContractive FML, !subG (sinvΣ FML) Σ} : sinvGpreS FML Σ.
Proof. solve_inG. Qed.

Section sinv.
  Context `{!sinvGS FML Σ}.
  Implicit Type Px : FML $oi Σ.

  (** Simple invariant token *)
  Local Definition sinv_itok_def i Px : iProp Σ :=
    own sinv_name (gmap_view_frag i DfracDiscarded (to_agree Px)).
  Local Lemma sinv_itok_aux : seal sinv_itok_def. Proof. by eexists. Qed.
  Definition sinv_itok := sinv_itok_aux.(unseal).
  Local Lemma sinv_itok_unseal : sinv_itok = sinv_itok_def.
  Proof. exact: seal_eq. Qed.

  (** Simple invariant token with the index hidden *)
  Definition sinv_tok Px : iProp Σ := ∃ i, sinv_itok i Px.

  (** Authoritative token *)
  Local Definition sinv_auth_tok M :=
    own sinv_name (gmap_view_auth (DfracOwn 1) (to_agree <$> M)).
  (** World satisfaction *)
  Definition sinv_iwsat_def sm : iProp Σ :=
    ∃ M, sinv_auth_tok M ∗ [∗ map] i ↦ Px ∈ M, sm i Px.
  Local Lemma sinv_iwsat_aux : seal sinv_iwsat_def. Proof. by eexists. Qed.
  Definition sinv_iwsat := sinv_iwsat_aux.(unseal).
  Local Lemma sinv_iwsat_unseal : sinv_iwsat = sinv_iwsat_def.
  Proof. exact: seal_eq. Qed.
End sinv.
(** World satisfaction whose semantics ignores the index *)
Notation sinv_wsat' FML sm := (sinv_iwsat (FML:=FML) (λ _, sm)).
Notation sinv_wsat sm := (sinv_wsat' _ sm).

Section sinv.
  Context `{!sinvGS FML Σ}.
  Implicit Type Px : FML $oi Σ.
  Implicit Type (i : positive) (I : gset positive).

  (** [sinv_itok] and [sinv_tok] are non-expansive *)
  #[export] Instance sinv_itok_ne {i} : NonExpansive (sinv_itok i).
  Proof. rewrite sinv_itok_unseal. solve_proper. Qed.
  #[export] Instance sinv_itok_proper {i} : Proper ((≡) ==> (⊣⊢)) (sinv_itok i).
  Proof. apply ne_proper, _. Qed.
  #[export] Instance sinv_tok_ne : NonExpansive sinv_tok.
  Proof. solve_proper. Qed.
  #[export] Instance sinv_tok_proper: Proper ((≡) ==> (⊣⊢)) sinv_tok.
  Proof. solve_proper. Qed.
  (** [sinv_itok] and [sinv_tok] are persistent *)
  #[export] Instance sinv_itok_persistent {i Px} : Persistent (sinv_itok i Px).
  Proof. rewrite sinv_itok_unseal. exact _. Qed.
  Fact sinv_tok_persistent {Px} : Persistent (sinv_tok Px).
  Proof. exact _. Qed.
  (** [sinv_itok] and [sinv_tok] are timeless for discrete formulas *)
  #[export] Instance sinv_itok_timeless `{!Discrete Px} {i} :
    Timeless (sinv_itok i Px).
  Proof. rewrite sinv_itok_unseal /sinv_itok_def /gmap_view_frag. exact _. Qed.
  Fact sinv_tok_timeless `{!Discrete Px} : Timeless (sinv_tok Px).
  Proof. exact _. Qed.

  (** [sinv_iwsat] is non-expansive *)
  #[export] Instance sinv_iwsat_ne {n} :
    Proper (pointwise_relation _ (pointwise_relation _ (≡{n}≡)) ==> (≡{n}≡))
      sinv_iwsat.
  Proof. rewrite sinv_iwsat_unseal. solve_proper. Qed.
  #[export] Instance sinv_iwsat_proper :
    Proper (pointwise_relation _ (pointwise_relation _ (≡)) ==> (≡)) sinv_iwsat.
  Proof. rewrite sinv_iwsat_unseal. solve_proper. Qed.

  (** [sinv_iwsat] is timeless if [sm] is always timeless
    and the underlying ofe is discrete *)
  #[export] Instance sinv_iwsat_timeless
    `{!OfeDiscrete (FML $oi Σ), !∀ i Px, Timeless (sm i Px)} :
    Timeless (sinv_iwsat sm).
  Proof. rewrite sinv_iwsat_unseal. exact _. Qed.

  (** Lemma for [sinv_itok_alloc] *)
  Local Lemma sinv_auth_tok_alloc {M i Px} : i ∉ dom M →
    sinv_auth_tok M ==∗ sinv_auth_tok (<[i:=Px]> M) ∗ sinv_itok i Px.
  Proof.
    move=> /not_elem_of_dom eq. iIntros "●". rewrite sinv_itok_unseal -own_op.
    iApply own_update; [|done]. rewrite fmap_insert.
    apply gmap_view_alloc; [|done..]. by rewrite lookup_fmap eq.
  Qed.
  (** Allocate [sinv_itok] *)
  Lemma sinv_itok_alloc {sm} Px :
    sinv_iwsat sm -∗ ∃ I, ∀ i, ⌜i ∉ I⌝ ==∗
      sinv_itok i Px ∗ (sm i Px -∗ sinv_iwsat sm).
  Proof.
    rewrite sinv_iwsat_unseal. iIntros "[%M[● M]]". iExists (dom M).
    iIntros (i ?). iMod (sinv_auth_tok_alloc with "●") as "[● #i]"; [done|].
    iModIntro. iSplitR; [by rewrite sinv_itok_unseal|]. iIntros "Px". iExists _.
    iFrame "●". iApply (big_sepM_insert_2 with "Px M").
  Qed.
  Lemma sinv_tok_alloc {sm} Px :
    sinv_wsat sm ==∗ sinv_tok Px ∗ (sm Px -∗ sinv_wsat sm).
  Proof.
    iIntros "W". iDestruct (sinv_itok_alloc with "W") as (?) "big".
    iMod ("big" with "[]") as "[? $]". { iPureIntro. apply is_fresh. }
    iModIntro. by iExists _.
  Qed.

  (** Lemma for [sinv_tok_acc'] *)
  Local Lemma sinv_auth_tok_lookup {M i Px} :
    sinv_auth_tok M -∗ sinv_itok i Px -∗ ∃ Px', ⌜M !! i = Some Px'⌝ ∗ Px ≡ Px'.
  Proof.
    rewrite sinv_itok_unseal. iIntros "● i".
    iDestruct (own_valid_2 with "● i") as "✓".
    rewrite gmap_view_both_validI_total. iDestruct "✓" as (? _ _ eq) "[_ in]".
    move: eq. rewrite lookup_fmap. case: (M !! i); [|done]=> Px' [<-].
    iExists Px'. iSplit; [done|]. by rewrite to_agree_includedI.
  Qed.
  (** Access via [sinv_tok] *)
  Lemma sinv_tok_acc' `{!NonExpansive (sm i)} {Px} :
    sinv_itok i Px -∗ sinv_iwsat sm -∗ sm i Px ∗ (sm i Px -∗ sinv_iwsat sm).
  Proof.
    rewrite sinv_iwsat_unseal. iIntros "i [%M[● M]]".
    iDestruct (sinv_auth_tok_lookup with "● i") as (Px' eq) "#≡".
    iDestruct (big_sepM_lookup_acc with "M") as "[Px' →M]"; [done|].
    iRewrite "≡". iFrame "Px'". iIntros "Px'". iExists _. iFrame "●".
    by iApply "→M".
  Qed.
  Lemma sinv_tok_acc `{!NonExpansive sm} {Px} :
    sinv_tok Px -∗ sinv_wsat sm -∗ sm Px ∗ (sm Px -∗ sinv_wsat sm).
  Proof. iIntros "[%i i]". iApply (sinv_tok_acc' with "i"). Qed.
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
  ⊢ |==> ∃ _ : sinvGS FML Σ, ∀ sm, sinv_iwsat sm.
Proof.
  iMod sinv_auth_tok_alloc_empty as (?) "●". iModIntro. iExists _.
  iIntros. rewrite sinv_iwsat_unseal. iExists ∅. by iFrame.
Qed.
