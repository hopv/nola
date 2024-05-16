(** * Simple invariant *)

From nola.bi Require Export ofe upd.
From iris.algebra Require Import agree gmap_view.
From iris.proofmode Require Import proofmode.
Import OfeNotation.

Implicit Type PROP : oFunctor.

Class sinvGpreS PROP Σ :=
  sinvGpreS_in : inG Σ (gmap_viewR positive (agreeR (PROP $o Σ))).
Local Existing Instance sinvGpreS_in.
Class sinvGS PROP Σ := SinvGS {
  sinvGS_pre : sinvGpreS PROP Σ;
  sinv_name : gname;
}.
Local Existing Instance sinvGS_pre.
Definition sinvΣ PROP `{!oFunctorContractive PROP} :=
  #[GFunctor (gmap_viewRF positive (agreeRF PROP))].
#[export] Instance subG_sinvΣ
  `{!oFunctorContractive PROP, !subG (sinvΣ PROP) Σ} : sinvGpreS PROP Σ.
Proof. solve_inG. Qed.

Section sinv.
  Context `{!sinvGS PROP Σ}.
  Implicit Type P : PROP $o Σ.

  (** Simple invariant token *)
  Local Definition sinv_itok_def i P : iProp Σ :=
    own sinv_name (gmap_view_frag i DfracDiscarded (to_agree P)).
  Local Lemma sinv_itok_aux : seal sinv_itok_def. Proof. by eexists. Qed.
  Definition sinv_itok := sinv_itok_aux.(unseal).
  Local Lemma sinv_itok_unseal : sinv_itok = sinv_itok_def.
  Proof. exact: seal_eq. Qed.

  (** Simple invariant token with the index hidden *)
  Definition sinv_tok P : iProp Σ := ∃ i, sinv_itok i P.

  (** Authoritative token *)
  Local Definition sinv_auth_tok M :=
    own sinv_name (gmap_view_auth (DfracOwn 1) (to_agree <$> M)).
  (** World satisfaction *)
  Definition sinv_iwsat_def intp : iProp Σ :=
    ∃ M, sinv_auth_tok M ∗ [∗ map] i ↦ P ∈ M, intp i P.
  Local Lemma sinv_iwsat_aux : seal sinv_iwsat_def. Proof. by eexists. Qed.
  Definition sinv_iwsat := sinv_iwsat_aux.(unseal).
  Local Lemma sinv_iwsat_unseal : sinv_iwsat = sinv_iwsat_def.
  Proof. exact: seal_eq. Qed.
End sinv.
(** World satisfaction whose interpretation ignores the index *)
Notation sinv_wsat' PROP intp := (sinv_iwsat (PROP:=PROP) (λ _, intp)).
Notation sinv_wsat intp := (sinv_wsat' _ intp).

Section sinv.
  Context `{!sinvGS PROP Σ}.
  Implicit Type P : PROP $o Σ.
  Implicit Type (i : positive) (I : gset positive).

  (** [sinv_itok] and [sinv_tok] are non-expansive *)
  #[export] Instance sinv_itok_ne i : NonExpansive (sinv_itok i).
  Proof. rewrite sinv_itok_unseal. solve_proper. Qed.
  #[export] Instance sinv_tok_ne : NonExpansive sinv_tok.
  Proof. solve_proper. Qed.
  (** [sinv_itok] and [sinv_tok] are persistent *)
  #[export] Instance sinv_itok_persistent {i P} : Persistent (sinv_itok i P).
  Proof. rewrite sinv_itok_unseal. exact _. Qed.
  Fact sinv_tok_persistent {P} : Persistent (sinv_tok P).
  Proof. exact _. Qed.
  (** [sinv_itok] and [sinv_tok] are timeless
    if the underlying ofe is discrete *)
  #[export] Instance sinv_itok_timeless `{!OfeDiscrete (PROP $o Σ)}
    {i P} : Timeless (sinv_itok i P).
  Proof. rewrite sinv_itok_unseal. exact _. Qed.
  Fact sinv_tok_timeless `{!OfeDiscrete (PROP $o Σ)} {P} :
    Timeless (sinv_tok P).
  Proof. exact _. Qed.

  (** [sinv_iwsat] is non-expansive *)
  #[export] Instance sinv_iwsat_ne {n} :
    Proper (pointwise_relation _ (pointwise_relation _ (≡{n}≡)) ==> (≡{n}≡))
      sinv_iwsat.
  Proof. rewrite sinv_iwsat_unseal. solve_proper. Qed.
  #[export] Instance sinv_iwsat_proper :
    Proper (pointwise_relation _ (pointwise_relation _ (≡)) ==> (≡)) sinv_iwsat.
  Proof. rewrite sinv_iwsat_unseal. solve_proper. Qed.

  (** [sinv_iwsat] is timeless if [intp] is always timeless
    and the underlying ofe is discrete *)
  #[export] Instance sinv_iwsat_timeless
    `{!OfeDiscrete (PROP $o Σ), !∀ i P, Timeless (intp i P)} :
    Timeless (sinv_iwsat intp).
  Proof. rewrite sinv_iwsat_unseal. exact _. Qed.

  (** Lemma for [sinv_itok_alloc] *)
  Local Lemma sinv_auth_tok_alloc {M i P} : i ∉ dom M →
    sinv_auth_tok M ==∗ sinv_auth_tok (<[i:=P]> M) ∗ sinv_itok i P.
  Proof.
    move=> /not_elem_of_dom eq. iIntros "●". rewrite sinv_itok_unseal -own_op.
    iApply own_update; [|done]. rewrite fmap_insert.
    apply gmap_view_alloc; [|done..]. by rewrite lookup_fmap eq.
  Qed.
  (** Allocate [sinv_itok] *)
  Lemma sinv_itok_alloc {intp} P :
    sinv_iwsat intp -∗ ∃ I, ∀ i, ⌜i ∉ I⌝ ==∗
      sinv_itok i P ∗ (intp i P -∗ sinv_iwsat intp).
  Proof.
    rewrite sinv_iwsat_unseal. iIntros "[%M[● M]]". iExists (dom M).
    iIntros (i ?). iMod (sinv_auth_tok_alloc with "●") as "[● #i]"; [done|].
    iModIntro. iSplitR; [by rewrite sinv_itok_unseal|]. iIntros "P". iExists _.
    iFrame "●". iApply (big_sepM_insert_2 with "P M").
  Qed.
  Lemma sinv_tok_alloc {intp} P :
    sinv_wsat intp ==∗ sinv_tok P ∗ (intp P -∗ sinv_wsat intp).
  Proof.
    iIntros "W". iDestruct (sinv_itok_alloc with "W") as (?) "big".
    iMod ("big" with "[]") as "[? $]". { iPureIntro. apply is_fresh. }
    iModIntro. by iExists _.
  Qed.

  (** Lemma for [sinv_tok_acc'] *)
  Local Lemma sinv_auth_tok_lookup {M i P} :
    sinv_auth_tok M -∗ sinv_itok i P -∗ ∃ P', ⌜M !! i = Some P'⌝ ∗ P ≡ P'.
  Proof.
    rewrite sinv_itok_unseal. iIntros "● i".
    iDestruct (own_valid_2 with "● i") as "✓".
    rewrite gmap_view_both_validI_total. iDestruct "✓" as (? _ _ eq) "[_ in]".
    move: eq. rewrite lookup_fmap. case: (M !! i); [|done]=> P' [<-].
    iExists P'. iSplit; [done|]. by rewrite to_agree_includedI.
  Qed.
  (** Access via [sinv_tok] *)
  Lemma sinv_tok_acc' {intp i P} `{!NonExpansive (intp i)} :
    sinv_itok i P -∗ sinv_iwsat intp -∗
      intp i P ∗ (intp i P -∗ sinv_iwsat intp).
  Proof.
    rewrite sinv_iwsat_unseal. iIntros "i [%M[● M]]".
    iDestruct (sinv_auth_tok_lookup with "● i") as (P' eq) "#≡".
    iDestruct (big_sepM_lookup_acc with "M") as "[P' →M]"; [done|].
    iRewrite "≡". iFrame "P'". iIntros "P'". iExists _. iFrame "●".
    by iApply "→M".
  Qed.
  Lemma sinv_tok_acc {intp P} `{!NonExpansive intp} :
    sinv_tok P -∗ sinv_wsat intp -∗ intp P ∗ (intp P -∗ sinv_wsat intp).
  Proof. iIntros "[%i i]". iApply (sinv_tok_acc' with "i"). Qed.
End sinv.

(** Lemma for [sinv_wsat_alloc] *)
Local Lemma sinv_auth_tok_alloc_empty `{!sinvGpreS PROP Σ} :
  ⊢ |==> ∃ _ : sinvGS PROP Σ, sinv_auth_tok ∅.
Proof.
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅)) as (γ) "●".
  { apply gmap_view_auth_valid. } { iModIntro. by iExists (SinvGS _ _ _ γ). }
Qed.
(** Allocate [sinv_wsat] *)
Lemma sinv_wsat_alloc `{!sinvGpreS PROP Σ} :
  ⊢ |==> ∃ _ : sinvGS PROP Σ, ∀ intp, sinv_iwsat intp.
Proof.
  iMod sinv_auth_tok_alloc_empty as (?) "●". iModIntro. iExists _.
  iIntros. rewrite sinv_iwsat_unseal. iExists ∅. by iFrame.
Qed.
