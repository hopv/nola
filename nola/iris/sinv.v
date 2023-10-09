(** * Simple invariant *)

From nola.iris Require Export upd.
From iris.base_logic.lib Require Import ghost_map.
From iris.proofmode Require Import proofmode.

Implicit Type PROP : Type.

Class sinvGS PROP Σ := SinvGS {
  sinvGS_in :: ghost_mapG Σ positive (leibnizO PROP);
  sinv_name : gname;
}.
Class sinvGpreS PROP Σ :=
  sinvGpreS_in :: ghost_mapG Σ positive (leibnizO PROP).
Definition sinvΣ PROP : gFunctors := ghost_mapΣ positive (leibnizO PROP).
#[export] Instance subG_sinvΣ `{!subG (sinvΣ PROP) Σ} : sinvGpreS PROP Σ.
Proof. solve_inG. Qed.

Section sinv.
  Context `{!sinvGS PROP Σ}.

  (** Simple invariant token *)
  Local Definition sinv_tok'_def i P : iProp Σ := i ↪[sinv_name]□ P.
  Local Lemma sinv_tok'_aux : seal sinv_tok'_def. Proof. by eexists. Qed.
  Definition sinv_tok' := sinv_tok'_aux.(unseal).
  Local Lemma sinv_tok'_unseal : sinv_tok' = sinv_tok'_def.
  Proof. exact: seal_eq. Qed.

  (** Simple invariant token with the index hidden *)
  Definition sinv_tok P : iProp Σ := ∃ i, sinv_tok' i P.

  (** World satisfaction *)
  Definition sinv_wsat'_def intp : iProp Σ :=
    ∃ M, ghost_map_auth sinv_name 1 M ∗ [∗ map] i ↦ P ∈ M, intp i P.
  Local Lemma sinv_wsat'_aux : seal sinv_wsat'_def. Proof. by eexists. Qed.
  Definition sinv_wsat' := sinv_wsat'_aux.(unseal).
  Local Lemma sinv_wsat'_unseal : sinv_wsat' = sinv_wsat'_def.
  Proof. exact: seal_eq. Qed.
End sinv.
(** World satisfaction whose interpretation ignores the index *)
Notation sinv_wsat intp := (sinv_wsat' (λ _, intp)).

Section sinv.
  Context `{!sinvGS PROP Σ}.
  Implicit Type (i : positive) (P : PROP) (I : gset positive).

  (** [sinv_tok'] and [sinv_tok] are persistent and timeless *)
  #[export] Instance sinv_tok'_persistent {i P} : Persistent (sinv_tok' i P).
  Proof. rewrite sinv_tok'_unseal. exact _. Qed.
  #[export] Instance sinv_tok'_timeless {i P} : Timeless (sinv_tok' i P).
  Proof. rewrite sinv_tok'_unseal. exact _. Qed.
  Fact sinv_tok_persistent {P} : Persistent (sinv_tok P).
  Proof. exact _. Qed.
  Fact sinv_tok_timeless {P} : Timeless (sinv_tok P).
  Proof. exact _. Qed.

  (** [sinv_wsat'] is non-expansive *)
  #[export] Instance sinv_wsat'_ne {n} :
    Proper (pointwise_relation _ (pointwise_relation _ (≡{n}≡)) ==> (≡{n}≡))
      sinv_wsat'.
  Proof. rewrite sinv_wsat'_unseal. solve_proper. Qed.
  #[export] Instance sinv_wsat'_proper :
    Proper (pointwise_relation _ (pointwise_relation _ (≡)) ==> (≡)) sinv_wsat'.
  Proof. rewrite sinv_wsat'_unseal. solve_proper. Qed.

  (** [sinv_wsat'] is timeless if [intp] is always timeless *)
  #[export] Instance sinv_wsat'_timeless `{!∀ i P, Timeless (intp i P)} :
    Timeless (sinv_wsat' intp).
  Proof. rewrite sinv_wsat'_unseal. exact _. Qed.

  (** Allocate [sinv_tok'] *)
  Lemma sinv_alloc' {intp} P :
    sinv_wsat' intp -∗ ∃ I, ∀ i, ⌜i ∉ I⌝ ==∗
      sinv_tok' i P ∗ (intp i P -∗ sinv_wsat' intp).
  Proof.
    rewrite sinv_wsat'_unseal. iIntros "[%M[● M]]". iExists (dom M).
    iIntros (i ?). iMod (ghost_map_insert_persist with "●") as "[● #i]";
      [by apply not_elem_of_dom|]. iModIntro.
    iSplitR; [by rewrite sinv_tok'_unseal|]. iIntros "P". iExists _. iFrame "●".
    iApply (big_sepM_insert_2 with "P M").
  Qed.
  Lemma sinv_alloc {intp} P :
    sinv_wsat intp ==∗ sinv_tok P ∗ (intp P -∗ sinv_wsat intp).
  Proof.
    iIntros "W". iDestruct (sinv_alloc' with "W") as (?) "big".
    iMod ("big" with "[]") as "[? $]". { iPureIntro. apply is_fresh. }
    iModIntro. by iExists _.
  Qed.

  (** Accesss via [sinv_tok] *)
  Lemma sinv_acc' {intp i P} :
    sinv_tok' i P -∗ sinv_wsat' intp -∗
      intp i P ∗ (intp i P -∗ sinv_wsat' intp).
  Proof.
    rewrite sinv_tok'_unseal sinv_wsat'_unseal. iIntros "i [%M[● M]]".
    iDestruct (ghost_map_lookup with "● i") as %?.
    iDestruct (big_sepM_lookup_acc with "M") as "[$ →M]"; [done|]. iIntros "P".
    iExists _. iFrame "●". by iApply "→M".
  Qed.
  Lemma sinv_acc {intp P} :
    sinv_tok P -∗ sinv_wsat intp -∗ intp P ∗ (intp P -∗ sinv_wsat intp).
  Proof. iIntros "[%i i]". iApply (sinv_acc' with "i"). Qed.
End sinv.

(** Allocate [sinv_wsat] *)
Lemma sinv_wsat_alloc `{!sinvGpreS PROP Σ} :
  ⊢ |==> ∃ _ : sinvGS PROP Σ, ∀ intp, sinv_wsat' intp.
Proof.
  iMod ghost_map_alloc_empty as (γ) "●". iModIntro. iExists (SinvGS _ _ _ γ).
  iIntros. rewrite sinv_wsat'_unseal. iExists ∅. by iFrame.
Qed.
