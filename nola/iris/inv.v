(** * Nola later-free invariant *)

From nola.iris Require Export upd.
From stdpp Require Export namespaces.
From iris.algebra Require Import gset.
From iris.base_logic.lib Require Import ghost_map wsat invariants.
From iris.proofmode Require Import proofmode.

Implicit Type PROP : Type.

(** ** Resources *)

Class ninvGS PROP Σ := NinvGS {
  ninvGS_in :: ghost_mapG Σ positive (leibnizO PROP);
  ninv_name : gname;
}.
Class ninvGpreS PROP Σ :=
  ninvGpreS_in :: ghost_mapG Σ positive (leibnizO PROP).
Definition ninvΣ PROP : gFunctors := ghost_mapΣ positive (leibnizO PROP).
#[export] Instance subG_ninvΣ `{!subG (ninvΣ PROP) Σ} : ninvGpreS PROP Σ.
Proof. solve_inG. Qed.

Section ninv.
  Context `{!invGS_gen hlc Σ, !ninvGS PROP Σ}.

  (** ** Propositions *)

  (** [ownI]: Basic invariant token *)
  Local Definition ownI (i : positive) (P : PROP) : iProp Σ :=
    i ↪[ninv_name]□ P.

  (** [ninv]: Invariant token *)
  Local Definition ninv_def (N : namespace) (P : PROP) : iProp Σ :=
    ∃ i, ⌜i ∈ (↑N:coPset)⌝ ∗ ownI i P.
  Local Definition ninv_aux : seal ninv_def. Proof. by eexists. Qed.
  Definition ninv := ninv_aux.(unseal).
  Local Lemma ninv_unseal : ninv = ninv_def.
  Proof. exact ninv_aux.(seal_eq). Qed.

  (** [ninv] is timeless and persistent *)
  #[export] Instance ninv_timeless {N P} : Timeless (ninv N P).
  Proof. rewrite ninv_unseal. exact _. Qed.
  #[export] Instance ninv_persistent {N P} : Persistent (ninv N P).
  Proof. rewrite ninv_unseal. exact _. Qed.

  (** [ninv_wsat]: Invariant world satisfaction *)
  Local Definition authI (I : gmap positive PROP) :=
    ghost_map_auth ninv_name 1 I.
  Local Definition ninv_wsat_def (intp : PROP -d> iProp Σ) : iProp Σ :=
    ∃ I, authI I ∗ [∗ map] i ↦ P ∈ I, intp P ∗ ownD {[i]} ∨ ownE {[i]}.
  Local Definition ninv_wsat_aux : seal ninv_wsat_def. Proof. by eexists. Qed.
  Definition ninv_wsat := ninv_wsat_aux.(unseal).
  Local Lemma ninv_wsat_unseal : ninv_wsat = ninv_wsat_def.
  Proof. exact ninv_wsat_aux.(seal_eq). Qed.

  (** [ninv_wsat] is non-expansive *)
  #[export] Instance ninv_wsat_ne : NonExpansive ninv_wsat.
  Proof. rewrite ninv_wsat_unseal. solve_proper. Qed.
  #[export] Instance ninv_wsat_proper : Proper ((≡) ==> (≡)) ninv_wsat.
  Proof. apply ne_proper, _. Qed.

  (** ** Lemmas *)

  (** Allocate [ownI] *)
  Local Lemma ownI_alloc_rec {intp P N} :
    (∀ i, ⌜i ∈ (↑N:coPset)⌝ → ownI i P -∗ intp P) -∗ ninv_wsat intp ==∗
      ∃ i, ⌜i ∈ (↑N:coPset)⌝ ∗ ninv_wsat intp ∗ ownI i P.
  Proof.
    rewrite ninv_wsat_unseal. iIntros "→P [%I[I W]]".
    iMod (own_unit (gset_disjUR positive) disabled_name) as "D".
    iMod (own_updateP with "[$]") as (x) "[X D]".
    { apply (gset_disj_alloc_empty_updateP_strong'
        (λ i, I !! i = None ∧ i ∈ (↑N:coPset)))=> E.
      case: (fresh_inv_name (E ∪ dom I) N)=>
        [i[/not_elem_of_union[?/not_elem_of_dom ?]?]]. by exists i. }
    iDestruct "X" as %[i[->[??]]].
    iMod (ghost_map_insert_persist with "I") as "[I #i]"; [done|]. iModIntro.
    iExists _. iFrame "i". iSplit; [done|]. iExists _. iFrame "I".
    iApply (big_sepM_insert_2 with "[→P D]"); [|done]. iLeft.
    iSplitR "D"; [|done]. by iApply "→P".
  Qed.
  (** Turn [ownI] to [ninv] *)
  Local Lemma ownI_ninv {i N P} : i ∈ (↑N:coPset) → ownI i P ⊢ ninv N P.
  Proof. rewrite ninv_unseal. iIntros. iExists _. by iSplit. Qed.
  (** Allocate [ninv] *)
  Lemma ninv_alloc_rec {intp N P} :
    (ninv N P -∗ intp P) =[ninv_wsat intp]=∗ ninv N P.
  Proof.
    iIntros "→P W".
    iMod (ownI_alloc_rec with "[→P] W") as (i ?) "[W i]".
    - iIntros (i ?) "i". iApply "→P". by iApply ownI_ninv.
    - iModIntro. iFrame "W". by iApply ownI_ninv.
  Qed.
  Lemma ninv_alloc {intp N P} : intp P =[ninv_wsat intp]=∗ ninv N P.
  Proof. iIntros "P W". iApply (ninv_alloc_rec with "[P] W"). by iIntros. Qed.

  (** Open by [ownI] *)
  Local Lemma ownI_open {intp i P} :
    ownI i P -∗ ownE {[i]} -∗ ninv_wsat intp -∗
      ninv_wsat intp ∗ intp P ∗ ownD {[i]}.
  Proof.
    rewrite ninv_wsat_unseal. iIntros "i ? [%I[I W]]".
    iDestruct (ghost_map_lookup with "I i") as %?.
    iDestruct (big_sepM_lookup_acc with "W") as "[[[$$]|?] →W]";
      [done| |iDestruct (ownE_singleton_twice with "[$]") as "[]"].
    iExists _. iFrame "I". iApply "→W". by iRight.
  Qed.
  (** Close by [ownI] *)
  Local Lemma ownI_close {intp i P} :
    ownI i P -∗ ownD {[i]} -∗ intp P -∗ ninv_wsat intp -∗
      ninv_wsat intp ∗ ownE {[i]}.
  Proof.
    rewrite ninv_wsat_unseal. iIntros "i ? ? [%I[I W]]".
    iDestruct (ghost_map_lookup with "I i") as %?.
    iDestruct (big_sepM_lookup_acc with "W") as "[[[_ ?]|$] →W]";
      [done|iDestruct (ownD_singleton_twice with "[$]") as %[]|].
    iExists _. iFrame "I". iApply "→W". iLeft. iFrame.
  Qed.
  (** Access [ownE] *)
  Local Lemma ownE_acc {N E} :
    ↑N ⊆ E →  ⊢ |={E,E∖↑N}=> ownE (↑N) ∗ (ownE (↑N) ={E∖↑N,E}=∗ True).
  Proof.
    rewrite fancy_updates.uPred_fupd_unseal /fancy_updates.uPred_fupd_def.
    move=> ?. iIntros "[$ E]". do 2 iModIntro.
    rewrite {1 4}(union_difference_L (↑ N) E); [|done].
    rewrite ownE_op; [|set_solver]. iDestruct "E" as "[$$]". by iIntros "$$".
  Qed.
  (** Access [ninv] *)
  Lemma ninv_acc {intp N E P} :
    ↑N ⊆ E → ninv N P =[ninv_wsat intp]{E,E∖↑N}=∗
      intp P ∗ (intp P =[ninv_wsat intp]{E∖↑N,E}=∗ True)%I.
  Proof.
    move=> ?. rewrite ninv_unseal. iIntros "[%i[% #i]] W".
    iMod ownE_acc as "[N cl]"; [done|].
    rewrite {1 2}(union_difference_L {[i]} (↑N)); [|set_solver].
    rewrite ownE_op; [|set_solver]. iDestruct "N" as "[E E']".
    iDestruct (ownI_open with "i E W") as "[$[$ D]]". iModIntro.
    iIntros "P W". iDestruct (ownI_close with "i D P W") as "[$ E]".
    iApply "cl". iFrame.
  Qed.
End ninv.

(** Allocate [ninv_wsat] *)
Lemma ninv_wsat_alloc `{!invGS_gen hlc Σ, !ninvGpreS PROP Σ} :
  ⊢ |==> ∃ _ : ninvGS PROP Σ, ∀ intp, ninv_wsat intp.
Proof.
  iMod ghost_map_alloc_empty as (γ) "●". iModIntro. iExists (NinvGS _ _ _ γ).
  rewrite ninv_wsat_unseal. iIntros (?). iExists ∅. by iFrame.
Qed.
