(** * Nola later-free invariant *)

From nola.iris Require Export sinv upd.
From stdpp Require Export namespaces.
From iris.algebra Require Import gset.
From iris.base_logic.lib Require Import wsat invariants.
From iris.proofmode Require Import proofmode.

Implicit Type PROP : Type.

(** ** Resources *)

Class ninvGS PROP Σ := ninvGS_in :: sinvGS PROP Σ.
Class ninvGpreS PROP Σ := ninvGpreS_in :: sinvGpreS PROP Σ.
Definition ninvΣ PROP : gFunctors := sinvΣ PROP.
#[export] Instance subG_ninvΣ `{!subG (ninvΣ PROP) Σ} : ninvGpreS PROP Σ.
Proof. solve_inG. Qed.

Section ninv.
  Context `{!invGS_gen hlc Σ, !ninvGS PROP Σ}.

  (** [ninv]: Invariant token *)
  Local Definition ninv_def (N : namespace) (P : PROP) : iProp Σ :=
    ∃ i, ⌜i ∈ (↑N:coPset)⌝ ∗ sinv_tok' i P.
  Local Definition ninv_aux : seal ninv_def. Proof. by eexists. Qed.
  Definition ninv := ninv_aux.(unseal).
  Local Lemma ninv_unseal : ninv = ninv_def. Proof. exact: seal_eq. Qed.

  (** [ninv] is persistent and timeless *)
  #[export] Instance ninv_persistent {N P} : Persistent (ninv N P).
  Proof. rewrite ninv_unseal. exact _. Qed.
  #[export] Instance ninv_timeless {N P} : Timeless (ninv N P).
  Proof. rewrite ninv_unseal. exact _. Qed.

  Local Definition ninv_wsat_def (intp : PROP -d> iProp Σ) : iProp Σ :=
    sinv_wsat' (λ i P, intp P ∗ ownD {[i]} ∨ ownE {[i]})%I.
  Local Definition ninv_wsat_aux : seal ninv_wsat_def. Proof. by eexists. Qed.
  Definition ninv_wsat := ninv_wsat_aux.(unseal).
  Local Lemma ninv_wsat_unseal : ninv_wsat = ninv_wsat_def.
  Proof. exact: seal_eq. Qed.

  (** [ninv_wsat] is non-expansive *)
  #[export] Instance ninv_wsat_ne : NonExpansive ninv_wsat.
  Proof. rewrite ninv_wsat_unseal. solve_proper. Qed.
  #[export] Instance ninv_wsat_proper : Proper ((≡) ==> (≡)) ninv_wsat.
  Proof. apply ne_proper, _. Qed.

  (** ** Lemmas *)

  (** Allocate [ninv] *)
  Lemma ninv_alloc_rec {intp N P} :
    (ninv N P -∗ intp P) =[ninv_wsat intp]=∗ ninv N P.
  Proof.
    rewrite ninv_unseal ninv_wsat_unseal. iIntros "→P W".
    iDestruct (sinv_alloc' with "W") as (I) "big".
    iMod (own_unit (gset_disjUR positive) disabled_name) as "D".
    iMod (own_updateP with "[$]") as (x) "[X D]".
    { apply (gset_disj_alloc_empty_updateP_strong'
        (λ i, i ∉ I ∧ i ∈ (↑N:coPset)))=> J.
      case: (fresh_inv_name (I ∪ J) N)=> [i[/not_elem_of_union[??]?]].
      by exists i. }
    iDestruct "X" as %[i[->[??]]]. iMod ("big" with "[//]") as "[#i →W]".
    iModIntro. iSplitL; [|iExists _; by iSplit]. iApply "→W". iLeft.
    iSplitR "D"; [|done]. iApply "→P". iExists _; by iSplit.
  Qed.
  Lemma ninv_alloc {intp N P} : intp P =[ninv_wsat intp]=∗ ninv N P.
  Proof. iIntros "P W". iApply (ninv_alloc_rec with "[P] W"). by iIntros. Qed.

  (** Access [ownE] *)
  Local Lemma ownE_acc {N E} :
    ↑N ⊆ E → ⊢ |={E,E∖↑N}=> ownE (↑N) ∗ (ownE (↑N) ={E∖↑N,E}=∗ True).
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
    move=> ?. rewrite ninv_unseal ninv_wsat_unseal. iIntros "[%i[% #i]] W".
    iMod ownE_acc as "[N cl]"; [done|].
    iDestruct (sinv_acc' with "i W") as "[in →W]".
    rewrite {1 2}(union_difference_L {[i]} (↑N)); [|set_solver].
    rewrite ownE_op; [|set_solver]. iDestruct "N" as "[Ei EN∖i]".
    iDestruct "in" as "[[$ D]|Ei']"; last first.
    { iDestruct (ownE_singleton_twice with "[$Ei $Ei']") as "[]". }
    iModIntro. iDestruct ("→W" with "[$Ei]") as "$". iIntros "P W".
    iDestruct (sinv_acc' with "i W") as "[[[_ D']|Ei] →W]".
    { iDestruct (ownD_singleton_twice with "[$D $D']") as "[]". }
    iMod ("cl" with "[$Ei $EN∖i]") as "_". iModIntro. iSplitL; [|done].
    iApply "→W". iLeft. iFrame.
  Qed.
End ninv.

(** Allocate [ninv_wsat] *)
Lemma ninv_wsat_alloc `{!ninvGpreS PROP Σ, !invGS_gen hlc Σ} :
  ⊢ |==> ∃ _ : ninvGS PROP Σ, ∀ intp, ninv_wsat intp.
Proof.
  iMod sinv_wsat_alloc as (?) "W". iModIntro. iExists _. iIntros (?).
  rewrite ninv_wsat_unseal. iApply "W".
Qed.
