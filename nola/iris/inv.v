(** * Nola later-free invariant *)

From nola.iris Require Export sinv upd.
From iris.base_logic.lib Require Export wsat invariants.
From iris.algebra Require Import gset.
From iris.proofmode Require Import proofmode.

Implicit Type PROP : Type.

Class ninvGS PROP Σ := ninvGS_in : sinvGS PROP Σ.
Local Existing Instance ninvGS_in.
Class ninvGpreS PROP Σ := ninvGpreS_in : sinvGpreS PROP Σ.
Local Existing Instance ninvGpreS_in.
Definition ninvΣ PROP : gFunctors := sinvΣ PROP.
#[export] Instance subG_ninvΣ `{!subG (ninvΣ PROP) Σ} : ninvGpreS PROP Σ.
Proof. solve_inG. Qed.

Section inv_tok.
  Context `{!ninvGS PROP Σ, !invGS_gen hlc Σ}.

  (** [inv_tok]: Invariant token *)
  Local Definition inv_tok_def (N : namespace) (P : PROP) : iProp Σ :=
    ∃ i, ⌜i ∈ (↑N:coPset)⌝ ∗ sinv_tok' i P.
  Local Definition inv_tok_aux : seal inv_tok_def. Proof. by eexists. Qed.
  Definition inv_tok := inv_tok_aux.(unseal).
  Local Lemma inv_tok_unseal : inv_tok = inv_tok_def.
  Proof. exact: seal_eq. Qed.

  (** [inv_tok] is persistent and timeless *)
  #[export] Instance inv_tok_persistent {N P} : Persistent (inv_tok N P).
  Proof. rewrite inv_tok_unseal. exact _. Qed.
  #[export] Instance inv_tok_timeless {N P} : Timeless (inv_tok N P).
  Proof. rewrite inv_tok_unseal. exact _. Qed.

  (** World satisfaction *)
  Local Definition inv_wsat_def (intp : PROP -d> iProp Σ) : iProp Σ :=
    sinv_wsat' (λ i P, intp P ∗ ownD {[i]} ∨ ownE {[i]})%I.
  Local Definition inv_wsat_aux : seal inv_wsat_def. Proof. by eexists. Qed.
  Definition inv_wsat := inv_wsat_aux.(unseal).
  Local Lemma inv_wsat_unseal : inv_wsat = inv_wsat_def.
  Proof. exact: seal_eq. Qed.

  (** [inv_wsat] is non-expansive *)
  #[export] Instance inv_wsat_ne : NonExpansive inv_wsat.
  Proof. rewrite inv_wsat_unseal. solve_proper. Qed.
  #[export] Instance inv_wsat_proper : Proper ((≡) ==> (≡)) inv_wsat.
  Proof. apply ne_proper, _. Qed.

  (** Allocate [inv_tok] *)
  Lemma inv_tok_alloc_rec {intp} P N :
    (inv_tok N P -∗ intp P) =[inv_wsat intp]=∗ inv_tok N P.
  Proof.
    rewrite inv_tok_unseal inv_wsat_unseal. iIntros "→P W".
    iDestruct (sinv_tok_alloc' with "W") as (I) "big".
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
  Lemma inv_tok_alloc {intp} P N : intp P =[inv_wsat intp]=∗ inv_tok N P.
  Proof.
    iIntros "P W". iApply (inv_tok_alloc_rec with "[P] W"). by iIntros.
  Qed.

  (** Access [ownE] *)
  Lemma ownE_subset {E F} : F ⊆ E → ownE E ⊣⊢ ownE F ∗ ownE (E∖F).
  Proof.
    move=> ?. rewrite {1}(union_difference_L F E); [|done].
    by rewrite ownE_op; [|set_solver].
  Qed.
  (** Access [ownE] from [fupd] *)
  Lemma fupd_ownE_acc {E F} :
    F ⊆ E → ⊢ |={E,E∖F}=> ownE F ∗ (ownE F ={E∖F,E}=∗ True).
  Proof.
    rewrite fancy_updates.uPred_fupd_unseal /fancy_updates.uPred_fupd_def=> FE.
    rewrite (ownE_subset FE). by iIntros "[$[$$]]!>!>$[$$]!>".
  Qed.

  (** Access [inv_tok] *)
  Lemma inv_tok_acc' {intp N E P} :
    ↑N ⊆ E → ownE E -∗ inv_tok N P -∗ modw id (inv_wsat intp) (
      ownE (E∖↑N) ∗ intp P ∗
      (ownE (E∖↑N) -∗ intp P -∗ modw id (inv_wsat intp) (ownE E))).
  Proof.
    move=> NE. rewrite inv_tok_unseal inv_wsat_unseal (ownE_subset NE).
    iIntros "[N $] [%i[% #i]] W".
    iDestruct (sinv_tok_acc' with "i W") as "[in →W]".
    rewrite {1 3}(union_difference_L {[i]} (↑N)); [|set_solver].
    rewrite ownE_op; [|set_solver]. iDestruct "N" as "[Ei $]".
    iDestruct "in" as "[[$ D]|Ei']"; last first.
    { iDestruct (ownE_singleton_twice with "[$Ei $Ei']") as "[]". }
    iDestruct ("→W" with "[$Ei]") as "$". iIntros "$ P W".
    iDestruct (sinv_tok_acc' with "i W") as "[[[_ D']|$] →W]".
    { iDestruct (ownD_singleton_twice with "[$D $D']") as "[]". }
    iApply "→W". iLeft. iFrame.
  Qed.
  Lemma inv_tok_acc {intp N E P} :
    ↑N ⊆ E → inv_tok N P =[inv_wsat intp]{E,E∖↑N}=∗
      intp P ∗ (intp P =[inv_wsat intp]{E∖↑N,E}=∗ True).
  Proof.
    iIntros (NE) "iP W". iMod (fupd_ownE_acc NE) as "[N cl]".
    iDestruct (inv_tok_acc' with "N iP W") as "[$[N∖N[$ cl']]]"; [done|].
    iIntros "!> P W". iDestruct ("cl'" with "N∖N P W") as "[$ N]".
    by iApply "cl".
  Qed.
End inv_tok.

(** Allocate [inv_wsat] *)
Lemma inv_wsat_alloc `{!ninvGpreS PROP Σ, !invGS_gen hlc Σ} :
  ⊢ |==> ∃ _ : ninvGS PROP Σ, ∀ intp, inv_wsat intp.
Proof.
  iMod sinv_wsat_alloc as (?) "W". iModIntro. iExists _. iIntros (?).
  rewrite inv_wsat_unseal. iApply "W".
Qed.
