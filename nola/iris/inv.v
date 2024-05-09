(** * Nola later-free invariant *)

From nola.iris Require Export ofe sinv upd.
From iris.base_logic.lib Require Export wsat invariants.
From iris.algebra Require Import gset.
From iris.proofmode Require Import proofmode.

Implicit Type (PROP : oFunctor) (i : positive) (N : namespace).

Class inv'GpreS PROP Σ := inv'GpreS_sinv : sinvGpreS PROP Σ.
Local Existing Instance inv'GpreS_sinv.
Class inv'GS PROP Σ := inv'GS_sinv : sinvGS PROP Σ.
Local Existing Instance inv'GS_sinv.
Definition inv'Σ PROP `{!oFunctorContractive PROP} := #[sinvΣ PROP].
#[export] Instance subG_inv'Σ
  `{!oFunctorContractive PROP, !subG (inv'Σ PROP) Σ} : inv'GpreS PROP Σ.
Proof. solve_inG. Qed.

Section inv.
  Context `{!inv'GS PROP Σ, !invGS_gen hlc Σ}.
  Implicit Type P : PROP $o iProp Σ.

  (** [inv_tok]: Invariant token *)
  Local Definition inv_tok_def N P : iProp Σ :=
    ∃ i, ⌜i ∈ (↑N:coPset)⌝ ∗ sinv_itok i P.
  Local Definition inv_tok_aux : seal inv_tok_def. Proof. by eexists. Qed.
  Definition inv_tok := inv_tok_aux.(unseal).
  Local Lemma inv_tok_unseal : inv_tok = inv_tok_def.
  Proof. exact: seal_eq. Qed.

  (** [inv_tok] is non-expansive *)
  #[export] Instance inv_tok_ne N : NonExpansive (inv_tok N).
  Proof. rewrite inv_tok_unseal. solve_proper. Qed.
  (** [inv_tok] is persistent *)
  #[export] Instance inv_tok_persistent {N P} : Persistent (inv_tok N P).
  Proof. rewrite inv_tok_unseal. exact _. Qed.
  (** [inv_tok] is timeless if the underlying ofe is discrete *)
  #[export] Instance inv_tok_timeless `{!OfeDiscrete (PROP $o iProp Σ)} {N P} :
    Timeless (inv_tok N P).
  Proof. rewrite inv_tok_unseal. exact _. Qed.

  (** Interpretation *)
  Local Definition inv_intp (intp : PROP $o iProp Σ → iProp Σ) i P : iProp Σ :=
    intp P ∗ ownD {[i]} ∨ ownE {[i]}.

  (** [inv_intp intp] is non-expansive when [intp] is *)
  Local Instance inv_intp_ne `{!NonExpansive intp} {i} :
    NonExpansive (inv_intp intp i).
  Proof. solve_proper. Qed.

  (** World satisfaction *)
  Local Definition inv_wsat_def (intp : PROP $o iProp Σ -d> iProp Σ)
    : iProp Σ := sinv_iwsat (inv_intp intp).
  Local Definition inv_wsat_aux : seal inv_wsat_def. Proof. by eexists. Qed.
  Definition inv_wsat := inv_wsat_aux.(unseal).
  Local Lemma inv_wsat_unseal : inv_wsat = inv_wsat_def.
  Proof. exact: seal_eq. Qed.

  (** [inv_wsat] is non-expansive *)
  #[export] Instance inv_wsat_ne : NonExpansive inv_wsat.
  Proof.
    rewrite inv_wsat_unseal. unfold inv_wsat_def, inv_intp. solve_proper.
  Qed.
  #[export] Instance inv_wsat_proper : Proper ((≡) ==> (≡)) inv_wsat.
  Proof. apply ne_proper, _. Qed.

  (** Allocate [inv_tok] *)
  Lemma inv_tok_alloc_rec {intp} P N :
    (inv_tok N P -∗ intp P) =[inv_wsat intp]=∗ inv_tok N P.
  Proof.
    rewrite inv_tok_unseal inv_wsat_unseal. iIntros "→P W".
    iDestruct (sinv_itok_alloc with "W") as (I) "big".
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
  Lemma inv_tok_acc' `{!NonExpansive intp} {N E P} :
    ↑N ⊆ E → ownE E -∗ inv_tok N P -∗ modw id (inv_wsat intp) (
      ownE (E∖↑N) ∗ intp P ∗
      (ownE (E∖↑N) -∗ intp P -∗ modw id (inv_wsat intp) (ownE E))).
  Proof.
    move=> NE. rewrite inv_tok_unseal inv_wsat_unseal (ownE_subset NE).
    iIntros "[N $] [%i[% #iP]] W".
    iDestruct (sinv_tok_acc' with "iP W") as "[in →W]".
    rewrite (ownE_subset (E:=↑N) (F:={[i]})); [|set_solver].
    iDestruct "N" as "[i $]".
    iDestruct "in" as "[[$ D]|i']"; last first.
    { iDestruct (ownE_singleton_twice with "[$i $i']") as "[]". }
    iDestruct ("→W" with "[$i]") as "$". iIntros "$ P W".
    iDestruct (sinv_tok_acc' with "iP W") as "[[[_ D']|$] →W]".
    { iDestruct (ownD_singleton_twice with "[$D $D']") as "[]". }
    iApply "→W". iLeft. iFrame.
  Qed.
  Lemma inv_tok_acc `{!NonExpansive intp} {N E P} :
    ↑N ⊆ E → inv_tok N P =[inv_wsat intp]{E,E∖↑N}=∗
      intp P ∗ (intp P =[inv_wsat intp]{E∖↑N,E}=∗ True).
  Proof.
    iIntros (NE) "iP W". iMod (fupd_ownE_acc NE) as "[N cl]".
    iDestruct (inv_tok_acc' with "N iP W") as "[$[N∖N[$ cl']]]"; [done|].
    iIntros "!> P W". iDestruct ("cl'" with "N∖N P W") as "[$ N]".
    by iApply "cl".
  Qed.
End inv.

(** Allocate [inv_wsat] *)
Lemma inv_wsat_alloc `{!inv'GpreS PROP Σ, !invGS_gen hlc Σ} :
  ⊢ |==> ∃ _ : inv'GS PROP Σ, ∀ intp, inv_wsat intp.
Proof.
  iMod sinv_wsat_alloc as (?) "W". iModIntro. iExists _. iIntros (?).
  rewrite inv_wsat_unseal. iApply "W".
Qed.
