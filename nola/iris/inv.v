(** * Nola later-free invariant *)

From nola.iris Require Export sinv.
From iris.base_logic.lib Require Export wsat invariants.
From iris.algebra Require Import gset.
From iris.proofmode Require Import proofmode.
Import iPropAppNotation UpdwNotation.

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
  Implicit Type (ip : PROP $oi Σ → iProp Σ) (P : PROP $oi Σ).

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
  #[export] Instance inv_tok_timeless `{!OfeDiscrete (PROP $oi Σ)} {N P} :
    Timeless (inv_tok N P).
  Proof. rewrite inv_tok_unseal. exact _. Qed.

  (** Interpretation *)
  Local Definition inv_intp (ip : PROP $oi Σ → iProp Σ) i P : iProp Σ :=
    ip P ∗ ownD {[i]} ∨ ownE {[i]}.

  (** [inv_intp ip] is non-expansive when [ip] is *)
  Local Instance inv_intp_ne `{!NonExpansive ip} {i} :
    NonExpansive (inv_intp ip i).
  Proof. solve_proper. Qed.

  (** World satisfaction *)
  Local Definition inv_wsat_def (ip : PROP $oi Σ -d> iProp Σ) : iProp Σ :=
    sinv_iwsat (inv_intp ip).
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

  Context `{!NonExpansive ip}.

  (** Allocate [ownD] *)
  Lemma alloc_ownD (I : gset positive) N :
    ⊢ |==> ∃ i, ⌜i ∉ I⌝ ∗ ⌜i ∈ (↑N:coPset)⌝ ∗ ownD {[i]}.
  Proof.
    iMod (own_unit (gset_disjUR positive) disabled_name) as "D".
    iMod (own_updateP with "[$]") as (x) "[X D]".
    { apply (gset_disj_alloc_empty_updateP_strong'
        (λ i, i ∉ I ∧ i ∈ (↑N:coPset)))=> J.
      case: (fresh_inv_name (I ∪ J) N)=> [i[/not_elem_of_union[??]?]].
      by exists i. }
    iDestruct "X" as %[i[->[??]]]. iModIntro. iExists i. iSplit; by [|iSplit].
  Qed.

  (** Access [ownE] *)
  Local Lemma ownE_subset {E F} : F ⊆ E → ownE E ⊣⊢ ownE F ∗ ownE (E∖F).
  Proof.
    move=> ?. rewrite {1}(union_difference_L F E); [|done].
    by rewrite ownE_op; [|set_solver].
  Qed.
  (** Access [ownE] from [fupd] *)
  Local Lemma fupd_ownE_acc {E F} : F ⊆ E →
    ⊢ |={E,E∖F}=> ownE F ∗ (ownE F ={E∖F,E}=∗ True).
  Proof.
    rewrite fancy_updates.uPred_fupd_unseal /fancy_updates.uPred_fupd_def=> FE.
    rewrite (ownE_subset FE). by iIntros "[$[$$]]!>!>$[$$]!>".
  Qed.
  Local Lemma fupd_ownE_acc_in {i E F} : i ∈ F → F ⊆ E →
    ⊢ |={E,E∖F}=> ownE {[i]} ∗ (ownE {[i]} ={E∖F,E}=∗ True).
  Proof.
    move=> iF FE. iMod (fupd_ownE_acc FE) as "[F cl]".
    rewrite (ownE_subset (E:=F) (F:={[i]})); [|set_solver].
    iDestruct "F" as "[$ F∖i]". iIntros "!> i". iApply ("cl" with "[$]").
  Qed.

  (** Allocate [inv_tok] *)
  Lemma inv_tok_alloc_rec P N :
    (inv_tok N P -∗ ip P) =[inv_wsat ip]=∗ inv_tok N P.
  Proof.
    rewrite inv_tok_unseal inv_wsat_unseal. iIntros "→P W".
    iDestruct (sinv_itok_alloc P with "W") as (I) "big".
    iMod (alloc_ownD I N) as (???) "D". iMod ("big" with "[//]") as "[#i →W]".
    iModIntro. iSplitL; [|iExists _; by iSplit]. iApply "→W". iLeft.
    iSplitR "D"; [|done]. iApply "→P". iExists _; by iSplit.
  Qed.
  Lemma inv_tok_alloc P N : ip P =[inv_wsat ip]=∗ inv_tok N P.
  Proof.
    iIntros "P W". iApply (inv_tok_alloc_rec with "[P] W"). by iIntros.
  Qed.

  (** Allocate [inv_tok] before storing the content *)
  Lemma inv_tok_alloc_open {E} P N : ↑N ⊆ E →
    ⊢ |=[inv_wsat ip]{E, E∖↑N}=> inv_tok N P ∗
      (ip P =[inv_wsat ip]{E∖↑N, E}=∗ True).
  Proof.
    rewrite inv_tok_unseal inv_wsat_unseal=> NE. iIntros "W".
    iDestruct (sinv_itok_alloc P with "W") as (I) "big".
    iMod (alloc_ownD I N) as (?? iN) "D".
    iMod ("big" with "[//]") as "[#iP →W]".
    iMod (fupd_ownE_acc_in iN NE) as "[i cl]".
    iDestruct ("→W" with "[$i]") as "$". iModIntro.
    iSplit; [iExists _; by iSplit|]. iIntros "P W".
    iDestruct (sinv_tok_acc' with "iP W") as "[[[_ D']|i] →W]".
    { iDestruct (ownD_singleton_twice with "[$D $D']") as "[]". }
    iMod ("cl" with "i") as "_". iModIntro. iSplit; [|done]. iApply "→W".
    iLeft. iFrame.
  Qed.

  (** Access using [inv_tok] *)
  Lemma inv_tok_acc {N E P} : ↑N ⊆ E →
    inv_tok N P =[inv_wsat ip]{E,E∖↑N}=∗
      ip P ∗ (ip P =[inv_wsat ip]{E∖↑N,E}=∗ True).
  Proof.
    rewrite inv_tok_unseal inv_wsat_unseal=> NE. iIntros "[%i[%iN #iP]] W".
    iMod (fupd_ownE_acc_in iN NE) as "[i cl]".
    iDestruct (sinv_tok_acc' with "iP W") as "[in →W]".
    iDestruct "in" as "[[$ D]|i']"; last first.
    { iDestruct (ownE_singleton_twice with "[$i $i']") as "[]". }
    iDestruct ("→W" with "[$i]") as "$". iIntros "!> P W".
    iDestruct (sinv_tok_acc' with "iP W") as "[[[_ D']|i] →W]".
    { iDestruct (ownD_singleton_twice with "[$D $D']") as "[]". }
    iMod ("cl" with "i") as "_". iModIntro. iSplit; [|done]. iApply "→W".
    iLeft. iFrame.
  Qed.
End inv.

(** Allocate [inv_wsat] *)
Lemma inv_wsat_alloc `{!inv'GpreS PROP Σ, !invGS_gen hlc Σ} :
  ⊢ |==> ∃ _ : inv'GS PROP Σ, ∀ ip, inv_wsat ip.
Proof.
  iMod sinv_wsat_alloc as (?) "W". iModIntro. iExists _. iIntros (?).
  rewrite inv_wsat_unseal. iApply "W".
Qed.
