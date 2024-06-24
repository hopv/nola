(** * Nola later-free invariant *)

From nola.iris Require Export sinv.
From iris.base_logic.lib Require Export wsat invariants.
From iris.algebra Require Import gset.
From iris.proofmode Require Import proofmode.
Import iPropAppNotation UpdwNotation.

Implicit Type (FML : oFunctor) (i : positive) (N : namespace).

Class inv'GpreS FML Σ := inv'GpreS_sinv : sinvGpreS FML Σ.
Local Existing Instance inv'GpreS_sinv.
Class inv'GS FML Σ := inv'GS_sinv : sinvGS FML Σ.
Local Existing Instance inv'GS_sinv.
Definition inv'Σ FML `{!oFunctorContractive FML} := #[sinvΣ FML].
#[export] Instance subG_inv'Σ
  `{!oFunctorContractive FML, !subG (inv'Σ FML) Σ} : inv'GpreS FML Σ.
Proof. solve_inG. Qed.

Section inv.
  Context `{!inv'GS FML Σ, !invGS_gen hlc Σ}.
  Implicit Type (sm : FML $oi Σ → iProp Σ) (P : FML $oi Σ).

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
  (** [inv_tok] is timeless for discrete formulas *)
  #[export] Instance inv_tok_timeless `{!Discrete P} {N} :
    Timeless (inv_tok N P).
  Proof. rewrite inv_tok_unseal. exact _. Qed.

  (** Semantics *)
  Local Definition inv_sem (sm : FML $oi Σ → iProp Σ) i P : iProp Σ :=
    sm P ∗ ownD {[i]} ∨ ownE {[i]}.

  (** [inv_sem sm] is non-expansive when [sm] is *)
  Local Instance inv_sem_ne `{!NonExpansive sm} {i} :
    NonExpansive (inv_sem sm i).
  Proof. solve_proper. Qed.

  (** World satisfaction *)
  Local Definition inv_wsat_def (sm : FML $oi Σ -d> iProp Σ) : iProp Σ :=
    sinv_iwsat (inv_sem sm).
  Local Definition inv_wsat_aux : seal inv_wsat_def. Proof. by eexists. Qed.
  Definition inv_wsat := inv_wsat_aux.(unseal).
  Local Lemma inv_wsat_unseal : inv_wsat = inv_wsat_def.
  Proof. exact: seal_eq. Qed.

  (** [inv_wsat] is non-expansive *)
  #[export] Instance inv_wsat_ne : NonExpansive inv_wsat.
  Proof.
    rewrite inv_wsat_unseal. unfold inv_wsat_def, inv_sem. solve_proper.
  Qed.
  #[export] Instance inv_wsat_proper : Proper ((≡) ==> (≡)) inv_wsat.
  Proof. apply ne_proper, _. Qed.

  Context `{!NonExpansive sm}.

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
    (inv_tok N P -∗ sm P) =[inv_wsat sm]=∗ inv_tok N P.
  Proof.
    rewrite inv_tok_unseal inv_wsat_unseal. iIntros "→P W".
    iDestruct (sinv_itok_alloc P with "W") as (I) "big".
    iMod (alloc_ownD I N) as (???) "D". iMod ("big" with "[//]") as "[#i →W]".
    iModIntro. iSplitL; [|iExists _; by iSplit]. iApply "→W". iLeft.
    iSplitR "D"; [|done]. iApply "→P". iExists _; by iSplit.
  Qed.
  Lemma inv_tok_alloc P N : sm P =[inv_wsat sm]=∗ inv_tok N P.
  Proof.
    iIntros "P W". iApply (inv_tok_alloc_rec with "[P] W"). by iIntros.
  Qed.

  (** Allocate [inv_tok] before storing the content *)
  Lemma inv_tok_alloc_open {E} P N : ↑N ⊆ E →
    ⊢ |=[inv_wsat sm]{E, E∖↑N}=> inv_tok N P ∗
      (sm P =[inv_wsat sm]{E∖↑N, E}=∗ True).
  Proof.
    rewrite inv_tok_unseal inv_wsat_unseal=> NE. iIntros "W".
    iDestruct (sinv_itok_alloc P with "W") as (I) "big".
    iMod (alloc_ownD I N) as (?? iN) "D".
    iMod ("big" with "[//]") as "[#sm →W]".
    iMod (fupd_ownE_acc_in iN NE) as "[i cl]".
    iDestruct ("→W" with "[$i]") as "$". iModIntro.
    iSplit; [iExists _; by iSplit|]. iIntros "P W".
    iDestruct (sinv_tok_acc' with "sm W") as "[[[_ D']|i] →W]".
    { iDestruct (ownD_singleton_twice with "[$D $D']") as "[]". }
    iMod ("cl" with "i") as "_". iModIntro. iSplit; [|done]. iApply "→W".
    iLeft. iFrame.
  Qed.

  (** Access using [inv_tok] *)
  Lemma inv_tok_acc {N E P} : ↑N ⊆ E →
    inv_tok N P =[inv_wsat sm]{E,E∖↑N}=∗
      sm P ∗ (sm P =[inv_wsat sm]{E∖↑N,E}=∗ True).
  Proof.
    rewrite inv_tok_unseal inv_wsat_unseal=> NE. iIntros "[%i[%iN #sm]] W".
    iMod (fupd_ownE_acc_in iN NE) as "[i cl]".
    iDestruct (sinv_tok_acc' with "sm W") as "[in →W]".
    iDestruct "in" as "[[$ D]|i']"; last first.
    { iDestruct (ownE_singleton_twice with "[$i $i']") as "[]". }
    iDestruct ("→W" with "[$i]") as "$". iIntros "!> P W".
    iDestruct (sinv_tok_acc' with "sm W") as "[[[_ D']|i] →W]".
    { iDestruct (ownD_singleton_twice with "[$D $D']") as "[]". }
    iMod ("cl" with "i") as "_". iModIntro. iSplit; [|done]. iApply "→W".
    iLeft. iFrame.
  Qed.
End inv.

(** Allocate [inv_wsat] *)
Lemma inv_wsat_alloc `{!inv'GpreS FML Σ, !invGS_gen hlc Σ} :
  ⊢ |==> ∃ _ : inv'GS FML Σ, ∀ sm, inv_wsat sm.
Proof.
  iMod sinv_wsat_alloc as (?) "W". iModIntro. iExists _. iIntros (?).
  rewrite inv_wsat_unseal. iApply "W".
Qed.
