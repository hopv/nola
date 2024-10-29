(** * Nola later-free invariant *)

From nola.bi Require Export internal modw.
From nola.bi Require Import wpw.
From nola.iris Require Export iprop.
From nola.iris Require Import sinv.
From iris.base_logic.lib Require Export wsat invariants.
From iris.algebra Require Import gset.
From iris.proofmode Require Import proofmode.
Import iPropAppNotation ModwNotation WpwNotation.

Implicit Type (FML : oFunctor) (i : positive) (N : namespace).

Class inv'GpreS FML Σ := inv'GpreS_sinv : sinvGpreS FML Σ.
Local Existing Instance inv'GpreS_sinv.
Class inv'GS FML Σ := inv'GS_sinv : sinvGS FML Σ.
Local Existing Instance inv'GS_sinv.
Definition inv'Σ FML `{!oFunctorContractive FML} := sinvΣ FML.
#[export] Instance subG_inv'Σ
  `{!oFunctorContractive FML, !subG (inv'Σ FML) Σ} : inv'GpreS FML Σ.
Proof. solve_inG. Qed.

Section inv.
  Context `{!inv'GS FML Σ, !invGS_gen hlc Σ}.
  Implicit Type (Px : FML $oi Σ) (sm : FML $oi Σ -d> iProp Σ).

  (** [inv_tok]: Invariant token *)
  Local Definition inv_tok_def (N : namespace) (Px : FML $oi Σ) : iProp Σ :=
    ∃ i, ⌜i ∈ (↑N:coPset)⌝ ∗ sinv_tok i Px.
  Local Definition inv_tok_aux : seal inv_tok_def. Proof. by eexists. Qed.
  Definition inv_tok := inv_tok_aux.(unseal).
  Local Lemma inv_tok_unseal : inv_tok = inv_tok_def.
  Proof. exact: seal_eq. Qed.

  (** [inv_tok] is non-expansive *)
  #[export] Instance inv_tok_ne N : NonExpansive (inv_tok N).
  Proof. rewrite inv_tok_unseal. solve_proper. Qed.
  #[export] Instance inv_tok_proper N : Proper ((≡) ==> (⊣⊢)) (inv_tok N).
  Proof. apply ne_proper, _. Qed.
  (** [inv_tok] is persistent *)
  #[export] Instance inv_tok_persistent {N Px} : Persistent (inv_tok N Px).
  Proof. rewrite inv_tok_unseal. exact _. Qed.
  (** [inv_tok] is timeless for discrete formulas *)
  #[export] Instance inv_tok_timeless `{!Discrete Px} {N} :
    Timeless (inv_tok N Px).
  Proof. rewrite inv_tok_unseal. exact _. Qed.

  (** Semantics *)
  Local Definition inv_sem sm i Px : iProp Σ :=
    sm Px ∗ ownD {[i]} ∨ ownE {[i]}.
  (** [inv_sem sm] is non-expansive when [sm] is *)
  Local Lemma inv_sem_ne {sm} :
    internal_ne sm ⊢@{iProp Σ} ∀ i, internal_ne (inv_sem sm i).
  Proof.
    iIntros "#Ne" (???) "≡". unfold inv_sem. by iRewrite ("Ne" with "≡").
  Qed.

  (** World satisfaction *)
  Local Definition inv_wsat_def sm : iProp Σ := sinv_wsat (inv_sem sm).
  Local Definition inv_wsat_aux : seal inv_wsat_def. Proof. by eexists. Qed.
  Definition inv_wsat := inv_wsat_aux.(unseal).
  Local Lemma inv_wsat_unseal : inv_wsat = inv_wsat_def.
  Proof. exact: seal_eq. Qed.

  (** [inv_wsat] is non-expansive *)
  #[export] Instance inv_wsat_ne : NonExpansive inv_wsat.
  Proof. rewrite inv_wsat_unseal /inv_wsat_def /inv_sem. solve_proper. Qed.
  #[export] Instance inv_wsat_proper : Proper ((≡) ==> (≡)) inv_wsat.
  Proof. apply ne_proper, _. Qed.

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

  (** Allocate [inv_tok] suspending the world satisfaction *)
  Lemma inv_tok_alloc_suspend {sm} Px N :
    inv_wsat sm ==∗ inv_tok N Px ∗ (sm Px -∗ inv_wsat sm).
  Proof.
    rewrite inv_tok_unseal inv_wsat_unseal. iIntros "W".
    iDestruct (sinv_tok_alloc Px with "W") as (I) "big".
    iMod (alloc_ownD I N) as (???) "D". iMod ("big" with "[//]") as "[#i →W]".
    iModIntro. iSplitR; [by iFrame "i"|]. iIntros "?". iApply "→W". iLeft.
    iFrame.
  Qed.
  (** Allocate [inv_tok] *)
  Lemma inv_tok_alloc {sm} Px N : sm Px =[inv_wsat sm]=∗ inv_tok N Px.
  Proof.
    iIntros "? W". iMod (inv_tok_alloc_suspend with "W") as "[$ →W]". iModIntro.
    by iApply "→W".
  Qed.

  (** Allocate [inv_tok] before storing the content *)
  Lemma inv_tok_alloc_open {sm E} Px N : ↑N ⊆ E →
    ⊢ |=[inv_wsat sm]{E, E∖↑N}=> inv_tok N Px ∗
      (sm Px =[inv_wsat sm]{E∖↑N, E}=∗ True).
  Proof.
    rewrite inv_tok_unseal inv_wsat_unseal=> NE. iIntros "W".
    iDestruct (sinv_tok_alloc Px with "W") as (I) "big".
    iMod (alloc_ownD I N) as (?? iN) "D".
    iMod ("big" with "[//]") as "[#sm →W]".
    iMod (fupd_ownE_acc_in iN NE) as "[i cl]".
    iDestruct ("→W" with "[$i]") as "$". iModIntro.
    iSplit; [iExists _; by iSplit|]. iIntros "Px W".
    iDestruct (sinv_tok_acc with "sm W") as "[[[_ D']|i] →W]".
    { iDestruct (ownD_singleton_twice with "[$D $D']") as %[]. }
    iMod ("cl" with "i") as "_". iModIntro. iSplit; [|done]. iApply "→W".
    iLeft. iFrame.
  Qed.

  (** Access using [inv_tok] *)
  Lemma inv_tok_acc {sm N E Px} : ↑N ⊆ E →
    inv_tok N Px =[inv_wsat sm]{E,E∖↑N}=∗
      sm Px ∗ (sm Px =[inv_wsat sm]{E∖↑N,E}=∗ True).
  Proof.
    rewrite inv_tok_unseal inv_wsat_unseal=> NE. iIntros "[%i[%iN #sm]] W".
    iMod (fupd_ownE_acc_in iN NE) as "[i cl]".
    iDestruct (sinv_tok_acc with "sm W") as "[in →W]".
    iDestruct "in" as "[[$ D]|i']"; last first.
    { iDestruct (ownE_singleton_twice with "[$i $i']") as %[]. }
    iDestruct ("→W" with "[$i]") as "$". iIntros "!> Px W".
    iDestruct (sinv_tok_acc with "sm W") as "[[[_ D']|i] →W]".
    { iDestruct (ownD_singleton_twice with "[$D $D']") as %[]. }
    iMod ("cl" with "i") as "_". iModIntro. iSplit; [|done]. iApply "→W".
    iLeft. iFrame.
  Qed.
  (** Access using [inv_tok] via view shift *)
  Lemma inv_tok_acc_vs {sm N Px E Q R} : ↑N ⊆ E →
    □ (sm Px -∗ Q =[inv_wsat sm]{E∖↑N}=∗ sm Px ∗ R) -∗
    □ (inv_tok N Px -∗ Q =[inv_wsat sm]{E}=∗ R).
  Proof.
    iIntros (?) "#vs !> i Q". iMod (inv_tok_acc with "i") as "[Px cl]"; [done|].
    iMod ("vs" with "Px Q") as "[Px $]". by iApply "cl".
  Qed.
End inv.

Section inv_wp.
  Context `{!inv'GS FML Σ, !iris'GS_gen hlc Λ Σ}.

  (** Access using [inv_tok] via [twp] *)
  Lemma inv_tok_acc_twp `{!Atomic (stuckness_to_atomicity s) e}
    {sm N Px E Q Ψ} :
    ↑N ⊆ E → to_val e = None →
    [[{ sm Px ∗ Q }]][inv_wsat sm] e @ s; E∖↑N [[{ v, RET v; sm Px ∗ Ψ v }]] -∗
      [[{ inv_tok N Px ∗ Q }]][inv_wsat sm] e @ s; E [[{ v, RET v; Ψ v }]].
  Proof.
    iIntros (??) "#twp %Φ !> [i Q] →Φ".
    iMod (inv_tok_acc with "i") as "[Px cl]"; [done..|].
    iApply ("twp" with "[$Px $Q //]"). iIntros (?) "[Px Ψ]".
    iMod ("cl" with "Px") as "_". iModIntro. by iApply "→Φ".
  Qed.
End inv_wp.

(** Allocate [inv_wsat] *)
Lemma inv_wsat_alloc `{!inv'GpreS FML Σ, !invGS_gen hlc Σ} :
  ⊢ |==> ∃ _ : inv'GS FML Σ, ∀ sm, internal_ne sm -∗ inv_wsat sm.
Proof.
  iMod sinv_wsat_alloc as (?) "W". iModIntro. iExists _. iIntros (?) "Ne".
  rewrite inv_wsat_unseal. iApply "W". iApply (inv_sem_ne with "Ne").
Qed.
