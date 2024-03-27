(** * For non-atomic invariants *)

From nola.util Require Import prod.
From nola.iris Require Export ofe inv.
From iris.base_logic Require Export lib.na_invariants.
From iris.algebra Require Import gset coPset.
From iris.proofmode Require Import proofmode.

Implicit Type (PROP : oFunctor) (p : na_inv_pool_name) (i : positive).

(** Proposition data type *)
Local Definition na_inv_prop PROP : oFunctor :=
  leibnizO (na_inv_pool_name *' positive) * PROP.

Class na_ninvGS PROP Σ := na_ninvGS_in : ninvGS (na_inv_prop PROP) Σ.
Local Existing Instance na_ninvGS_in.
Class na_ninvGpreS PROP Σ := na_ninvGpreS_in : ninvGpreS (na_inv_prop PROP) Σ.
Local Existing Instance na_ninvGpreS_in.
Definition na_ninvΣ PROP `{!oFunctorContractive PROP} :=
  #[ninvΣ (na_inv_prop PROP)].
#[export] Instance subG_na_ninvΣ
  `{!oFunctorContractive PROP, !subG (na_ninvΣ PROP) Σ} : na_ninvGpreS PROP Σ.
Proof. solve_inG. Qed.

Section na_ninv.
  Context `{!na_ninvGS PROP Σ, !invGS_gen hlc Σ, !na_invG Σ}.
  Local Existing Instance na_inv_inG.

  (** Access l of an non-atomic invariant *)
  Local Definition na_lock p i : iProp Σ := own p (ε, GSet {[i]}).

  (** Allocate [na_lock] *)
  Local Lemma na_lock_alloc {p N} :
    ⊢ |==> ∃ i, ⌜i ∈ (↑N:coPset)⌝ ∧ na_lock p i.
  Proof.
    iMod (own_unit (prodUR coPset_disjUR (gset_disjUR positive)) p) as "ε".
    iMod (own_updateP with "ε") as ([m1 m2]) "[%cond l]".
    { apply prod_updateP'.
      - apply cmra_updateP_id, (reflexivity (R:=eq)).
      - apply (gset_disj_alloc_empty_updateP_strong' (.∈ (↑N:coPset)))=> ?.
        apply fresh_inv_name. }
    move: cond=>/=[<-[i[->?]]]. iModIntro. iExists i. by iSplit.
  Qed.

  (** What to be put in a non-atomic invariant *)
  Local Definition na_body p i (P : iProp Σ) : iProp Σ :=
    P ∗ na_lock p i ∨ na_own p {[i]}.

  (** Access [P] from [na_body] *)
  Local Lemma na_body_acc {p i N E P} : i ∈ (↑N:coPset) → ↑N ⊆ E →
    na_own p E -∗ na_body p i P -∗
      na_own p (E∖↑N) ∗ na_body p i P ∗ P ∗
      (na_own p (E∖↑N) -∗ na_body p i P -∗ P -∗ na_body p i P ∗ na_own p E).
  Proof.
    iIntros (??) "E [[$ l]|i]"; last first.
    { iDestruct (na_own_disjoint with "i E") as %?. set_solver. }
    rewrite [E as X in na_own p X](union_difference_L (↑N) E); [|done].
    rewrite [X in (X ∪ _)](union_difference_L {[i]} (↑N)) ?na_own_union;
      [|set_solver..].
    iDestruct "E" as "[[$$] $]". iIntros "$ [[_ l']|i] P".
    - iCombine "l l'" gives %[_ Hval%gset_disj_valid_op]. set_solver.
    - iSplitR "i"; [|done]. iLeft. iFrame.
  Qed.

  (** Token for a non-atomic invariant *)
  Local Definition na_inv_tok_def p N (P : PROP $o iProp Σ) : iProp Σ :=
    ∃ i, ⌜i ∈ (↑N:coPset)⌝ ∗ inv_tok N ((p, i)', P).
  Local Lemma na_inv_tok_aux : seal na_inv_tok_def. Proof. by eexists. Qed.
  Definition na_inv_tok := na_inv_tok_aux.(unseal).
  Local Lemma na_inv_tok_unseal : na_inv_tok = na_inv_tok_def.
  Proof. exact: seal_eq. Qed.

  (** [na_inv_tok] is non-expansive *)
  #[export] Instance na_inv_tok_ne p N : NonExpansive (na_inv_tok p N).
  Proof.
    rewrite na_inv_tok_unseal /na_inv_tok_def=> ????. do 4 f_equiv. by split.
  Qed.
  (** [na_inv_tok] is persistent *)
  #[export] Instance na_inv_tok_persistent {p N P} :
    Persistent (na_inv_tok p N P).
  Proof. rewrite na_inv_tok_unseal. exact _. Qed.
  (** [na_inv_tok] is timeless if the underlying ofe is discrete *)
  #[export] Instance na_inv_tok_timeless
    `{!OfeDiscrete (PROP $o iProp Σ)} {p N P} : Timeless (na_inv_tok p N P).
  Proof. rewrite na_inv_tok_unseal. exact _. Qed.

  (** Interpretation *)
  Local Definition na_inv_intp (intp : PROP $o iProp Σ -d> iProp Σ)
    : na_inv_prop PROP $o iProp Σ -d> iProp Σ :=
    λ '((p, i)', P), na_body p i (intp P).

  (** [na_inv_intp intp] is non-expansive if [intp] is *)
  Local Instance na_inv_intp_ne `{!NonExpansive intp} :
    NonExpansive (na_inv_intp intp).
  Proof. move=> ?[??][??][/=??]. solve_proper. Qed.

  (** World satisfaction for non-atomic invariants *)
  Local Definition na_inv_wsat_def (intp : PROP $o iProp Σ -d> iProp Σ)
    : iProp Σ := inv_wsat (λ '((p, i)', P), na_body p i (intp P)).
  Local Lemma na_inv_wsat_aux : seal na_inv_wsat_def. Proof. by eexists. Qed.
  Definition na_inv_wsat := na_inv_wsat_aux.(unseal).
  Local Lemma na_inv_wsat_unseal : na_inv_wsat = na_inv_wsat_def.
  Proof. exact: seal_eq. Qed.

  (** [na_inv_wsat] is non-expansive *)
  #[export] Instance na_inv_wsat_ne : NonExpansive na_inv_wsat.
  Proof.
    rewrite na_inv_wsat_unseal /na_inv_wsat_def=> ????. f_equiv. case=> ??.
    solve_proper.
  Qed.
  #[export] Instance na_inv_wsat_proper : Proper ((≡) ==> (≡)) inv_wsat.
  Proof. apply ne_proper, _. Qed.

  (** Allocate [na_inv_tok] *)
  Lemma na_inv_tok_alloc_rec {intp} P p N :
    (na_inv_tok p N P -∗ intp P) =[na_inv_wsat intp]=∗ na_inv_tok p N P.
  Proof.
    rewrite na_inv_tok_unseal na_inv_wsat_unseal.
    iIntros "→P". iMod na_lock_alloc as (i ?) "l".
    iMod (inv_tok_alloc_rec with "[→P l]"); last first.
    { iModIntro. iExists _. by iSplit. }
    iIntros "i". iLeft. iFrame "l". iApply "→P". iExists _. by iSplit.
  Qed.
  Lemma na_inv_tok_alloc {intp} P p N :
    intp P =[na_inv_wsat intp]=∗ na_inv_tok p N P.
  Proof. iIntros "?". iApply na_inv_tok_alloc_rec. by iIntros. Qed.

  (** Access [na_inv_tok] *)
  Lemma na_inv_tok_acc' `{!NonExpansive intp} {p N E F P} : ↑N ⊆ E → ↑N ⊆ F →
    ownE E -∗ na_own p F -∗ na_inv_tok p N P -∗ modw id (na_inv_wsat intp) (
      ownE E ∗ na_own p (F∖↑N) ∗ intp P ∗
      (ownE E -∗ na_own p (F∖↑N) -∗ intp P -∗ modw id (na_inv_wsat intp) (
        (ownE E ∗ na_own p F)))).
  Proof.
    rewrite na_inv_tok_unseal na_inv_wsat_unseal=> ??.
    iIntros "E F [%i[% #iP]] W".
    iDestruct (inv_tok_acc' with "E iP W") as "[W[E∖N[bd cl]]]"; [done|].
    iDestruct (na_body_acc with "F bd") as "[$[bd[$ →bdF]]]"; [done..|].
    iDestruct ("cl" with "E∖N bd W") as "[$$]". iIntros "E F∖N P W".
    iDestruct (inv_tok_acc' with "E iP W") as "[W[E∖N[bd cl]]]"; [done|].
    iDestruct ("→bdF" with "F∖N bd P") as "[bd $]".
    iApply ("cl" with "E∖N bd W").
  Qed.
  Lemma na_inv_tok_acc `{!NonExpansive intp} {p N E F P} : ↑N ⊆ E → ↑N ⊆ F →
    na_own p F -∗ na_inv_tok p N P =[na_inv_wsat intp]{E}=∗
      na_own p (F∖↑N) ∗ intp P ∗
      (na_own p (F∖↑N) -∗ intp P =[na_inv_wsat intp]{E}=∗ na_own p F).
  Proof.
    iIntros (NE ?) "F iP W". iMod (fupd_ownE_acc NE) as "[N cl]".
    iDestruct (na_inv_tok_acc' with "N F iP W") as "[$[N[$[$ cl']]]]";
      [done..|].
    iMod ("cl" with "N") as "_". iIntros "!> F∖N P W".
    iMod (fupd_ownE_acc NE) as "[N cl]".
    iDestruct ("cl'" with "N F∖N P W") as "[$[N $]]". by iApply "cl".
  Qed.
End na_ninv.

(** Allocate [na_inv_wsat] *)
Lemma na_inv_wsat_alloc `{!na_ninvGpreS PROP Σ, !invGS_gen hlc Σ, !na_invG Σ} :
  ⊢ |==> ∃ _ : na_ninvGS PROP Σ, ∀ intp, na_inv_wsat intp.
Proof.
  iMod inv_wsat_alloc as (?) "W". iModIntro. iExists _. iIntros (?).
  rewrite na_inv_wsat_unseal. iApply "W".
Qed.
