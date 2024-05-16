(** * For non-atomic invariants *)

From nola.util Require Import prod.
From nola.iris Require Export inv.
From iris.base_logic.lib Require Export na_invariants.
From iris.algebra Require Import gset coPset.
From iris.proofmode Require Import proofmode.
Import ProdNotation OfeNotation UpdwNotation.

Implicit Type (PROP : oFunctor) (p : na_inv_pool_name) (i : positive).

(** Proposition data type *)
Local Definition na_inv_prop PROP : oFunctor :=
  leibnizO (na_inv_pool_name *' positive) * PROP.

Class na_inv'GS PROP Σ := na_inv'GS_in : inv'GS (na_inv_prop PROP) Σ.
Local Existing Instance na_inv'GS_in.
Class na_inv'GpreS PROP Σ := na_inv'GpreS_in : inv'GpreS (na_inv_prop PROP) Σ.
Local Existing Instance na_inv'GpreS_in.
Definition na_inv'Σ PROP `{!oFunctorContractive PROP} :=
  #[inv'Σ (na_inv_prop PROP)].
#[export] Instance subG_na_inv'Σ
  `{!oFunctorContractive PROP, !subG (na_inv'Σ PROP) Σ} : na_inv'GpreS PROP Σ.
Proof. solve_inG. Qed.

Section na_inv.
  Context `{!na_inv'GS PROP Σ, !invGS_gen hlc Σ, !na_invG Σ}.
  Local Existing Instance na_inv_inG.

  (** Access l of an non-atomic invariant *)
  Local Definition na_lock p i : iProp Σ := own p (ε, GSet {[i]}).

  (** Allocate [na_lock] *)
  Local Lemma na_lock_alloc p N :
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

  (** Access [na_own] *)
  Local Lemma na_own_subset {p E F} : F ⊆ E →
    na_own p E ⊣⊢ na_own p F ∗ na_own p (E∖F).
  Proof.
    move=> ?. rewrite {1}(union_difference_L F E); [|done].
    by rewrite na_own_union; [|set_solver].
  Qed.
  Lemma na_own_in {p i E} : i ∈ E →
    na_own p E ⊣⊢ na_own p {[i]} ∗ na_own p (E∖{[i]}).
  Proof. move=> ?. apply na_own_subset. set_solver. Qed.

  (** [na_lock] is exclusive *)
  Local Lemma na_lock_2_no {p i} : na_lock p i -∗ na_lock p i -∗ False.
  Proof.
    iIntros "l l'". iCombine "l l'" gives %[_ Hval%gset_disj_valid_op].
    set_solver.
  Qed.

  (** What to be put in a non-atomic invariant *)
  Local Definition na_body p i (P : iProp Σ) : iProp Σ :=
    P ∗ na_lock p i ∨ na_own p {[i]}.

  (** Token for a non-atomic invariant *)
  Local Definition na_inv_tok_def p N (P : PROP $o Σ) : iProp Σ :=
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
  #[export] Instance na_inv_tok_timeless `{!OfeDiscrete (PROP $o Σ)} {p N P} :
    Timeless (na_inv_tok p N P).
  Proof. rewrite na_inv_tok_unseal. exact _. Qed.

  (** Interpretation *)
  Local Definition na_inv_intp (intp : PROP $o Σ -d> iProp Σ)
    : na_inv_prop PROP $o Σ -d> iProp Σ :=
    λ '((p, i)', P), na_body p i (intp P).

  (** [na_inv_intp intp] is non-expansive if [intp] is *)
  Local Instance na_inv_intp_ne `{!NonExpansive intp} :
    NonExpansive (na_inv_intp intp).
  Proof. move=> ?[??][??][/=??]. solve_proper. Qed.

  (** World satisfaction for non-atomic invariants *)
  Local Definition na_inv_wsat_def (intp : PROP $o Σ -d> iProp Σ) : iProp Σ :=
    inv_wsat (na_inv_intp intp).
  Local Lemma na_inv_wsat_aux : seal na_inv_wsat_def. Proof. by eexists. Qed.
  Definition na_inv_wsat := na_inv_wsat_aux.(unseal).
  Local Lemma na_inv_wsat_unseal : na_inv_wsat = na_inv_wsat_def.
  Proof. exact: seal_eq. Qed.

  (** [na_inv_wsat] is non-expansive *)
  #[export] Instance na_inv_wsat_ne : NonExpansive na_inv_wsat.
  Proof.
    rewrite na_inv_wsat_unseal /na_inv_wsat_def=> ????. f_equiv. case=> ??.
    unfold na_inv_intp. solve_proper.
  Qed.
  #[export] Instance na_inv_wsat_proper : Proper ((≡) ==> (≡)) inv_wsat.
  Proof. apply ne_proper, _. Qed.

  (** Allocate [na_inv_tok] *)
  Lemma na_inv_tok_alloc_rec {intp} P p N :
    (na_inv_tok p N P -∗ intp P) =[na_inv_wsat intp]=∗ na_inv_tok p N P.
  Proof.
    rewrite na_inv_tok_unseal na_inv_wsat_unseal.
    iIntros "→P". iMod (na_lock_alloc p N) as (i ?) "l".
    iMod (inv_tok_alloc_rec with "[→P l]"); last first.
    { iModIntro. iExists _. by iSplit. }
    iIntros "i". iLeft. iFrame "l". iApply "→P". iExists _. by iSplit.
  Qed.
  Lemma na_inv_tok_alloc {intp} P p N :
    intp P =[na_inv_wsat intp]=∗ na_inv_tok p N P.
  Proof. iIntros "?". iApply na_inv_tok_alloc_rec. by iIntros. Qed.

  (** Allocate [inv_tok] before storing the content *)
  Lemma na_inv_tok_alloc_open `{!NonExpansive intp} {p N E F P} :
    ↑N ⊆ E → ↑N ⊆ F →
    na_own p F =[na_inv_wsat intp]{E}=∗
      na_own p (F∖↑N) ∗ na_inv_tok p N P ∗
      (na_own p (F∖↑N) -∗ intp P =[na_inv_wsat intp]{E}=∗ na_own p F).
  Proof.
    rewrite na_inv_tok_unseal na_inv_wsat_unseal=> NE NF.
    iMod (na_lock_alloc p N) as (i iN) "l".
    rewrite (na_own_subset NF) (na_own_in iN). iIntros "[[i $]$] W".
    iMod (inv_tok_alloc_open (PROP:=na_inv_prop _) ((p, i)', P) N NE with "W")
      as "[W[iP cl]]".
    iMod ("cl" with "[$i//] W") as "[$ _]". iModIntro.
    iSplit; [iExists _; by iFrame|]. iIntros "$ P W".
    iMod (inv_tok_acc NE with "iP W") as "[W[[[_ l']|$]cl]]".
    { iDestruct (na_lock_2_no with "l l'") as "[]". }
    iMod ("cl" with "[l P] W") as "[$ _]"; [|done]. iLeft. iFrame.
  Qed.

  (** Access [P] from [na_body] *)
  Local Lemma na_body_acc {p i N P} : i ∈ (↑N:coPset) →
    na_own p (↑N) -∗ na_body p i P -∗
      na_body p i P ∗ P ∗ (na_body p i P -∗ P -∗ na_own p (↑N) ∗ na_body p i P).
  Proof.
    move=> iN. rewrite (na_own_in iN). iIntros "[i $] [[$ l]|i']"; last first.
    { iDestruct (na_own_disjoint with "i i'") as %?. set_solver. }
    iSplitL "i"; [by iRight|]. iIntros "[[_ l']|$] P".
    { iDestruct (na_lock_2_no with "l l'") as "[]". }
    iLeft. iFrame.
  Qed.

  (** Access via [na_inv_tok] *)
  Lemma na_inv_tok_acc `{!NonExpansive intp} {p N E F P} : ↑N ⊆ E → ↑N ⊆ F →
    na_own p F -∗ na_inv_tok p N P =[na_inv_wsat intp]{E}=∗
      na_own p (F∖↑N) ∗ intp P ∗
      (na_own p (F∖↑N) -∗ intp P =[na_inv_wsat intp]{E}=∗ na_own p F).
  Proof.
    rewrite na_inv_tok_unseal na_inv_wsat_unseal=> NE NF.
    rewrite (na_own_subset NF). iIntros "[N $] [%i[%iN #iP]] W".
    iMod (inv_tok_acc NE with "iP W") as "[W[bd cl]]".
    iDestruct (na_body_acc iN with "N bd") as "[bd[$ →bd]]".
    iMod ("cl" with "bd W") as "[$ _]". iIntros "!> F∖N P W".
    iMod (inv_tok_acc NE with "iP W") as "[W[bd cl]]".
    iDestruct ("→bd" with "bd P") as "[$ bd]".
    by iMod ("cl" with "bd W") as "[$ _]".
  Qed.
End na_inv.

(** Allocate [na_inv_wsat] *)
Lemma na_inv_wsat_alloc `{!na_inv'GpreS PROP Σ, !invGS_gen hlc Σ, !na_invG Σ} :
  ⊢ |==> ∃ _ : na_inv'GS PROP Σ, ∀ intp, na_inv_wsat intp.
Proof.
  iMod inv_wsat_alloc as (?) "W". iModIntro. iExists _. iIntros (?).
  rewrite na_inv_wsat_unseal. iApply "W".
Qed.
