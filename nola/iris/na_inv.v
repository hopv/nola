(** * For non-atomic invariants *)

From nola.util Require Import prod.
From nola.iris Require Export inv.
From iris.base_logic.lib Require Export na_invariants.
From iris.algebra Require Import gset coPset.
From iris.proofmode Require Import proofmode.
Import ProdNotation iPropAppNotation UpdwNotation.

Implicit Type (FML : oFunctor) (p : na_inv_pool_name) (i : positive).

(** Proposition data type *)
Local Definition na_inv_prop FML : oFunctor :=
  leibnizO (na_inv_pool_name *' positive) * FML.

Class na_inv'GS FML Σ := na_inv'GS_in : inv'GS (na_inv_prop FML) Σ.
Local Existing Instance na_inv'GS_in.
Class na_inv'GpreS FML Σ := na_inv'GpreS_in : inv'GpreS (na_inv_prop FML) Σ.
Local Existing Instance na_inv'GpreS_in.
Definition na_inv'Σ FML `{!oFunctorContractive FML} :=
  #[inv'Σ (na_inv_prop FML)].
#[export] Instance subG_na_inv'Σ
  `{!oFunctorContractive FML, !subG (na_inv'Σ FML) Σ} : na_inv'GpreS FML Σ.
Proof. solve_inG. Qed.

Section na_inv.
  Context `{!na_inv'GS FML Σ, !invGS_gen hlc Σ, !na_invG Σ}.
  Local Existing Instance na_inv_inG.
  Implicit Type (sm : FML $oi Σ → iProp Σ) (Px : FML $oi Σ) (P : iProp Σ).

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
  Local Definition na_body p i P : iProp Σ := P ∗ na_lock p i ∨ na_own p {[i]}.

  (** Token for a non-atomic invariant *)
  Local Definition na_inv_tok_def p N Px : iProp Σ :=
    ∃ i, ⌜i ∈ (↑N:coPset)⌝ ∗ inv_tok N ((p, i)', Px).
  Local Lemma na_inv_tok_aux : seal na_inv_tok_def. Proof. by eexists. Qed.
  Definition na_inv_tok := na_inv_tok_aux.(unseal).
  Local Lemma na_inv_tok_unseal : na_inv_tok = na_inv_tok_def.
  Proof. exact: seal_eq. Qed.

  (** [na_inv_tok] is non-expansive *)
  #[export] Instance na_inv_tok_ne {p N} : NonExpansive (na_inv_tok p N).
  Proof.
    rewrite na_inv_tok_unseal /na_inv_tok_def=> ????. do 4 f_equiv. by split.
  Qed.
  #[export] Instance na_inv_tok_proper {p N} :
    Proper ((≡) ==> (⊣⊢)) (na_inv_tok p N).
  Proof. apply ne_proper, _. Qed.
  (** [na_inv_tok] is persistent *)
  #[export] Instance na_inv_tok_persistent {p N Px} :
    Persistent (na_inv_tok p N Px).
  Proof. rewrite na_inv_tok_unseal. exact _. Qed.
  (** [na_inv_tok] is timeless for discrete formulas *)
  #[export] Instance na_inv_tok_timeless `{!Discrete Px} {p N} :
    Timeless (na_inv_tok p N Px).
  Proof. rewrite na_inv_tok_unseal. exact _. Qed.

  (** Semantics *)
  Local Definition na_inv_sem (sm : FML $oi Σ -d> iProp Σ)
    : na_inv_prop FML $oi Σ -d> iProp Σ :=
    λ '((p, i)', Px), na_body p i (sm Px).

  (** [na_inv_sem sm] is non-expansive if [sm] is *)
  Local Instance na_inv_sem_ne `{!NonExpansive sm} :
    NonExpansive (na_inv_sem sm).
  Proof. move=> ?[[??]?][[??]?][/=[??]?]. solve_proper. Qed.

  (** World satisfaction for non-atomic invariants *)
  Local Definition na_inv_wsat_def (sm : FML $oi Σ -d> iProp Σ) : iProp Σ :=
    inv_wsat (na_inv_sem sm).
  Local Lemma na_inv_wsat_aux : seal na_inv_wsat_def. Proof. by eexists. Qed.
  Definition na_inv_wsat := na_inv_wsat_aux.(unseal).
  Local Lemma na_inv_wsat_unseal : na_inv_wsat = na_inv_wsat_def.
  Proof. exact: seal_eq. Qed.

  (** [na_inv_wsat] is non-expansive *)
  #[export] Instance na_inv_wsat_ne : NonExpansive na_inv_wsat.
  Proof.
    rewrite na_inv_wsat_unseal /na_inv_wsat_def=> ????. f_equiv. case=> ??.
    unfold na_inv_sem. solve_proper.
  Qed.
  #[export] Instance na_inv_wsat_proper : Proper ((≡) ==> (≡)) inv_wsat.
  Proof. apply ne_proper, _. Qed.

  Context `{!NonExpansive sm}.

  (** Allocate [na_inv_tok] *)
  Lemma na_inv_tok_alloc_rec Px p N :
    (na_inv_tok p N Px -∗ sm Px) =[na_inv_wsat sm]=∗ na_inv_tok p N Px.
  Proof.
    rewrite na_inv_tok_unseal na_inv_wsat_unseal.
    iIntros "→Px". iMod (na_lock_alloc p N) as (i ?) "l".
    iMod (inv_tok_alloc_rec with "[→Px l]"); last first.
    { iModIntro. iExists _. by iSplit. }
    iIntros "i". iLeft. iFrame "l". iApply "→Px". iExists _. by iSplit.
  Qed.
  Lemma na_inv_tok_alloc Px p N :
    sm Px =[na_inv_wsat sm]=∗ na_inv_tok p N Px.
  Proof. iIntros "?". iApply na_inv_tok_alloc_rec. by iIntros. Qed.

  (** Allocate [inv_tok] before storing the content *)
  Lemma na_inv_tok_alloc_open {p N E F Px} : ↑N ⊆ E → ↑N ⊆ F →
    na_own p F =[na_inv_wsat sm]{E}=∗
      na_own p (F∖↑N) ∗ na_inv_tok p N Px ∗
      (na_own p (F∖↑N) -∗ sm Px =[na_inv_wsat sm]{E}=∗ na_own p F).
  Proof.
    rewrite na_inv_tok_unseal na_inv_wsat_unseal=> NE NF.
    iMod (na_lock_alloc p N) as (i iN) "l".
    rewrite (na_own_subset NF) (na_own_in iN). iIntros "[[i $]$] W".
    iMod (inv_tok_alloc_open (FML:=na_inv_prop _) ((p, i)', Px) N NE with "W")
      as "[W[sm cl]]".
    iMod ("cl" with "[$i//] W") as "[$ _]". iModIntro.
    iSplit; [iExists _; by iFrame|]. iIntros "$ Px W".
    iMod (inv_tok_acc NE with "sm W") as "[W[[[_ l']|$]cl]]".
    { iDestruct (na_lock_2_no with "l l'") as %[]. }
    iMod ("cl" with "[l Px] W") as "[$ _]"; [|done]. iLeft. iFrame.
  Qed.

  (** Access [Px] from [na_body] *)
  Local Lemma na_body_acc {p i N P} : i ∈ (↑N:coPset) →
    na_own p (↑N) -∗ na_body p i P -∗
      na_body p i P ∗ P ∗ (na_body p i P -∗ P -∗ na_own p (↑N) ∗ na_body p i P).
  Proof.
    move=> iN. rewrite (na_own_in iN). iIntros "[i $] [[$ l]|i']"; last first.
    { iDestruct (na_own_disjoint with "i i'") as %?. set_solver. }
    iSplitL "i"; [by iRight|]. iIntros "[[_ l']|$] Px".
    { iDestruct (na_lock_2_no with "l l'") as %[]. }
    iLeft. iFrame.
  Qed.

  (** Access via [na_inv_tok] *)
  Lemma na_inv_tok_acc {p N E F Px} : ↑N ⊆ E → ↑N ⊆ F →
    na_own p F -∗ na_inv_tok p N Px =[na_inv_wsat sm]{E}=∗
      na_own p (F∖↑N) ∗ sm Px ∗
      (na_own p (F∖↑N) -∗ sm Px =[na_inv_wsat sm]{E}=∗ na_own p F).
  Proof.
    rewrite na_inv_tok_unseal na_inv_wsat_unseal=> NE NF.
    rewrite (na_own_subset NF). iIntros "[N $] [%i[%iN #sm]] W".
    iMod (inv_tok_acc NE with "sm W") as "[W[bd cl]]".
    iDestruct (na_body_acc iN with "N bd") as "[bd[$ →bd]]".
    iMod ("cl" with "bd W") as "[$ _]". iIntros "!> F∖N Px W".
    iMod (inv_tok_acc NE with "sm W") as "[W[bd cl]]".
    iDestruct ("→bd" with "bd Px") as "[$ bd]".
    by iMod ("cl" with "bd W") as "[$ _]".
  Qed.
End na_inv.

(** Allocate [na_inv_wsat] *)
Lemma na_inv_wsat_alloc `{!na_inv'GpreS FML Σ, !invGS_gen hlc Σ, !na_invG Σ} :
  ⊢ |==> ∃ _ : na_inv'GS FML Σ, ∀ sm, na_inv_wsat sm.
Proof.
  iMod inv_wsat_alloc as (?) "W". iModIntro. iExists _. iIntros (?).
  rewrite na_inv_wsat_unseal. iApply "W".
Qed.
