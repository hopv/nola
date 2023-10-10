(** * For non-atomic invariants *)

From nola.iris Require Export inv.
From iris.base_logic Require Export lib.na_invariants.
From iris.algebra Require Import gset coPset.
From iris.proofmode Require Import proofmode.

Implicit Type PROP : Type.
Implicit Type (p : na_inv_pool_name) (i : positive).

#[projections(primitive)]
Record na_prop PROP := NaProp {
  na_prop_p : na_inv_pool_name;
  na_prop_i : positive;
  na_prop_P : PROP;
}.
Arguments NaProp {_} _ _ _.
Add Printing Constructor na_prop.

Class na_ninvGS PROP Σ := na_ninvGS_in : ninvGS (na_prop PROP) Σ.
Local Existing Instance na_ninvGS_in.
Class na_ninvGpreS PROP Σ := na_ninvGpreS_in : ninvGpreS (na_prop PROP) Σ.
Local Existing Instance na_ninvGpreS_in.
Definition na_ninvΣ PROP : gFunctors := ninvΣ (na_prop PROP).
#[export] Instance subG_na_ninvΣ `{!subG (na_ninvΣ PROP) Σ} :
  na_ninvGpreS PROP Σ.
Proof. solve_inG. Qed.

Section na_ninv.
  Context `{!na_ninvGS PROP Σ, !invGS_gen hlc Σ, !na_invG Σ}.
  Implicit Type intp : PROP -d> iProp Σ.
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
  Local Definition na_inv_tok_def p N (P : PROP) : iProp Σ :=
    ∃ i, ⌜i ∈ (↑N:coPset)⌝ ∗ inv_tok N (NaProp p i P).
  Local Lemma na_inv_tok_aux : seal na_inv_tok_def. Proof. by eexists. Qed.
  Definition na_inv_tok := na_inv_tok_aux.(unseal).
  Local Lemma na_inv_tok_unseal : na_inv_tok = na_inv_tok_def.
  Proof. exact: seal_eq. Qed.

  (** [na_inv_tok] is persistent and timeless *)
  #[export] Instance na_inv_tok_persistent {p N P} :
    Persistent (na_inv_tok p N P).
  Proof. rewrite na_inv_tok_unseal. exact _. Qed.
  #[export] Instance na_inv_tok_timeless {p N P} : Timeless (na_inv_tok p N P).
  Proof. rewrite na_inv_tok_unseal. exact _. Qed.

  (** World satisfaction for non-atomic invariants *)
  Local Definition na_inv_wsat_def intp : iProp Σ :=
    inv_wsat (λ '(NaProp p i P), na_body p i (intp P)).
  Local Lemma na_inv_wsat_aux : seal na_inv_wsat_def. Proof. by eexists. Qed.
  Definition na_inv_wsat := na_inv_wsat_aux.(unseal).
  Local Lemma na_inv_wsat_unseal : na_inv_wsat = na_inv_wsat_def.
  Proof. exact: seal_eq. Qed.

  (** [na_inv_wsat] is non-expansive *)
  #[export] Instance na_inv_wsat_ne : NonExpansive na_inv_wsat.
  Proof.
    rewrite na_inv_wsat_unseal /na_inv_wsat_def=> ????. f_equiv. case=> >.
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
  Lemma na_inv_tok_acc {intp p N E F P} : ↑N ⊆ E → ↑N ⊆ F →
    na_own p F -∗ na_inv_tok p N P =[na_inv_wsat intp]{E}=∗
      na_own p (F∖↑N) ∗ intp P ∗
      (na_own p (F∖↑N) -∗ intp P =[na_inv_wsat intp]{E}=∗ na_own p F).
  Proof.
    rewrite na_inv_tok_unseal na_inv_wsat_unseal=> ??. iIntros "F [%i[% #i]]".
    iMod (inv_tok_acc with "i") as "[bd cl]"; [done|].
    iDestruct (na_body_acc with "F bd") as "[$[bd[$ →bdF]]]"; [done..|].
    iMod ("cl" with "bd") as "_". iIntros "!> F∖N P".
    iMod (inv_tok_acc with "i") as "[bd cl]"; [done|].
    iDestruct ("→bdF" with "F∖N bd P") as "[bd $]". by iApply "cl".
  Qed.
End na_ninv.

(** Allocate [na_inv_wsat] *)
Lemma na_inv_wsat_alloc `{!na_ninvGpreS PROP Σ, !invGS_gen hlc Σ, !na_invG Σ} :
  ⊢ |==> ∃ _ : na_ninvGS PROP Σ, ∀ intp, na_inv_wsat intp.
Proof.
  iMod inv_wsat_alloc as (?) "W". iModIntro. iExists _. iIntros (?).
  rewrite na_inv_wsat_unseal. iApply "W".
Qed.
