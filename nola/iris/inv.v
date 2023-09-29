(** * Nola later-free invariant *)

From nola.iris Require Export upd.
From iris.algebra Require Import gmap_view gset coPset.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export own wsat fancy_updates invariants.

(** ** Resources *)

Class ninvGpreS (PROP : Type) (Σ : gFunctors) := NinvGpreS {
  ninvGpreS_inv :: inG Σ (gmap_viewR positive (leibnizO PROP));
}.
Class ninvGS (PROP : Type) (Σ : gFunctors) := NinvGS {
  ninv_inG :: ninvGpreS PROP Σ;
  ninv_name : gname;
}.

Definition ninvΣ (PROP : Type) : gFunctors :=
  #[GFunctor (gmap_viewRF positive (leibnizO PROP))].
#[export] Instance subG_ninvΣ `{!subG (ninvΣ PROP) Σ} : ninvGpreS PROP Σ.
Proof. solve_inG. Qed.

Section ninv.
  Context `{!invGS_gen hlc Σ, !ninvGS PROP Σ}.

  (** ** Propositions *)

  (** [ownNi]: Basic invariant token *)
  Local Definition ownNi (i : positive) (P : PROP) : iProp Σ :=
    own ninv_name (gmap_view_frag i DfracDiscarded (P : leibnizO _)).

  (** [ninv]: Invariant token *)
  Local Definition ninv_def (N : namespace) (P : PROP) : iProp Σ :=
    ∃ i, ⌜i ∈ (↑N:coPset)⌝ ∧ ownNi i P.
  Local Definition ninv_aux : seal ninv_def. Proof. by eexists. Qed.
  Definition ninv := ninv_aux.(unseal).
  Local Lemma ninv_unseal : ninv = ninv_def.
  Proof. exact ninv_aux.(seal_eq). Qed.
  #[export] Instance ninv_timeless {N P} : Timeless (ninv N P).
  Proof. rewrite ninv_unseal. exact _. Qed.
  #[export] Instance ninv_persistent {N P} : Persistent (ninv N P).
  Proof. rewrite ninv_unseal. exact _. Qed.

  (** [ninv_wsat]: Invariant world satisfaction *)
  Local Definition authNi (Ps : gmap positive (leibnizO PROP)) :=
    own ninv_name (gmap_view_auth (DfracOwn 1) Ps).
  Local Definition ninv_wsat_def (intp : PROP -d> iProp Σ) : iProp Σ :=
    ∃ Ps, authNi Ps ∗ [∗ map] i ↦ P ∈ Ps, intp P ∗ ownD {[i]} ∨ ownE {[i]}.
  Local Definition ninv_wsat_aux : seal ninv_wsat_def. Proof. by eexists. Qed.
  Definition ninv_wsat := ninv_wsat_aux.(unseal).
  Local Lemma ninv_wsat_unseal : ninv_wsat = ninv_wsat_def.
  Proof. exact ninv_wsat_aux.(seal_eq). Qed.
  #[export] Instance ninv_wsat_ne : NonExpansive ninv_wsat.
  Proof. rewrite ninv_wsat_unseal. solve_proper. Qed.
  #[export] Instance ninv_wsat_proper : Proper ((≡) ==> (≡)) ninv_wsat.
  Proof. apply ne_proper, _. Qed.

  (** ** Lemmas *)

  (** ** Lookup in [authNi] *)
  Local Lemma authNi_lookup {Ps i P} :
    authNi Ps -∗ ownNi i P -∗ ⌜Ps !! i = Some P⌝.
  Proof.
    iIntros "aPs iP". unfold authNi, ownNi. iCombine "aPs iP" as "eq".
    rewrite own_valid gmap_view_both_validI bi.and_elim_r.
    iDestruct "eq" as %eq. by apply leibniz_equiv in eq.
  Qed.

  (** Open and close by [ownNi] *)
  Local Lemma ownNi_open {intp i P} :
    ownNi i P -∗ ownE {[i]} -∗ ninv_wsat intp -∗
      ninv_wsat intp ∗ intp P ∗ ownD {[i]}.
  Proof.
    rewrite ninv_wsat_unseal. iIntros "iP Ei (%Ps & aPs & W)".
    iDestruct (authNi_lookup with "aPs iP") as %eqP.
    iDestruct (big_sepM_delete with "W") as "[[[$$]|Ei'] W]";
      [done| |iDestruct (ownE_singleton_twice with "[$]") as "[]"].
    iExists _. iFrame "aPs". iApply big_sepM_delete; [done|]. iFrame.
  Qed.
  Local Lemma ownNi_close {intp i P} :
    ownNi i P -∗ intp P -∗ ownD {[i]} -∗ ninv_wsat intp -∗
      ninv_wsat intp ∗ ownE {[i]}.
  Proof.
    rewrite ninv_wsat_unseal. iIntros "iP P Di (%Ps & aPs & W)".
    iDestruct (authNi_lookup with "aPs iP") as %eqP.
    iDestruct (big_sepM_delete with "W") as "[[[_ Di']|$] W]";
      [done|iDestruct (ownD_singleton_twice with "[$]") as %[]|].
    iExists _. iFrame "aPs". iApply big_sepM_delete; [done|]. iFrame "W".
    iLeft. iFrame.
  Qed.

  (** Allocate [ownNi] *)
  Local Lemma ownNi_alloc_rec {intp P} φ :
    (∀ E : gset positive, ∃ i, i ∉ E ∧ φ i) →
    (∀ i, ⌜φ i⌝ → ownNi i P -∗ intp P) -∗ ninv_wsat intp ==∗
      ∃ i, ⌜φ i⌝ ∗ ninv_wsat intp ∗ ownNi i P.
  Proof.
    rewrite ninv_wsat_unseal. iIntros (fresh) "→P (%Ps & aPs & W)".
    iMod (own_unit (gset_disjUR positive) disabled_name) as "?".
    iMod (own_updateP with "[$]") as (I) "[X DI]".
    { apply (gset_disj_alloc_empty_updateP_strong' (λ i, Ps !! i = None ∧ φ i)).
      move=> E. case: (fresh (E ∪ dom Ps))=>
        [i [/not_elem_of_union[? /not_elem_of_dom?] ?]]. by exists i. }
    iDestruct "X" as %(i & -> & Psi & ?).
    iMod (own_update with "aPs") as "[aPs iP]";
      [by eapply (gmap_view_alloc _ i DfracDiscarded (P : leibnizO _))|].
    iModIntro. iExists i. iSplit; [done|]. unfold ownNi.
    iRevert "iP". iIntros "#iP". iFrame "iP". iExists _. iFrame "aPs".
    iApply big_sepM_insert; [done|]. iFrame "W". iLeft. unfold ownD.
    iFrame "DI". by iApply "→P".
  Qed.

  (** Get [ownE] out of the fancy update *)
  Local Lemma fupd_accE {N E} : ↑N ⊆ E →
    ⊢ |={E,E∖↑N}=> ownE (↑N) ∗ (ownE (↑N) ={E∖↑N,E}=∗ True).
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
    move=> ?. rewrite ninv_unseal. iIntros "(%i & %iN & #iP) W".
    iMod fupd_accE as "[N N→]"; [done|].
    rewrite {1 2}(union_difference_L {[i]} (↑N)); [|set_solver].
    rewrite ownE_op; [|set_solver]. iDestruct "N" as "[i N∖i]".
    iDestruct (ownNi_open with "iP i W") as "($ & $ & Di)". iModIntro.
    iIntros "P W". iDestruct (ownNi_close with "iP P Di W") as "[$ i]".
    iApply "N→". iFrame.
  Qed.

  (** Turn [ownNi] to [ninv] *)
  Local Lemma ownNi_ninv {i N P} : i ∈ (↑N:coPset) → ownNi i P -∗ ninv N P.
  Proof. rewrite ninv_unseal. iIntros. iExists _. by iSplit. Qed.

  (** Allocate [ninv] *)
  Lemma ninv_alloc_rec {intp N P} :
    (ninv N P -∗ intp P) =[ninv_wsat intp]=∗ ninv N P.
  Proof.
    iIntros "→P W".
    iMod (ownNi_alloc_rec (.∈ ↑N) with "[→P] W") as (i) "(%iN & W & iP)".
    - move=> ?. apply fresh_inv_name.
    - iIntros (? iN) "iP". iApply "→P". by iApply ownNi_ninv.
    - iModIntro. iFrame "W". by iApply ownNi_ninv.
  Qed.
  Lemma ninv_alloc {intp N P} : intp P =[ninv_wsat intp]=∗ ninv N P.
  Proof. iIntros "P W". iApply (ninv_alloc_rec with "[P] W"). by iIntros. Qed.
End ninv.

(** Allocate [∀ intp, ninv_wsat intp] *)
Lemma ninv_wsat_alloc `{!invGS_gen hlc Σ, !ninvGpreS PROP Σ} :
  ⊢ |==> ∃ _ : ninvGS PROP Σ, ∀ intp, ninv_wsat intp.
Proof.
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅)) as (γ) "a∅";
    [by apply gmap_view_auth_valid|].
  iModIntro. iExists (NinvGS _ _ _ γ). rewrite ninv_wsat_unseal. iIntros (?).
  iExists ∅. rewrite big_opM_empty. iFrame.
Qed.
