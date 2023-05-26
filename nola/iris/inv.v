(** Nola later-free invariant *)

From iris.algebra Require Import gmap_view gset coPset.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export own wsat fancy_updates invariants.

(** Resources *)

Class ninvGpreS (PROP : Type) (Σ : gFunctors) : Set := NinvGpreS {
  ninvGpreS_inv :: inG Σ (gmap_viewR positive (leibnizO PROP));
}.

Class ninvGS (PROP : Type) (Σ : gFunctors) : Set := NinvGS {
  ninv_inG :: ninvGpreS PROP Σ;
  ninv_name : gname;
}.

Definition ninvΣ (PROP : Type) : gFunctors :=
  #[GFunctor (gmap_viewRF positive (leibnizO PROP))].

#[export] Instance subG_ninvΣ {PROP Σ} : subG (ninvΣ PROP) Σ → ninvGpreS PROP Σ.
Proof. solve_inG. Qed.

(** [ownNi], [ninv] Invariant token *)

Section ninv.
  Context `{!invGS Σ, !ninvGS PROP Σ}.

  Definition ownNi (i : positive) (P : PROP) : iProp Σ :=
    own ninv_name (gmap_view_frag i DfracDiscarded (P : leibnizO _)).
  #[export] Typeclasses Opaque ownNi.
  #[export] Instance ownNi_persistent {i P} : Persistent (ownNi i P).
  Proof. rewrite /ownNi. apply _. Qed.

  Definition ninv_def (N : namespace) (P : PROP) : iProp Σ :=
    ∃ i, ⌜i ∈ (↑N:coPset)⌝ ∧ ownNi i P.
  Definition ninv_aux : seal ninv_def. Proof. by eexists. Qed.
  Definition ninv := ninv_aux.(unseal).
  Lemma ninv_unseal : ninv = ninv_def. Proof. exact ninv_aux.(seal_eq). Qed.
End ninv.

(** [ninv_wsat]: Invariant world satisfaction *)

Section ninv_wsat.
  Context `{!invGS_gen hlc Σ, !ninvGS PROP Σ} (intp : PROP → iProp Σ).

  Definition authNi (Ps : gmap positive (leibnizO PROP)) :=
    own ninv_name (gmap_view_auth (DfracOwn 1) Ps).

  Definition ninv_wsat_def : iProp Σ :=
    ∃ Ps, authNi Ps ∗ [∗ map] i ↦ P ∈ Ps, intp P ∗ ownD {[i]} ∨ ownE {[i]}.
  Definition ninv_wsat_aux : seal ninv_wsat_def. Proof. by eexists. Qed.
  Definition ninv_wsat := ninv_wsat_aux.(unseal).
  Lemma ninv_wsat_unseal : ninv_wsat = ninv_wsat_def.
  Proof. exact ninv_wsat_aux.(seal_eq). Qed.

  Lemma authNi_lookup {Ps i P} :
    authNi Ps -∗ ownNi i P -∗ ⌜Ps !! i = Some P⌝.
  Proof.
    iIntros "aPs iP". rewrite /authNi /ownNi. iCombine "aPs iP" as "eq".
    rewrite own_valid gmap_view_both_validI bi.and_elim_r.
    iDestruct "eq" as %eq. by apply leibniz_equiv in eq.
  Qed.

  (** Open and close by [ownNi] *)
  Lemma ownNi_open {i P} :
    ninv_wsat -∗ ownNi i P -∗ ownE {[i]} -∗ ninv_wsat ∗ intp P ∗ ownD {[i]}.
  Proof.
    rewrite ninv_wsat_unseal. iIntros "(%Ps & aPs & W) iP Ei".
    iDestruct (authNi_lookup with "aPs iP") as %eqP.
    iDestruct (big_sepM_delete with "W") as "[[[$$]|Ei'] W]";
      [done| |iDestruct (ownE_singleton_twice with "[$]") as "[]"].
    iExists _. iFrame "aPs". iApply big_sepM_delete; [done|]. iFrame.
  Qed.
  Lemma ownNi_close {i P} :
    ninv_wsat -∗ ownNi i P -∗ intp P -∗ ownD {[i]} -∗ ninv_wsat ∗ ownE {[i]}.
  Proof.
    rewrite ninv_wsat_unseal. iIntros "(%Ps & aPs & W) iP P Di".
    iDestruct (authNi_lookup with "aPs iP") as %eqP.
    iDestruct (big_sepM_delete with "W") as "[[[_ Di']|$] W]";
      [done|iDestruct (ownD_singleton_twice with "[$]") as %[]|].
    iExists _. iFrame "aPs". iApply big_sepM_delete; [done|]. iFrame "W".
    iLeft. iFrame.
  Qed.

  (** Create [ownNi] *)
  Lemma ownNi_alloc_rec φ P :
    (∀ E : gset positive, ∃ i, i ∉ E ∧ φ i) →
    ninv_wsat -∗ (∀ i, ⌜φ i⌝ → ownNi i P -∗ intp P) ==∗
      ∃ i, ⌜φ i⌝ ∗ ninv_wsat ∗ ownNi i P.
  Proof.
    rewrite ninv_wsat_unseal. iIntros (fresh) "(%Ps & aPs & W) toP".
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
    iFrame "DI". by iApply "toP".
  Qed.

  (** Get [ownE] out of the fancy update *)
  Lemma fupd_accE {N E} : ↑N ⊆ E →
    ⊢ |={E,E∖↑N}=> ownE (↑N) ∗ (ownE (↑N) ={E∖↑N,E}=∗ True).
  Proof.
    rewrite fancy_updates.uPred_fupd_unseal /fancy_updates.uPred_fupd_def.
    move=> ?. iIntros "[$ E]". do 2 iModIntro.
    rewrite {1 4}(union_difference_L (↑ N) E); [|done].
    rewrite ownE_op; [|set_solver]. iDestruct "E" as "[$$]". by iIntros "$$".
  Qed.

  (** Access [ninv] *)
  Lemma ninv_acc {N E P} :
    ↑N ⊆ E → ninv_wsat -∗ ninv N P ={E,E∖↑N}=∗
      ninv_wsat ∗ intp P ∗ (ninv_wsat -∗ intp P ={E∖↑N,E}=∗ ninv_wsat).
  Proof.
    move=> ?. rewrite ninv_unseal. iIntros "W (%i & %iN & #iP)".
    iMod fupd_accE as "[N Nto]"; [done|].
    rewrite {1 2}(union_difference_L {[i]} (↑N)); [|set_solver].
    rewrite ownE_op; [|set_solver]. iDestruct "N" as "[i N∖i]".
    iDestruct (ownNi_open with "W iP i") as "($ & $ & Di)". iModIntro.
    iIntros "W P". iDestruct (ownNi_close with "W iP P Di") as "[$ i]".
    iApply "Nto". iFrame.
  Qed.

  (** Create [ninv] *)
  Lemma ninv_alloc_rec {N P} :
    ninv_wsat -∗ (ninv N P -∗ intp P) ==∗ ninv_wsat ∗ ninv N P.
  Proof.
    iIntros "W toP". rewrite ninv_unseal.
    iMod (ownNi_alloc_rec (.∈ ↑N) with "W [toP]") as (i) "(%iN & W & iP)".
    - move=> ?. apply fresh_inv_name.
    - iIntros (? iN) "iP". iApply "toP". iExists _. by iFrame.
    - iModIntro. iFrame "W". iExists _. by iFrame.
  Qed.
  Lemma ninv_alloc {N P} : ninv_wsat -∗ intp P ==∗ ninv_wsat ∗ ninv N P.
  Proof. iIntros "W P". iApply (ninv_alloc_rec with "W"). by iIntros. Qed.
End ninv_wsat.
