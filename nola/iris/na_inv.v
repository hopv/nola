(** * For non-atomic invariants *)

From nola Require Export iris.inv.
From iris.base_logic Require Export lib.na_invariants.
From iris.algebra Require Import gset coPset.
From iris.proofmode Require Import proofmode.

Section na_ninv.
  Context `{!invGS_gen hlc Σ, !na_invG Σ}.
  Local Existing Instance na_inv_inG.

  (** Access lock of an non-atomic invariant *)
  Definition na_lock (p : na_inv_pool_name) (i : positive) : iProp Σ :=
    own p (ε, GSet {[i]}).

  (** What to be put in an non-atomic invariant *)
  Definition na_body
    (p : na_inv_pool_name) (i : positive) (P : iProp Σ) : iProp Σ :=
    P ∗ na_lock p i ∨ na_own p {[i]}.
  #[export] Instance na_body_ne {p i} : NonExpansive (na_body p i).
  Proof. solve_proper. Qed.

  (** Allocate [na_lock] *)
  Lemma na_lock_alloc {p N} :
    ⊢ |==> ∃ i, ⌜i ∈ (↑N:coPset)⌝ ∧ na_lock p i.
  Proof.
    iMod (own_unit (prodUR coPset_disjUR (gset_disjUR positive)) p) as "ε".
    iMod (own_updateP with "ε") as ([m1 m2]) "[%cond lock]".
    { apply prod_updateP'.
      - apply cmra_updateP_id, (reflexivity (R:=eq)).
      - apply (gset_disj_alloc_empty_updateP_strong' (.∈ (↑N:coPset)))=> ?.
        apply fresh_inv_name. }
    move: cond=>/=[<-[i[->?]]]. iModIntro. iExists i. by iSplit.
  Qed.

  (** Access [P] from [na_body] *)
  Lemma na_body_acc {p i N E P} :
    i ∈ (↑N:coPset) → ↑N ⊆ E →
    na_body p i P -∗ na_own p E -∗ P ∗ na_own p (E∖↑N) ∗
      (P -∗ na_own p (E∖↑N) -∗ na_body p i P ∗ na_own p E).
  Proof.
    iIntros (??) "[[$ lock]|i] E"; last first.
    { iDestruct (na_own_disjoint with "i E") as %?. set_solver. }
    rewrite [E as X in na_own p X](union_difference_L (↑N) E); [|done].
    rewrite [X in (X ∪ _)](union_difference_L {[i]} (↑N)) ?na_own_union;
      [|set_solver..].
    iDestruct "E" as "[[i $] $]". iIntros "P $". iSplitR "i"; [|done].
    iLeft. iFrame.
  Qed.
End na_ninv.
