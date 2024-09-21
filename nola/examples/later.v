(** * Example of instantiating Nola with [▶ ∙] *)

From nola.iris Require Export inv.
From nola.bi Require Import later.
From nola.heap_lang Require Export notation proofmode.
Import WpwNotation.

Implicit Type (N : namespace) (l : loc).

Section verify.
  Context `{!inv'GS (▶ ∙) Σ, !heapGS_gen hlc Σ}.

  (** Fixed point generator of [ilist] *)
  Definition ilist_gen N Φ (self : loc -d> iProp Σ) : loc -d> iProp Σ :=
    (λ l, inv_tok N (Next (Φ l)) ∗ inv_tok N (Next
      (∃ l', (l +ₗ 1) ↦ #l' ∗ self l')%I))%I.
  (** [ilist_gen] is contractive *)
  Instance ilist_gen_contractive N Φ : Contractive (ilist_gen N Φ).
  Proof. solve_contractive. Qed.

  (** [ilist]: Linked list *)
  Definition ilist N Φ l : iProp Σ := fixpoint (ilist_gen N Φ) l.
  (** Unfold [ilist] *)
  Lemma ilist_unfold {N Φ l} : ilist N Φ l ≡ ilist_gen N Φ (ilist N Φ) l.
  Proof. by rewrite /ilist (fixpoint_unfold (ilist_gen N Φ) l). Qed.
  (** [ilist] is persistent *)
  Instance ilist_persistent N Φ l : Persistent (ilist N Φ l).
  Proof. rewrite ilist_unfold. exact _. Qed.

  (** Access the tail of [ilist] *)
  Definition tail_ilist : val := λ: "l", let: "l'" := !("l" +ₗ #1) in "l'".
  Lemma wp_tail_ilist {N E Φ l} : ↑N ⊆ E →
    {{{ ilist N Φ l }}}[inv_wsat laterl]
      tail_ilist #l @ E
    {{{ l', RET #l'; ilist N Φ l' }}}.
  Proof.
    iIntros (? Ψ) "#l →Ψ". wp_rec. wp_pure. wp_bind (! _)%E.
    rewrite ilist_unfold. iDestruct "l" as "[ihd itl]".
    iMod (inv_tok_acc (FML:=▶ ∙) (sm:=laterl) with "itl") as
      "/=[(%l' & >↦l' & #ltl) cl]"; [done|].
    wp_load. iModIntro. iMod ("cl" with "[↦l']") as "_".
    { iExists _. by iFrame. }
    iModIntro. wp_pures. iApply ("→Ψ" with "ltl").
  Qed.

  (** Iterate over [ilist] *)
  Definition iter_ilist : val := rec: "self" "f" "c" "l" :=
    if: !"c" ≤ #0 then #() else
      "f" "l";; "c" <- !"c" - #1;;
      let: "l'" := tail_ilist "l" in "self" "f" "c" "l'".
  Lemma wp_iter_list {N E Φ c l} {f : val} {n : nat} : ↑N ⊆ E →
    (∀ l0, {{{ inv_tok N (Next (Φ l0)) }}}[inv_wsat laterl] f #l0 @ E
      {{{ RET #(); True }}}) -∗
    {{{ c ↦ #n ∗ ilist N Φ l }}}[inv_wsat laterl]
      iter_ilist f #c #l @ E
    {{{ RET #(); c ↦ #0 }}}.
  Proof.
    iIntros "% #f" (Ψ) "!> [c↦ #l] →Ψ".
    iInduction n as [|m] "IH" forall (l) "l".
    { wp_rec. wp_load. wp_pures. by iApply "→Ψ". }
    wp_rec. wp_load. wp_pures. wp_apply "f".
    { rewrite ilist_unfold. iDestruct "l" as "[$ _]". }
    iIntros "_". wp_load. wp_store. have -> : (S m - 1)%Z = m by lia.
    wp_apply wp_tail_ilist; [done..|]. iIntros (l') "#ltl". wp_pures.
    iApply ("IH" with "c↦ →Ψ ltl").
  Qed.
End verify.
