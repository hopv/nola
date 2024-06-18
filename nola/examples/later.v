(** * Example of instantiating Nola with [▶ ∙] *)

From nola.iris Require Export inv.
From nola.bi Require Import ofe.
From nola.heap_lang Require Export notation proofmode.
Import WpwNotation.

Implicit Type (N : namespace) (l : loc).

(** ** Linked list mutation *)

(** Target function *)
Definition iter_ilist : val := rec: "self" "f" "c" "l" :=
  if: !"c" = #0 then #() else
    "f" "l";; "c" <- !"c" - #1;; "self" "f" "c" (!("l" +ₗ #1)).

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

  (** Safety of [iter] *)
  Lemma wp_iter_list {N Φ c l} {f : val} {n : nat} :
    (∀ l0, {{{ inv_tok N (Next (Φ l0)) }}}[inv_wsat laterl] f #l0 @ ↑N
      {{{ RET #(); True }}}) -∗
    {{{ c ↦ #n ∗ ilist N Φ l }}}[inv_wsat laterl]
      iter_ilist f #c #l @ ↑N
    {{{ RET #(); c ↦ #0 }}}.
  Proof.
    iIntros "#f" (Ψ) "!> [c↦ #l] →Ψ". iInduction n as [|m] "IH" forall (l) "l".
    { wp_rec. wp_load. wp_pures. by iApply "→Ψ". }
    rewrite ilist_unfold. iDestruct "l" as "[ihd itl]". wp_rec. wp_load.
    wp_pures. wp_apply "f"; [done|]. iIntros "_". wp_load. wp_store. wp_op.
    wp_bind (! _)%E. have -> : (S m - 1)%Z = m by lia.
    iMod (inv_tok_acc (FML:=▶ ∙) (ip:=laterl) with "itl") as
      "/=[(%l' & ↦l' & #l') cl]"; [done|].
    wp_load. iModIntro. iMod ("cl" with "[↦l']") as "_".
    { iNext. iExists _. by iFrame "↦l'". }
    iModIntro. by iApply ("IH" with "c↦ →Ψ").
  Qed.
End verify.
