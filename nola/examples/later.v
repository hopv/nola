(** * Example of instantiating Nola with [▶ ∙] *)

From nola.heap_lang Require Import notation proofmode.
From nola.bi Require Import ofe.
From nola.iris Require Import inv.
Import WpwNotation.

(** ** Target function: Linked list mutation *)
Definition iter : val := rec: "self" "f" "c" "l" :=
  if: !"c" = #0 then #() else
    "f" "l";; "c" <- !"c" - #1;; "self" "f" "c" (!("l" +ₗ #1)).

Section iris.
  Context `{!inv'GS (▶ ∙) Σ, !heapGS_gen hlc Σ}.
  Implicit Type (N : namespace) (Φ : loc → iProp Σ) (l : loc).

  (** Fixed point generator of [ilist] *)
  Definition ilist_gen N Φ (self : loc -d> iProp Σ) : loc -d> iProp Σ :=
    (λ l, inv_tok N (Next (Φ l)) ∗ inv_tok N (Next
      (∃ l', (l +ₗ 1) ↦ #l' ∗ self l')%I))%I.

  (** [ilist_gen] is contractive *)
  Instance ilist_gen_contractive N Φ : Contractive (ilist_gen N Φ).
  Proof. solve_contractive. Qed.

  (** Fixed point of [ilist_gen] *)
  Definition ilist N Φ l : iProp Σ := fixpoint (ilist_gen N Φ) l.

  (** Unfold [ilist] *)
  Lemma ilist_unfold {N Φ l} : ilist N Φ l ≡ ilist_gen N Φ (ilist N Φ) l.
  Proof. by rewrite /ilist (fixpoint_unfold (ilist_gen N Φ) l). Qed.

  (** [ilist] is persistent *)
  Instance ilist_persistent N Φ l : Persistent (ilist N Φ l).
  Proof. rewrite ilist_unfold. exact _. Qed.

  (** ** Safety of [iter] *)
  Lemma wp_iter {N Φ c l} {f : val} {n : nat} :
    (∀ l0 : loc,
      {{{ inv_tok N (Next (Φ l0)) }}}[inv_wsat laterl]
        f #l0 @ ↑N
      {{{ RET #(); True }}}) -∗
    {{{ c ↦ #n ∗ ilist N Φ l }}}[inv_wsat laterl]
      iter f #c #l @ ↑N
    {{{ RET #(); c ↦ #0 }}}.
  Proof.
    iIntros "#Hf" (Ψ). iIntros "!> [c↦ #l] HΨ".
    iInduction n as [|m] "IH" forall (l) "l".
    { wp_rec. wp_pures. wp_load. wp_pures. by iApply "HΨ". }
    rewrite ilist_unfold. iDestruct "l" as "[ihd itl]".
    wp_rec. wp_pures. wp_load. wp_pures.
    wp_apply "Hf"; [done|]. iIntros "_". wp_pures.
    wp_load. wp_op. have -> : (S m - 1)%Z = m by lia. wp_store.
    wp_op. wp_bind (! _)%E.
    iMod (inv_tok_acc (PROP:=▶ ∙) (intp:=laterl) with "itl") as
      "/=[(%l' & ↦l' & #l') cl]"; [done|].
    wp_load. iModIntro. iMod ("cl" with "[↦l']") as "_".
    { iNext. iExists _. by iFrame "↦l'". } iModIntro.
    by iApply ("IH" with "c↦ HΨ").
  Qed.
End iris.
