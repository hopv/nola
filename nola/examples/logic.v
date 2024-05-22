(** * Showcase logic *)

From nola.iris Require Import ciprop inv.
From nola.heap_lang Require Import notation proofmode.
Import WpwNotation iPropAppNotation.

Implicit Type (N : namespace) (l : loc).

(** ** [sel]: Selector *)
Variant sel :=
| (** Invariant *) cips_inv (N : namespace).

(** ** [idom]: Domain for inductive parts *)
Definition idom (_ : sel) : Type := Empty_set.

(** ** [cdom]: Domain for coinductive parts *)
Definition cdom (s : sel) : Type := match s with
  | cips_inv _ => unit
  end.

(** ** [dataOF]: Data [oFunctor] *)
Definition dataOF (s : sel) : oFunctor := match s with
  | cips_inv _ => unitO
  end.

(** [dataOF] is contractive *)
#[export] Instance dataOF_contractive {s} : oFunctorContractive (dataOF s).
Proof. by case s. Qed.

(** ** [ciProp]: Proposition *)
Notation ciProp Σ := (ciProp idom cdom dataOF Σ).
Notation ciPropOF := (ciPropOF idom cdom dataOF).

(** [ciPropOF] is contractive *)
Fact ciPropOF_contractive : oFunctorContractive ciPropOF.
Proof. exact _. Qed.

(** ** Construct [ciProp] *)
Section ciProp.
  Context {Σ : gFunctors}.
  Definition cip_inv N (Px : ciProp Σ) : ciProp Σ :=
    cip_custom (cips_inv N) nullary (unary Px) ().
End ciProp.

Section iris.
  Context `{!inv'GS ciPropOF Σ}.

  (** ** [bintp]: Base interpretation *)
  Definition bintp s : (idom s -d> iProp Σ) → (cdom s -d> ciProp Σ) →
    dataOF s $oi Σ → iProp Σ :=
    match s with
    | cips_inv N => λ _ Pxs _, inv_tok N (Pxs ())
    end.

  (** [bintp] is non-expansive *)
  #[export] Instance bintp_ne {s} : NonExpansive3 (bintp s).
  Proof. case s=>/= ??????? eqv ???. f_equiv. apply eqv. Qed.

  (** ** [intp]: Interpretation of [ciProp] *)
  Definition intp : ciProp Σ → iProp Σ := cip_intp bintp.

  (** [intp] is non-expansive *)
  Fact intp_ne : NonExpansive intp.
  Proof. exact _. Qed.
End iris.

(** ** Target function: Linked list mutation *)
Definition iter : val := rec: "self" "f" "c" "l" :=
  if: !"c" = #0 then #() else
    "f" "l";; "c" <- !"c" - #1;; "self" "f" "c" (!("l" +ₗ #1)).

Section iris.
  Context `{!inv'GS ciPropOF Σ, !heapGS_gen hlc Σ}.

  Section ilist.
    Context N (Φ : loc → ciProp Σ).

    (** [ilist]: Syntactic proposition for a list *)
    Definition ilist_gen Ilist' l : ciProp Σ :=
      cip_inv N (Φ l) ∗ cip_inv N (Ilist' l).
    Definition ilist'_gen Ilist' l : ciProp Σ :=
      ∃ l', ▷ (l +ₗ 1) ↦ #l' ∗ ilist_gen Ilist' l'.
    CoFixpoint ilist' : loc → ciProp Σ := ilist'_gen ilist'.
    Definition ilist : loc → ciProp Σ := ilist_gen ilist'.
  End ilist.

  (** ** Termination of [iter] *)
  Lemma twp_iter {N Φ c l} {f : val} {n : nat} :
    (∀ l0 : loc,
      [[{ inv_tok N (Φ l0) }]][inv_wsat intp]
        f #l0 @ ↑N
      [[{ RET #(); True }]]) -∗
    [[{ c ↦ #n ∗ intp (ilist N Φ l) }]][inv_wsat intp]
      iter f #c #l @ ↑N
    [[{ RET #(); c ↦ #0 }]].
  Proof.
    iIntros "#Hf". iIntros (Ψ) "!> [c↦ #[ihd itl]]/= HΨ".
    iInduction n as [|m] "IH" forall (l) "ihd itl".
    { wp_rec. wp_pures. wp_load. wp_pures. by iApply "HΨ". }
    wp_rec. wp_pures. wp_load. wp_pures. wp_apply "Hf"; [done|]. iIntros "_".
    wp_pures. wp_load. wp_op. have -> : (S m - 1)%Z = m by lia. wp_store.
    wp_op. wp_bind (! _)%E.
    iMod (inv_tok_acc (PROP:=ciPropOF) (intp:=intp) with "itl") as
      "/=[(%l' & >↦l' & #itlhd & #itltl) cl]/="; [done|].
    wp_load. iModIntro. iMod ("cl" with "[↦l']") as "_".
    { iExists _. iFrame "↦l'". by iSplit. }
    iModIntro. by iApply ("IH" with "c↦ HΨ").
  Qed.
End iris.
