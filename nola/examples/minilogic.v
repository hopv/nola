(** * Minimal showcase logic *)

From nola.iris Require Export inv.
From nola.heap_lang Require Export notation proofmode.
Import WpwNotation.

Implicit Type (N : namespace) (l : loc).

(** ** Syntax for separation logic propositions *)
Inductive nProp : Type :=
| all {A : Type} (Φ : A → nProp) | ex {A : Type} (Φ : A → nProp)
| and (P Q : nProp) | or (P Q : nProp) | imp (P Q : nProp) | pure (φ : Prop)
| sep (P Q : nProp) | wand (P Q : nProp) | pers (P : nProp)
| bupd (P : nProp) | later (P : nProp) | pointsto (q : frac) (l : loc) (v : val)
| inv (N : namespace) (P : nProp)
| ilist (N : namespace) (Φ : loc → nProp) (l : loc).
#[warning="-redundant-canonical-projection"] Canonical nPropO := leibnizO nProp.

(** ** Target function: Linked list mutation *)
Definition iter : val := rec: "self" "f" "c" "l" :=
  if: !"c" = #0 then #() else
    "f" "l";; "c" <- !"c" - #1;; "self" "f" "c" (!("l" +ₗ #1)).

Section iris.
  Context `{!inv'GS nPropO Σ, !heapGS_gen hlc Σ}.

  (** ** Interpretation of [nProp] *)
  Fixpoint intp (P : nProp) : iProp Σ := match P with
  | all Φ => ∀ x, intp (Φ x) | ex Φ => ∃ x, intp (Φ x)
  | and P Q => intp P ∧ intp Q | or P Q => intp P ∨ intp Q
  | imp P Q => intp P → intp Q | pure φ => ⌜φ⌝
  | sep P Q => intp P ∗ intp Q | wand P Q => intp P -∗ intp Q
  | pers P => □ intp P | bupd P => |==> intp P | later P => ▷ intp P
  | pointsto q l v => l ↦{#q} v
  | inv N P => inv_tok N P
  | ilist N Φ l => inv_tok N (Φ l) ∗ inv_tok N
      (ex (λ l', sep (pointsto 1 (l +ₗ 1) (#l')) (ilist N Φ l')))
  end.

  (** ** Termination of [iter] *)
  Lemma twp_iter {N Φ c l} {f : val} {n : nat} :
    (∀ l0, [[{ inv_tok N (Φ l0) }]][inv_wsat intp] f #l0 @ ↑N
      [[{ RET #(); True }]]) -∗
    [[{ c ↦ #n ∗ intp (ilist N Φ l) }]][inv_wsat intp]
      iter f #c #l @ ↑N
    [[{ RET #(); c ↦ #0 }]].
  Proof.
    iIntros "#Hf" (Ψ) "!> /=[c↦ #[ihd itl]] HΨ".
    iInduction n as [|m] "IH" forall (l) "ihd itl".
    { wp_rec. wp_pures. wp_load. wp_pures. by iApply "HΨ". }
    wp_rec. wp_pures. wp_load. wp_pures. wp_apply "Hf"; [done|]. iIntros "_".
    wp_pures. wp_load. wp_op. have -> : (S m - 1)%Z = m by lia. wp_store.
    wp_op. wp_bind (! _)%E.
    iMod (inv_tok_acc (PROP:=nPropO) (intp:=intp) with "itl") as
      "/=[(%l' & ↦l' & #itlhd & #itltl) cl]"; [done|].
    wp_load. iModIntro. iMod ("cl" with "[↦l']") as "_".
    { iExists _. iFrame "↦l'". by iSplit. }
    iModIntro. by iApply ("IH" with "c↦ HΨ").
  Qed.
End iris.
