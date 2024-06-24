(** * Minimal showcase logic *)

From nola.iris Require Export inv.
From nola.heap_lang Require Export notation proofmode.
Import WpwNotation.

Implicit Type (N : namespace) (l : loc).

(** ** Separation logic formulas *)
Inductive fml : Type :=
| all {A : Type} (Φ : A → fml) | ex {A : Type} (Φ : A → fml)
| and (P Q : fml) | or (P Q : fml) | imp (P Q : fml) | pure (φ : Prop)
| sep (P Q : fml) | wand (P Q : fml) | pers (P : fml)
| bupd (P : fml) | later (P : fml) | pointsto (q : frac) (l : loc) (v : val)
| inv (N : namespace) (P : fml)
| ilist (N : namespace) (Φ : loc → fml) (l : loc).
#[warning="-redundant-canonical-projection"] Canonical fmlO := leibnizO fml.

(** ** Linked list mutation *)

(** Target function *)
Definition iter_ilist : val := rec: "self" "f" "c" "l" :=
  if: !"c" = #0 then #() else
    "f" "l";; "c" <- !"c" - #1;; "self" "f" "c" (!("l" +ₗ #1)).

Section verify.
  Context `{!inv'GS fmlO Σ, !heapGS_gen hlc Σ}.

  (** Semantics of [fml] *)
  Fixpoint sem (P : fml) : iProp Σ := match P with
  | all Φ => ∀ x, sem (Φ x) | ex Φ => ∃ x, sem (Φ x)
  | and P Q => sem P ∧ sem Q | or P Q => sem P ∨ sem Q
  | imp P Q => sem P → sem Q | pure φ => ⌜φ⌝
  | sep P Q => sem P ∗ sem Q | wand P Q => sem P -∗ sem Q
  | pers P => □ sem P | bupd P => |==> sem P | later P => ▷ sem P
  | pointsto q l v => l ↦{#q} v
  | inv N P => inv_tok N P
  | ilist N Φ l => inv_tok N (Φ l) ∗ inv_tok N
      (ex (λ l', sep (pointsto 1 (l +ₗ 1) (#l')) (ilist N Φ l')))
  end.

  (** Termination of [iter] *)
  Lemma twp_iter_list {N Φ c l} {f : val} {n : nat} :
    (∀ l0, [[{ inv_tok N (Φ l0) }]][inv_wsat sem] f #l0 @ ↑N
      [[{ RET #(); True }]]) -∗
    [[{ c ↦ #n ∗ sem (ilist N Φ l) }]][inv_wsat sem]
      iter_ilist f #c #l @ ↑N
    [[{ RET #(); c ↦ #0 }]].
  Proof.
    iIntros "#f" (Ψ) "!> /=[c↦ #[ihd itl]] →Ψ".
    iInduction n as [|m] "IH" forall (l) "ihd itl".
    { wp_rec. wp_load. wp_pures. by iApply "→Ψ". }
    wp_rec. wp_load. wp_pures. wp_apply "f"; [done|]. iIntros "_".
    wp_load. wp_store. wp_op. wp_bind (! _)%E. have -> : (S m - 1)%Z = m by lia.
    iMod (inv_tok_acc (FML:=fmlO) (sm:=sem) with "itl") as
      "/=[(%l' & ↦l' & #itlhd & #itltl) cl]"; [done|].
    wp_load. iModIntro. iMod ("cl" with "[↦l']") as "_".
    { iExists _. iFrame "↦l'". by iSplit. }
    iModIntro. by iApply ("IH" with "c↦ →Ψ").
  Qed.
End verify.
