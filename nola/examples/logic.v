(** * Showcase logic *)

From nola.iris Require Export ciprop inv_deriv.
From nola.heap_lang Require Export notation proofmode.
Import WpwNotation iPropAppNotation PintpNotation IntpNotation.

Implicit Type (N : namespace) (l : loc).

(** ** Preliminaries *)

(** [sel]: Selector *)
Variant sel :=
| (** Invariant *) cips_inv (N : namespace).
(** [idom]: Domain for inductive parts *)
Definition idom (_ : sel) : Type := Empty_set.
(** [cdom]: Domain for coinductive parts *)
Definition cdom (s : sel) : Type := match s with
  | cips_inv _ => unit
  end.
(** [dataOF]: Data [oFunctor] *)
Definition dataOF (_ : sel) : oFunctor := unitO.
(** [dataOF] is contractive *)
Fact dataOF_contractive {s} : oFunctorContractive (dataOF s).
Proof. exact _. Qed.

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

  #[export] Instance cip_inv_ne {N} : NonExpansive (cip_inv N).
  Proof. move=> ????. apply cip_custom_ne; solve_proper. Qed.
End ciProp.

(** ** [judg]: Judgment *)
Definition judg Σ : ofe := prodO (leibnizO namespace) (ciProp Σ).
Definition inv_jacsr {Σ} N Px : judg Σ := (N, Px).
#[export] Instance inv_jacsr_ne {Σ N} : NonExpansive (@inv_jacsr Σ N).
Proof. done. Qed.

#[export] Instance judg_inv_pre_deriv {Σ} :
  InvPreDeriv (ciProp Σ) (judg Σ) := INV_PRE_DERIV inv_jacsr.

Section iris.
  Context `{!inv'GS ciPropOF Σ}.
  Implicit Type δ : judg Σ → iProp Σ.

  (** ** [bintp]: Base interpretation *)
  Definition bintp δ s :
    (idom s -d> iProp Σ) → (cdom s -d> ciProp Σ) → dataOF s $oi Σ → iProp Σ :=
    match s with
    | cips_inv N => λ _ Pxs _, inv' δ N (Pxs ())
    end.

  (** [bintp] is non-expansive *)
  #[export] Instance bintp_ne `{!NonExpansive δ} {s} :
    NonExpansive3 (bintp δ s).
  Proof. case s; solve_proper. Qed.

  (** ** Parameterized interpretation of [ciProp] *)
  #[export] Instance ciProp_dintp : Dintp (judg Σ) (ciProp Σ) (iProp Σ) :=
    DINTP (λ δ, cip_intp (bintp δ)).

  (** [ciProp_intp] is non-expansive *)
  Fact ciProp_intp_ne `{!NonExpansive δ} : NonExpansive ⟦⟧(δ)@{ciProp Σ}.
  Proof. exact _. Qed.

  Context `{!invGS_gen hlc Σ}.

  (** ** [judg_intp]: Judgment interpretation *)
  Definition judg_intp δ (J : judg Σ) := match J with
    | (N, Px) => inv_acsr ⟦⟧(δ) N ⟦ Px ⟧(δ)
    end.
  Local Instance judg_intp_ne `{!NonExpansive δ} : NonExpansive (judg_intp δ).
  Proof. move=> ?[??][??][/=??]. solve_proper. Qed.
  #[export] Instance judg_dintp : Dintp (judg Σ) (judg Σ) (iProp Σ) :=
    DINTP judg_intp.
  Canonical judgJ : judgi (iProp Σ) := Judgi (judg Σ).

  #[export] Instance judg_inv_deriv : InvDeriv ciPropOF Σ judgJ.
  Proof. done. Qed.
End iris.

(** ** Target function: Linked list mutation *)
Definition iter : val := rec: "self" "f" "c" "l" :=
  if: !"c" = #0 then #() else
    "f" "l";; "c" <- !"c" - #1;; "self" "f" "c" (!("l" +ₗ #1)).

Section iris.
  Context `{!inv'GS ciPropOF Σ, !heapGS_gen hlc Σ}.
  Implicit Type Φx : loc → ciProp Σ.

  (** ** [ilist]: Syntactic proposition for a list *)
  Definition ilist_gen N Φx Ilist' l : ciProp Σ :=
    cip_inv N (Φx l) ∗ cip_inv N (Ilist' N Φx l).
  Definition ilist'_gen N Φx Ilist' l : ciProp Σ :=
    ∃ l', ▷ (l +ₗ 1) ↦ #l' ∗ ilist_gen N Φx Ilist' l'.
  CoFixpoint ilist' N Φx : loc → ciProp Σ := ilist'_gen N Φx ilist'.
  Definition ilist N Φx : loc → ciProp Σ := ilist_gen N Φx ilist'.

  (** ** Termination of [iter] *)
  Lemma twp_iter {N Φx c l} {f : val} {n : nat} :
    (∀ l0, [[{ inv' der N (Φx l0) }]][inv_wsatid] f #l0 @ ↑N
      [[{ RET #(); True }]]) -∗
    [[{ c ↦ #n ∗ ⟦ ilist N Φx l ⟧ }]][inv_wsatid]
      iter f #c #l @ ↑N
    [[{ RET #(); c ↦ #0 }]].
  Proof.
    unfold intp. iIntros "#Hf" (Ψ) "!> /=[c↦ #[ihd itl]] HΨ".
    iInduction n as [|m] "IH" forall (l) "ihd itl".
    { wp_rec. wp_pures. wp_load. wp_pures. by iApply "HΨ". }
    wp_rec. wp_pures. wp_load. wp_pures. wp_apply "Hf"; [done|]. iIntros "_".
    wp_pures. wp_load. wp_op. have -> : (S m - 1)%Z = m by lia. wp_store.
    wp_op. wp_bind (! _)%E.
    iMod (inv'_acc with "itl") as "/=[(%l' & >↦l' & #itlhd & #itltl) cl]/=";
      [done|].
    wp_load. iModIntro. iMod ("cl" with "[↦l']") as "_".
    { iExists _. iFrame "↦l'". by iSplit. }
    iModIntro. by iApply ("IH" with "c↦ HΨ").
  Qed.
End iris.
