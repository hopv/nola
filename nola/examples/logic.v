(** * Showcase logic *)

From nola.iris Require Export ciprop inv_deriv.
From nola.bi Require Import util.
From nola.heap_lang Require Export notation proofmode lib.mutex.
Import WpwNotation iPropAppNotation PintpNotation IntpNotation.

Implicit Type (N : namespace) (l : loc).

(** ** Preliminaries *)

(** [sel]: Selector *)
Variant sel :=
| (** Invariant *) cips_inv (N : namespace)
| (** Mutex *) cips_mutex (l : loc).
(** [idom]: Domain for inductive parts *)
Definition idom (_ : sel) : Type := Empty_set.
(** [cdom]: Domain for coinductive parts *)
Definition cdom (s : sel) : Type := match s with
  | cips_inv _ => unit
  | cips_mutex _ => unit
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
  Definition cip_mutex l (Px : ciProp Σ) : ciProp Σ :=
    cip_custom (cips_mutex l) nullary (unary Px) ().

  #[export] Instance cip_inv_ne {N} : NonExpansive (cip_inv N).
  Proof. move=> ????. apply cip_custom_ne; solve_proper. Qed.
End ciProp.

From iris.algebra Require Import ofe.
(** ** [judg]: Judgment *)
Definition judg Σ : ofe :=
  (leibnizO namespace * ciProp Σ + ciProp Σ * ciProp Σ)%type.
Definition inv_jacsr {Σ} N Px : judg Σ := inl (N, Px).
Definition mutex_jiff {Σ} Px Qx : judg Σ := inr (Px, Qx).
#[export] Instance inv_jacsr_ne {Σ N} : NonExpansive (@inv_jacsr Σ N).
Proof. move=> ????. exact: inl_ne. Qed.
#[export] Instance mutex_jiff_ne {Σ} : NonExpansive2 (@mutex_jiff Σ).
Proof. move=> ???????. exact: inr_ne. Qed.

#[export] Instance judg_inv_pre_deriv {Σ} :
  InvPreDeriv (ciProp Σ) (judg Σ) := INV_PRE_DERIV inv_jacsr.
#[export] Instance judg_mutex_pre_deriv {Σ} :
  MutexPreDeriv (ciProp Σ) (judg Σ) := MUTEX_PRE_DERIV mutex_jiff.

Section intp.
  Context `{!inv'GS ciPropOF Σ, !mutexGS ciPropOF Σ}.
  Implicit Type δ : judg Σ → iProp Σ.

  (** ** [bintp]: Base interpretation *)
  Definition bintp δ s :
    (idom s -d> iProp Σ) → (cdom s -d> ciProp Σ) → dataOF s $oi Σ → iProp Σ :=
    match s with
    | cips_inv N => λ _ Pxs _, inv' δ N (Pxs ())
    | cips_mutex l => λ _ Pxs _, mutex δ l (Pxs ())
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

  Context `{!heapGS_gen hlc Σ}.

  (** ** [judg_intp]: Judgment interpretation *)
  Definition judg_intp δ (J : judg Σ) := match J with
    | inl (N, Px) => inv_acsr ⟦⟧(δ) N ⟦ Px ⟧(δ)
    | inr (Px, Qx) =>
        (⟦ Px ⟧(δ) ={⊤}=∗ ⟦ Qx ⟧(δ)) ∧ (⟦ Qx ⟧(δ) ={⊤}=∗ ⟦ Px ⟧(δ))
    end%I.
  Local Instance judg_intp_ne `{!NonExpansive δ} : NonExpansive (judg_intp δ).
  Proof.
    move=> ???[[??][??][/=/leibniz_equiv_iff-> ?]|[??][??][/=??]]; solve_proper.
  Qed.
  #[export] Instance judg_dintp : Dintp (judg Σ) (judg Σ) (iProp Σ) :=
    DINTP judg_intp.
  Canonical judgJ : judgi (iProp Σ) := Judgi (judg Σ).

  #[export] Instance judg_inv_deriv : InvDeriv ciPropOF Σ judgJ.
  Proof. done. Qed.
  #[export] Instance judg_mutex_deriv : MutexDeriv ciPropOF Σ judgJ.
  Proof. done. Qed.
End intp.

(** ** Target function: Linked list mutation *)
Definition iter_ilist : val := rec: "self" "f" "c" "l" :=
  if: !"c" = #0 then #() else
    "f" "l";; "c" <- !"c" - #1;; "self" "f" "c" (!("l" +ₗ #1)).

Section verify.
  Context `{!inv'GS ciPropOF Σ, !mutexGS ciPropOF Σ, !heapGS_gen hlc Σ}.
  Implicit Type Φx Ψx : loc → ciProp Σ.

  (** ** [ilist]: Syntactic proposition for a list *)
  Definition ilist_gen N Φx Ilist' l : ciProp Σ :=
    cip_inv N (Φx l) ∗ cip_inv N (Ilist' N Φx l).
  Definition ilist'_gen N Φx Ilist' l : ciProp Σ :=
    ∃ l', ▷ (l +ₗ 1) ↦ #l' ∗ ilist_gen N Φx Ilist' l'.
  CoFixpoint ilist' N Φx : loc → ciProp Σ := ilist'_gen N Φx ilist'.
  Definition ilist N Φx : loc → ciProp Σ := ilist_gen N Φx ilist'.

  (** ** Convert the predicate of [ilist] using [mod_acsr] *)
  Local Lemma inv'_acsr_iff `{!Deriv ih δ} {N Φx Ψx l} :
    □ (∀ δ' l', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ →
      mod_acsr (fupd ∅ ∅) ⟦ Φx l' ⟧(δ') ⟦ Ψx l' ⟧(δ') ∧
      mod_acsr (fupd ∅ ∅) ⟦ Ψx l' ⟧(δ') ⟦ Φx l' ⟧(δ')) ⊢
      inv' δ N (Φx l) ∗-∗ inv' δ N (Ψx l).
  Proof.
    iIntros "#big". iSplit; iApply inv'_acsr; iIntros "!>" (????);
      [iApply bi.and_elim_l|iApply bi.and_elim_r]; by iApply "big".
  Qed.
  Local Lemma inv'_ilist'_iff `{!Deriv ih δ} {N Φx Ψx l} :
    □ (∀ δ' l', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ →
      inv' δ' N (Φx l') ∗-∗ inv' δ' N (Ψx l')) -∗
      inv' δ N (ilist' N Φx l) ∗-∗ inv' δ N (ilist' N Ψx l).
  Proof.
    move: l. apply Deriv_ind=> δ' ??. iIntros "#eqv".
    iSplit; iApply inv'_acsr; iIntros "!>" (??[IH ?]?);
      rewrite -(wand_iff_mod_acsr (M:=fupd _ _)) !/⟦ ilist' _ _ _ ⟧(_);
      (iModIntro; iSplit; iIntros "/=[%[$[ihd ?]]]"; (iSplit; [|by iApply IH]));
      iApply ("eqv" with "[%] [//] ihd"); by apply Deriv_mono=> ?[??].
  Qed.
  Lemma ilist_acsr `{!Deriv ih δ} {N Φx Ψx l} :
    □ (∀ δ' l', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ →
      mod_acsr (fupd ∅ ∅) ⟦ Φx l' ⟧(δ') ⟦ Ψx l' ⟧(δ') ∧
      mod_acsr (fupd ∅ ∅) ⟦ Ψx l' ⟧(δ') ⟦ Φx l' ⟧(δ')) -∗
      ⟦ ilist N Φx l ⟧(δ) ∗-∗ ⟦ ilist N Ψx l ⟧(δ).
  Proof.
    iIntros "#eqv". rewrite /⟦ ⟧(δ) /=.
    iSplit; (iIntros "[ihd itl]"; iSplitL "ihd";
      [by iApply (inv'_acsr_iff (Φx:=Φx))|]);
      iApply (inv'_ilist'_iff with "[] itl"); iIntros "!>" (????);
      [iApply bi.wand_iff_sym|]; by iApply inv'_acsr_iff.
  Qed.

  (** ** Termination of [iter] *)
  Lemma twp_iter_list {N Φx c l} {f : val} {n : nat} :
    (∀ l0, [[{ invd N (Φx l0) }]][inv_wsatid] f #l0 @ ↑N
      [[{ RET #(); True }]]) -∗
    [[{ c ↦ #n ∗ ⟦ ilist N Φx l ⟧ }]][inv_wsatid]
      iter_ilist f #c #l @ ↑N
    [[{ RET #(); c ↦ #0 }]].
  Proof.
    unfold intp. iIntros "#f" (Ψ) "!> /=[c↦ #[ihd itl]] →Ψ".
    iInduction n as [|m] "IH" forall (l) "ihd itl".
    { wp_rec. wp_pures. wp_load. wp_pures. by iApply "→Ψ". }
    wp_rec. wp_pures. wp_load. wp_pures. wp_apply "f"; [done|]. iIntros "_".
    wp_pures. wp_load. wp_op. have -> : (S m - 1)%Z = m by lia. wp_store.
    wp_op. wp_bind (! _)%E.
    iMod (invd_acc with "itl") as "/=[(%l' & >↦l' & #itlhd & #itltl) cl]/=";
      [done|].
    wp_load. iModIntro. iMod ("cl" with "[↦l']") as "_".
    { iExists _. iFrame "↦l'". by iSplit. }
    iModIntro. by iApply ("IH" with "c↦ →Ψ").
  Qed.
End verify.
