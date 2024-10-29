(** * Invariant machinery relaxed with derivability *)

From nola.util Require Import tagged.
From nola.bi Require Export deriv.
From nola.bi Require Import wpw.
From nola.iris Require Export inv.
From iris.proofmode Require Import proofmode.
Import FunNPNotation iPropAppNotation ModwNotation WpwNotation DsemNotation.

Implicit Type (Σ : gFunctors) (N : namespace) (FM : ofe).

(** ** [inv_judgty]: Judgment type for [inv] *)
Variant inv_judg_id FM := .
Definition inv_judgty (FM : ofe) : ofe :=
  (** Accessor judgment *) tagged (inv_judg_id FM) (leibnizO namespace * FM).

(** ** [InvJudg]: Judgment structure for [inv] *)
Notation InvJudg FM JUDG := (Ejudg (inv_judgty FM) JUDG).

Section inv_deriv.
  Context `{inv_judg : !InvJudg FM JUDG} {Σ}.
  Implicit Type (δ : JUDG -n> iProp Σ) (Px : FM).

  (** Accessor judgment *)
  Local Definition inv_jacsr N Px : JUDG := inv_judg (Tagged (N, Px)).
  Local Instance inv_jacsr_ne {N} : NonExpansive (inv_jacsr N).
  Proof. unfold inv_jacsr=> ????. f_equiv. by split. Qed.

  (** [inv']: Relaxed invariant *)
  Local Definition inv'_def δ N (Px : FM) : iProp Σ := □ δ (inv_jacsr N Px).
  Local Lemma inv'_aux : seal inv'_def. Proof. by eexists. Qed.
  Definition inv' := inv'_aux.(unseal).
  Local Lemma inv'_unseal : inv' = inv'_def. Proof. exact: seal_eq. Qed.

  (** [inv'] is persistent *)
  #[export] Instance inv'_persistent {δ N Px} : Persistent (inv' δ N Px).
  Proof. rewrite inv'_unseal. exact _. Qed.

  (** [inv'] is non-expansive *)
  #[export] Instance inv'_ne {δ N} : NonExpansive (inv' δ N).
  Proof. rewrite inv'_unseal. solve_proper. Qed.
  #[export] Instance inv'_proper {δ N} : Proper ((≡) ==> (⊣⊢)) (inv' δ N).
  Proof. apply ne_proper, _. Qed.
End inv_deriv.

(** Notation *)
Notation invd := (inv' der).

Section inv_deriv.
  Context `{!inv'GS FML Σ, !invGS_gen hlc Σ}.
  Implicit Type (P : iProp Σ) (Px : FML $oi Σ).

  (** Accessor to the invariant body *)
  Definition inv_acsr sm N P : iProp Σ :=
    ∀ E, ⌜↑N ⊆ E⌝ → |=[inv_wsat sm]{E,E∖↑N}=>
      P ∗ (P =[inv_wsat sm]{E∖↑N,E}=∗ True).
  (** [inv_acsr] is non-expansive *)
  #[export] Instance inv_acsr_ne {n} :
    Proper ((≡{n}≡) ==> (=) ==> (≡{n}≡) ==> (≡{n}≡)) inv_acsr.
  Proof. solve_proper. Qed.

  Context `{!InvJudg (FML $oi Σ) JUDG, !Jsem JUDG (iProp Σ),
    !Dsem JUDG (FML $oi Σ) (iProp Σ)}.
  Implicit Type δ : JUDG -n> iProp Σ.

  (** ** [inv_judg_sem]: Semantics of [inv_judgty] *)
  Definition inv_judg_sem δ (NPx : inv_judgty (FML $oi Σ)) : iProp Σ :=
    inv_acsr ⟦⟧(δ) NPx.(untag).1 ⟦ NPx.(untag).2 ⟧(δ).
  (** [inv_judg_sem] is non-expansive *)
  #[export] Instance inv_judg_sem_ne {δ} :
    NonExpansive (inv_judg_sem δ).
  Proof. move=> ?[[??]][[??]][/=/leibniz_equiv_iff<-?]. solve_proper. Qed.
  (** [Dsem] over [inv_judgty] *)
  #[export] Instance inv_judg_dsem
    : Dsem JUDG (inv_judgty (FML $oi Σ)) (iProp Σ) := DSEM inv_judg_sem _.
End inv_deriv.

(** ** [InvJsem]: Judgment semantics for [inv] *)
Notation InvJsem FML Σ JUDG := (Ejsem (inv_judgty (FML $oi Σ)) JUDG (iProp Σ)).

Section inv_deriv.
  Context `{!inv'GS FML Σ, !invGS_gen hlc Σ, !InvJudg (FML $oi Σ) JUDG,
    !Jsem JUDG (iProp Σ), !Dsem JUDG (FML $oi Σ) (iProp Σ),
    !InvJsem FML Σ JUDG}.
  Implicit Type Px Qx : FML $oi Σ.

  (** Access using [invd] *)
  Lemma invd_acc {N Px E} : ↑N ⊆ E →
    invd N Px =[inv_wsat ⟦⟧]{E,E∖↑N}=∗
      ⟦ Px ⟧ ∗ (⟦ Px ⟧ =[inv_wsat ⟦⟧]{E∖↑N,E}=∗ True).
  Proof.
    rewrite inv'_unseal. iIntros (?) "accPx".
    iDestruct (der_sound with "accPx") as "accPx". rewrite sem_ejudg.
    by iApply "accPx".
  Qed.
  (** Access using [invd] via view shift *)
  Lemma invd_acc_vs {N Px E Q R} : ↑N ⊆ E →
    □ (⟦ Px ⟧ -∗ Q =[inv_wsat ⟦⟧]{E∖↑N}=∗ ⟦ Px ⟧ ∗ R) -∗
    □ (invd N Px -∗ Q =[inv_wsat ⟦⟧]{E}=∗ R).
  Proof.
    iIntros (?) "#vs !> i Q". iMod (invd_acc with "i") as "[Px cl]"; [done|].
    iMod ("vs" with "Px Q") as "[Px $]". by iApply "cl".
  Qed.

  Context `{!Deriv (JUDG:=JUDG) ih δ}.

  (** Turn [inv_acsr] into [inv'] *)
  Lemma inv_acsr_inv' {N Px} :
    □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      inv_acsr ⟦⟧(δ') N ⟦ Px ⟧(δ')) ⊢
      inv' δ N Px.
  Proof.
    rewrite inv'_unseal. iIntros "#big !>". iApply Deriv_factor. iIntros (????).
    rewrite sem_ejudg. by iApply "big".
  Qed.

  (** Turn [inv_tok] into [inv'] *)
  Lemma inv_tok_inv' {N Px} : inv_tok N Px ⊢ inv' δ N Px.
  Proof.
    rewrite -inv_acsr_inv'. iIntros "#? !>" (??????). by iApply inv_tok_acc.
  Qed.

  (** Allocate [inv'] *)
  Lemma inv'_alloc_rec Px N :
    (inv' δ N Px -∗ ⟦ Px ⟧(δ)) =[inv_wsat ⟦⟧(δ)]=∗ inv' δ N Px.
  Proof. rewrite -inv_tok_inv'. exact: inv_tok_alloc_rec. Qed.
  Lemma inv'_alloc Px N : ⟦ Px ⟧(δ) =[inv_wsat ⟦⟧(δ)]=∗ inv' δ N Px.
  Proof. rewrite -inv_tok_inv'. exact: inv_tok_alloc. Qed.
  Lemma inv'_alloc_open Px N E : ↑N ⊆ E →
    ⊢ |=[inv_wsat ⟦⟧(δ)]{E, E∖↑N}=> inv' δ N Px ∗
      (⟦ Px ⟧(δ) =[inv_wsat ⟦⟧(δ)]{E∖↑N, E}=∗ True).
  Proof. rewrite -inv_tok_inv'. exact: inv_tok_alloc_open. Qed.

  (** Convert [inv'] with [mod_acsr] *)
  Lemma inv'_acsr {N Px Qx} :
    □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      mod_acsr (fupd ∅ ∅) ⟦ Px ⟧(δ') ⟦ Qx ⟧(δ')) -∗
      inv' δ N Px -∗ inv' δ N Qx.
  Proof.
    rewrite inv'_unseal. iIntros "#PQP #accPx !>". iApply Deriv_factor.
    iIntros (??? to). rewrite to !sem_ejudg. iIntros (? NE).
    iMod ("accPx" $! _ NE) as "[Px cl]".
    iMod (fupd_mask_subseteq ∅) as "→E∖N"; [set_solver|].
    iMod ("PQP" with "[//] [//] [//] Px") as "($& QP)". iMod "→E∖N" as "_".
    iIntros "!> Qx". iMod (fupd_mask_subseteq ∅) as "→E∖N"; [set_solver|].
    iMod ("QP" with "Qx") as "Px". iMod "→E∖N" as "_". iApply ("cl" with "Px").
  Qed.
  Lemma inv'_iff {N Px Qx} :
    □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Px ⟧(δ') ∗-∗ ⟦ Qx ⟧(δ')) -∗
      inv' δ N Px -∗ inv' δ N Qx.
  Proof.
    iIntros "#big". iApply inv'_acsr. iIntros "!>" (????).
    iApply (wand_iff_mod_acsr (M:=fupd _ _)). iModIntro. by iApply "big".
  Qed.

  (** Split [inv'] over [∗] *)
  Local Lemma inv'_sep' {N PQx Px Qx} :
    (∀ δ', ⟦ PQx ⟧(δ') ≡ (⟦ Px ⟧(δ') ∗ ⟦ Qx ⟧(δ'))%I) →
    inv' δ N PQx ⊢ inv' δ N Px.
  Proof.
    iIntros (eq). iApply (inv'_acsr with "[]"). iIntros "!>" (????).
    rewrite eq. iApply (mod_acsr_sep_l (M:=fupd _ _)).
  Qed.
  Lemma inv'_sep {N PQx Px Qx} :
    (∀ δ', ⟦ PQx ⟧(δ') ≡ (⟦ Px ⟧(δ') ∗ ⟦ Qx ⟧(δ'))%I) →
    inv' δ N PQx ⊢ inv' δ N Px ∗ inv' δ N Qx.
  Proof.
    iIntros (eq) "#i". iSplit; [by iApply inv'_sep'|].
    iApply (inv'_sep' with "i"). iIntros (?). by rewrite eq comm.
  Qed.

  (** Merge [inv']s with [∗] *)
  Lemma inv'_merge {N1 N2 N Px Qx PQx} : N1 ## N2 → ↑N1 ∪ ↑N2 ⊆@{coPset} ↑N →
    (∀ δ', ⟦ PQx ⟧(δ') ≡ (⟦ Px ⟧(δ') ∗ ⟦ Qx ⟧(δ'))%I) →
    inv' δ N1 Px -∗ inv' δ N2 Qx -∗ inv' δ N PQx.
  Proof.
    rewrite inv'_unseal. iIntros (?? eq) "#i #i' !>".
    iApply (Deriv_map2 with "[] i i'"). iIntros (????) "{i}i {i'}i'".
    rewrite !sem_ejudg. iIntros (??). rewrite eq.
    iMod ("i" with "[%]") as "[$ Px→]"; [set_solver|].
    iMod ("i'" with "[%]") as "[$ Qx→]"; [set_solver|].
    iApply fupdw_mask_intro; [set_solver|]. iIntros "cl [Px Qx]".
    iMod "cl" as "_". iMod ("Qx→" with "Qx") as "_". iApply ("Px→" with "Px").
  Qed.
End inv_deriv.

Section inv_deriv_wp.
  Context `{!inv'GS FML Σ, !iris'GS_gen hlc Λ Σ, !InvJudg (FML $oi Σ) JUDG,
    !Jsem JUDG (iProp Σ), !Dsem JUDG (FML $oi Σ) (iProp Σ),
    !InvJsem FML Σ JUDG}.

  (** Access using [invd] via [twp] *)
  Lemma invd_acc_twp `{!Atomic (stuckness_to_atomicity s) e} {N Px E Q Ψ} :
    ↑N ⊆ E → to_val e = None →
    [[{ ⟦ Px ⟧ ∗ Q }]][inv_wsat ⟦⟧]
      e @ s; E∖↑N
    [[{ v, RET v; ⟦ Px ⟧ ∗ Ψ v }]] -∗
      [[{ invd N Px ∗ Q }]][inv_wsat ⟦⟧] e @ s; E [[{ v, RET v; Ψ v }]].
  Proof.
    iIntros (??) "#twp %Φ !> [i Q] →Φ".
    iMod (invd_acc with "i") as "[Px cl]"; [done..|].
    iApply ("twp" with "[$Px $Q //]"). iIntros (?) "[Px Ψ]".
    iMod ("cl" with "Px") as "_". iModIntro. by iApply "→Φ". Unshelve.
  Qed.
End inv_deriv_wp.
