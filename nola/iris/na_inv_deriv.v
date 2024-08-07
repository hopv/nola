(** * Non-atomic invariant machinery relaxed with derivability *)

From nola.bi Require Export deriv.
From nola.iris Require Export na_inv.
From iris.proofmode Require Import proofmode.
Import iPropAppNotation PsemNotation SemNotation UpdwNotation.

(** Notation *)
Notation na_inv_wsati δ := (na_inv_wsat ⟦⟧(δ)).
Notation na_inv_wsatid := (na_inv_wsati der).

(** Derivability pre-data for [na_inv] *)
Class NaInvPreDeriv (FM JUDG : ofe) := NA_INV_PRE_DERIV {
  (** Accessor judgment *)
  na_inv_jacsr : na_inv_pool_name → namespace → FM → JUDG;
  (** [na_inv_jacsr] is non-expansive *)
  na_inv_jacsr_ne {p N} :: NonExpansive (na_inv_jacsr p N);
}.
Hint Mode NaInvPreDeriv ! - : typeclass_instances.
Arguments NA_INV_PRE_DERIV {_ _} _ {_}.

Section na_inv_deriv.
  Context `{!NaInvPreDeriv FM JUDG} {Σ : gFunctors}.
  Implicit Type δ : JUDG → iProp Σ.

  (** [na_inv']: Relaxed na_invariant *)
  Local Definition na_inv'_def δ p N (Px : FM) : iProp Σ :=
    □ δ (na_inv_jacsr p N Px).
  Local Lemma na_inv'_aux : seal na_inv'_def. Proof. by eexists. Qed.
  Definition na_inv' := na_inv'_aux.(unseal).
  Local Lemma na_inv'_unseal : na_inv' = na_inv'_def.
  Proof. exact: seal_eq. Qed.

  (** [na_inv'] is persistent *)
  #[export] Instance na_inv'_persistent {δ p N Px} :
    Persistent (na_inv' δ p N Px).
  Proof. rewrite na_inv'_unseal. exact _. Qed.

  (** [na_inv'] is non-expansive *)
  #[export] Instance na_inv'_ne `{!NonExpansive δ} {p N} :
    NonExpansive (na_inv' δ p N).
  Proof. rewrite na_inv'_unseal. solve_proper. Qed.
End na_inv_deriv.
Notation na_invd := (na_inv' der).

Section na_inv_deriv.
  Context `{!na_inv'GS FML Σ, !invGS_gen hlc Σ, !na_invG Σ}.
  Implicit Type Px Qx PQx : FML $oi Σ.

  (** Accessor *)
  Definition na_inv_acsr sm p N Pi : iProp Σ :=
    ∀ E F, ⌜↑N ⊆ E⌝ → ⌜↑N ⊆ F⌝ → na_own p F =[na_inv_wsat sm]{E}=∗
      na_own p (F∖↑N) ∗ Pi ∗
      (na_own p (F∖↑N) -∗ Pi =[na_inv_wsat sm]{E}=∗ na_own p F) .

  Context `{!NaInvPreDeriv (FML $oi Σ) (JUDGI : judgi (iProp Σ)),
    !Dsem JUDGI (FML $oi Σ) (iProp Σ)}.
  Implicit Type δ : JUDGI → iProp Σ.

  (** Derivability data for [na_inv] *)
  Class NaInvDeriv :=
    (** Interpreting [na_inv_jacsr] *)
    na_inv_jacsr_sem : ∀{δ p N Px},
      ⟦ na_inv_jacsr p N Px ⟧(δ) ⊣⊢ na_inv_acsr ⟦⟧(δ) p N (⟦ Px ⟧(δ)).

  Context `{!NaInvDeriv}.

  (** Access using [na_invd] *)
  Lemma na_invd_acc {p N Px E F} : ↑N ⊆ E → ↑N ⊆ F →
    na_own p F -∗ na_invd p N Px =[na_inv_wsatid]{E}=∗
      na_own p (F∖↑N) ∗ ⟦ Px ⟧ ∗
      (na_own p (F∖↑N) -∗ ⟦ Px ⟧ =[na_inv_wsatid]{E}=∗ na_own p F).
  Proof.
    rewrite na_inv'_unseal. iIntros (NE NF) "F accP".
    iDestruct (der_sound with "accP") as "accP". rewrite na_inv_jacsr_sem.
    iApply ("accP" $! _ _ NE NF with "F").
  Qed.

  Context `{!Deriv (JUDGI:=JUDGI) ih δ}.

  (** Turn [na_inv_acsr] into [na_inv'] *)
  Lemma na_inv_acsr_inv' {p N Px} :
    □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      na_inv_acsr ⟦⟧(δ') p N ⟦ Px ⟧(δ')) ⊢ na_inv' δ p N Px.
  Proof.
    rewrite na_inv'_unseal. iIntros "#big !>". iApply Deriv_factor.
    iIntros (????). rewrite na_inv_jacsr_sem. by iApply "big".
  Qed.

  (** Turn [na_inv_tok] into [na_inv'] *)
  Lemma na_inv_tok_na_inv' {p N Px} : na_inv_tok p N Px ⊢ na_inv' δ p N Px.
  Proof.
    rewrite -na_inv_acsr_inv'. iIntros "#i !>" (δ' ???????) "F".
    by iApply (na_inv_tok_acc (sm:=⟦⟧(δ')) with "F i").
  Qed.

  (** Allocate [na_inv'] *)
  Lemma na_inv'_alloc_rec p Px N :
    (na_inv' δ p N Px -∗ ⟦ Px ⟧(δ)) =[na_inv_wsati δ]=∗ na_inv' δ p N Px.
  Proof. rewrite -na_inv_tok_na_inv'. exact: na_inv_tok_alloc_rec. Qed.
  Lemma na_inv'_alloc p Px N : ⟦ Px ⟧(δ) =[na_inv_wsati δ]=∗ na_inv' δ p N Px.
  Proof. rewrite -na_inv_tok_na_inv'. exact: na_inv_tok_alloc. Qed.
  Lemma na_inv'_alloc_open p N E F Px :
    ↑N ⊆ E → ↑N ⊆ F →
    na_own p F =[na_inv_wsati δ]{E}=∗
      na_own p (F∖↑N) ∗ na_inv' δ p N Px ∗
      (na_own p (F∖↑N) -∗ ⟦ Px ⟧(δ) =[na_inv_wsati δ]{E}=∗ na_own p F).
  Proof. rewrite -na_inv_tok_na_inv'. exact: na_inv_tok_alloc_open. Qed.

  (** Convert [na_inv'] with [mod_acsr] *)
  Lemma na_inv'_acsr {p N Px Qx} :
    □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      mod_acsr (fupd ∅ ∅) ⟦ Px ⟧(δ') ⟦ Qx ⟧(δ')) -∗
      na_inv' δ p N Px -∗ na_inv' δ p N Qx.
  Proof.
    rewrite na_inv'_unseal. iIntros "#PQP #accP !>". iApply Deriv_factor.
    iIntros (??? to). rewrite to !na_inv_jacsr_sem. iIntros (?? NE NF) "F".
    iMod ("accP" $! _ _ NE NF with "F") as "($ & Px & cl)".
    iMod (fupd_mask_subseteq ∅) as "→E∖N"; [set_solver|].
    iMod ("PQP" with "[//] [//] [//] Px") as "[$ QP]". iMod "→E∖N" as "_".
    iIntros "!>". iMod (fupd_mask_subseteq ∅) as "→E∖N"; [set_solver|].
    iIntros "F∖N Qx". iMod ("QP" with "Qx") as "Px". iMod "→E∖N" as "_".
    iApply ("cl" with "F∖N Px").
  Qed.
  Lemma na_inv'_iff {p N Px Qx} :
    □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Px ⟧(δ') ∗-∗ ⟦ Qx ⟧(δ')) -∗
      na_inv' δ p N Px -∗ na_inv' δ p N Qx.
  Proof.
    iIntros "#big". iApply na_inv'_acsr. iIntros "!>" (????).
    iApply (wand_iff_mod_acsr (M:=fupd _ _)). iModIntro. by iApply "big".
  Qed.

  (** Split [na_inv'] over [∗] *)
  Local Lemma na_inv'_sep' {p N PQx Px Qx} :
    (∀ δ', ⟦ PQx ⟧(δ') ≡ (⟦ Px ⟧(δ') ∗ ⟦ Qx ⟧(δ'))%I) →
    na_inv' δ p N PQx ⊢ na_inv' δ p N Px.
  Proof.
    iIntros (eq). iApply (na_inv'_acsr with "[]"). iIntros "!>" (????).
    rewrite eq. iApply (mod_acsr_sep_l (M:=fupd _ _)).
  Qed.
  Lemma na_inv'_sep {p N PQx Px Qx} :
    (∀ δ', ⟦ PQx ⟧(δ') ≡ (⟦ Px ⟧(δ') ∗ ⟦ Qx ⟧(δ'))%I) →
    na_inv' δ p N PQx ⊢ na_inv' δ p N Px ∗ na_inv' δ p N Qx.
  Proof.
    iIntros (eq) "#i". iSplit; [by iApply na_inv'_sep'|].
    iApply (na_inv'_sep' with "i"). iIntros (?). by rewrite eq comm.
  Qed.

  (** Merge [na_inv']s with [∗] *)
  Lemma na_inv'_merge {p N1 N2 N Px Qx PQx} :
    N1 ## N2 → ↑N1 ∪ ↑N2 ⊆@{coPset} ↑N →
    (∀ δ', ⟦ PQx ⟧(δ') ≡ (⟦ Px ⟧(δ') ∗ ⟦ Qx ⟧(δ'))%I) →
    na_inv' δ p N1 Px -∗ na_inv' δ p N2 Qx -∗ na_inv' δ p N PQx.
  Proof.
    rewrite na_inv'_unseal. iIntros (?? eq) "#i #i' !>".
    iApply (Deriv_map2 with "[] i i'"). iIntros (????) "{i}i {i'}i'".
    rewrite !na_inv_jacsr_sem. iIntros (????) "F". rewrite eq.
    iMod ("i" with "[%] [%] F") as "(F∖N1 & $ & P→)"; [set_solver..|].
    iMod ("i'" with "[%] [%] F∖N1") as "(F∖N12 & $ & Q→)"; [set_solver..|].
    iDestruct (na_own_acc with "F∖N12") as "[$ F∖N→]"; [set_solver|].
    iApply fupdw_mask_intro; [set_solver|]. iIntros "cl F∖N [Px Qx]".
    iMod "cl" as "_". iDestruct ("F∖N→" with "F∖N") as "F∖N12".
    iMod ("Q→" with "F∖N12 Qx") as "F∖N". iApply ("P→" with "F∖N Px").
  Qed.
End na_inv_deriv.
Arguments NaInvDeriv FML Σ {_ _ _ _} JUDGI {_ _}.
Hint Mode NaInvDeriv ! - - - - - - - - : typeclass_instances.
