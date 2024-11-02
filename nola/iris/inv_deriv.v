(** * Invariants relaxed with derivability *)

From nola.util Require Import tagged.
From nola.bi Require Export deriv.
From nola.bi Require Import wpw.
From nola.iris Require Export inv.
From iris.proofmode Require Import proofmode.
Import iPropAppNotation ModwNotation WpwNotation DsemNotation.

Implicit Type (Σ : gFunctors) (N : namespace) (FM : ofe).

(** ** [invJT]: Judgment type for [inv] *)
Variant invJT_id FM := .
Definition invJT (FM : ofe) : ofe :=
  (** Accessor judgment *) tagged (invJT_id FM) (leibnizO namespace * FM).

(** ** [invJ]: [invJT] registered *)
Notation invJ FM := (inJ (invJT FM)).

Section invJ.
  Context `{inv_j : !invJ FM JUDG} {Σ}.
  Implicit Type (δ : JUDG -n> iProp Σ) (Px : FM).

  (** Accessor judgment *)
  Local Definition inv_jacsr N Px : JUDG := inv_j (Tagged (N, Px)).
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
End invJ.

(** Notation *)
Notation invd := (inv' der).

Section invJ.
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

  Context `{!invJ (FML $oi Σ) JUDG, !Dsem JUDG (FML $oi Σ) (iProp Σ),
    !Jsem JUDG (iProp Σ)}.
  Implicit Type δ : JUDG -n> iProp Σ.

  (** ** [invJT_sem]: Semantics of [invJT] *)
  Definition invJT_sem δ (NPx : invJT (FML $oi Σ)) : iProp Σ :=
    inv_acsr ⟦⟧(δ) NPx.(untag).1 ⟦ NPx.(untag).2 ⟧(δ).
  (** [invJT_sem] is non-expansive *)
  #[export] Instance invJT_sem_ne {δ} : NonExpansive (invJT_sem δ).
  Proof. move=> ?[[??]][[??]][/=/leibniz_equiv_iff<-?]. solve_proper. Qed.
  (** [Dsem] over [invJT] *)
  #[export] Instance invJT_dsem : Dsem JUDG (invJT (FML $oi Σ)) (iProp Σ) :=
    DSEM invJT_sem _.
End invJ.

(** ** [invJS]: Semantics of [invJT] registered *)
Notation invJS FML JUDG Σ := (inJS (invJT (FML $oi Σ)) JUDG (iProp Σ)).

Section inv_deriv.
  Context `{!inv'GS FML Σ, !invGS_gen hlc Σ, !invJ (FML $oi Σ) JUDG,
    !Dsem JUDG (FML $oi Σ) (iProp Σ), !Jsem JUDG (iProp Σ), !invJS FML JUDG Σ}.
  Implicit Type Px Qx : FML $oi Σ.

  (** Access using [invd] *)
  Lemma invd_acc {N Px E} : ↑N ⊆ E →
    invd N Px =[inv_wsat ⟦⟧]{E,E∖↑N}=∗
      ⟦ Px ⟧ ∗ (⟦ Px ⟧ =[inv_wsat ⟦⟧]{E∖↑N,E}=∗ True).
  Proof.
    rewrite inv'_unseal. iIntros (?) "accPx".
    iDestruct (der_sound with "accPx") as "accPx". rewrite in_js.
    by iApply "accPx".
  Qed.
  (** Access using [invd] via view shift, for presentation *)
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
    rewrite in_js. by iApply "big".
  Qed.

  (** Turn [inv_tok] into [inv'] *)
  Lemma inv_tok_inv' {N Px} : inv_tok N Px ⊢ inv' δ N Px.
  Proof.
    rewrite -inv_acsr_inv'. iIntros "#? !>" (??????). by iApply inv_tok_acc.
  Qed.

  (** Allocate [inv'] *)
  Lemma inv'_alloc_suspend Px N :
    inv_wsat ⟦⟧(δ) ==∗ inv' δ N Px ∗ (⟦ Px ⟧(δ) -∗ inv_wsat ⟦⟧(δ)).
  Proof. rewrite -inv_tok_inv'. exact: inv_tok_alloc_suspend. Qed.
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
    iIntros (??? to). rewrite to !in_js. iIntros (? NE).
    iMod ("accPx" $! _ NE) as "[Px cl]".
    iMod (fupd_mask_subseteq ∅) as "→E∖N"; [set_solver|].
    iMod ("PQP" with "[//] [//] [//] Px") as "[$ QP]". iMod "→E∖N" as "_".
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
    rewrite !in_js. iIntros (??). rewrite eq.
    iMod ("i" with "[%]") as "[$ Px→]"; [set_solver|].
    iMod ("i'" with "[%]") as "[$ Qx→]"; [set_solver|].
    iApply fupdw_mask_intro; [set_solver|]. iIntros "cl [Px Qx]".
    iMod "cl" as "_". iMod ("Qx→" with "Qx") as "_". iApply ("Px→" with "Px").
  Qed.
End inv_deriv.

Section inv_deriv_wp.
  Context `{!inv'GS FML Σ, !iris'GS_gen hlc Λ Σ, !invJ (FML $oi Σ) JUDG,
    !Dsem JUDG (FML $oi Σ) (iProp Σ), !Jsem JUDG (iProp Σ), !invJS FML JUDG Σ}.

  (** Access using [invd] via [twp], for presentation *)
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

(** ** Constructor *)

From nola.iris Require Import cif.

(** [invCT]: Constructor for [inv'] *)
Variant invCT_id := .
Definition invCT :=
  Cifcon invCT_id namespace (λ _, Empty_set) (λ _, unit) (λ _, unitO) _.
(** [invC]: [invCT] registered *)
Notation invC := (inC invCT).

Section invC.
  Context `{!invC CON} {Σ}.
  (** [cif_inv]: Formula for [inv'] *)
  Definition cif_inv N (Px : cif CON Σ) : cif CON Σ :=
    cif_in invCT N nullary (unary Px) ().
  (** [cif_inv] is non-expansive *)
  #[export] Instance cif_inv_ne {N} : NonExpansive (cif_inv N).
  Proof. move=> ????. apply cif_in_ne; solve_proper. Qed.
  #[export] Instance cif_inv_proper {N} : Proper ((≡) ==> (≡)) (cif_inv N).
  Proof. apply ne_proper, _. Qed.
  (** [cif_inv] is productive *)
  #[export] Instance cif_inv_productive {N} : Productive (cif_inv N).
  Proof.
    move=> ????. apply cif_in_preserv_productive=>//.
    by apply fun_proeq_later.
  Qed.

  Context `{!inv'GS (cifOF CON) Σ, !invJ (cifO CON Σ) JUDG}.
  (** Semantics of [invCT] *)
  #[export] Program Instance invCT_ecsem : Ecsem invCT CON JUDG Σ :=
    ECSEM (λ _ δ N _ Φx _, inv' δ N (Φx ())) _.
  Next Obligation. move=> ??*???*?? eqv ?*. f_equiv. apply eqv. Qed.
End invC.
(** [invC] semantics registered *)
Notation invCS := (inCS invCT).

(** Reify [inv'] *)
#[export] Program Instance inv'_as_cif `{!Csem CON JUDG Σ, !invC CON}
  `{!inv'GS (cifOF CON) Σ, !invJ (cifO CON Σ) JUDG, !invCS CON JUDG Σ} {N Px} :
  AsCif CON (λ δ, inv' δ N Px) := AS_CIF (cif_inv N Px) _.
Next Obligation. move=>/= *. by rewrite sem_cif_in. Qed.
