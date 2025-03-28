(** * Non-atomic invariants relaxed with derivability *)

From nola.util Require Import tagged.
From nola.util Require Export prod.
From nola.bi Require Export deriv.
From nola.iris Require Export na_inv.
From iris.proofmode Require Import proofmode.
Import ProdNotation iPropAppNotation ModwNotation DsemNotation.

Implicit Type (p : na_inv_pool_name) (N : namespace) (FM : ofe) (Σ : gFunctors).

(** [na_invJT]: Judgment type for [na_inv] *)
Variant na_invJT_id FM := .
Definition na_invJT (FM : ofe) : ofe :=
  tagged (na_invJT_id FM) (leibnizO (na_inv_pool_name *' namespace) * FM).
(** [na_invJ]: [na_invJT] registered *)
Notation na_invJ FM JUDG := (inJ (na_invJT FM) JUDG).

Section na_invJ.
  Context `{na_inv_j : !na_invJ FM JUDG} {Σ : gFunctors}.
  Implicit Type δ : JUDG -n> iProp Σ.

  (** Accessor judgment *)
  Local Definition na_inv_jacsr p N Px : JUDG :=
    na_inv_j (Tagged ((p, N)', Px)).
  Local Instance na_inv_jacsr_ne {p N} : NonExpansive (na_inv_jacsr p N).
  Proof. unfold na_inv_jacsr=> ????. f_equiv. by split. Qed.

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
  #[export] Instance na_inv'_ne {δ p N} : NonExpansive (na_inv' δ p N).
  Proof. rewrite na_inv'_unseal. solve_proper. Qed.
  #[export] Instance na_inv'_proper {δ p N} :
    Proper ((≡) ==> (⊣⊢)) (na_inv' δ p N).
  Proof. apply ne_proper, _. Qed.
End na_invJ.

(** Notation *)
Notation na_invd := (na_inv' der).

Section na_invJ.
  Context `{!inv'GS (cifOF CON) Σ, !invGS_gen hlc Σ, !na_invG Σ}.
  Implicit Type P : iProp Σ.

  (** Accessor *)
  Definition na_inv_acsr sm p N P : iProp Σ :=
    ∀ E F, ⌜↑N ⊆ E⌝ → ⌜↑N ⊆ F⌝ → na_own p F =[inv_wsat sm]{E}=∗
      na_own p (F∖↑N) ∗ P ∗
      (na_own p (F∖↑N) -∗ P =[inv_wsat sm]{E}=∗ na_own p F) .
  (** [na_inv_acsr] is non-expansive *)
  #[export] Instance na_inv_acsr_ne {n} :
    Proper ((≡{n}≡) ==> (=) ==> (=) ==> (≡{n}≡) ==> (≡{n}≡)) na_inv_acsr.
  Proof. solve_proper. Qed.

  Context `{!na_invJ (cif CON Σ) JUDG, !Dsem JUDG (cif CON Σ) (iProp Σ)}.
  Implicit Type δ : JUDG -n> iProp Σ.

  (** ** [na_invJT_sem]: Semantics of [na_invJT] *)
  Definition na_invJT_sem δ (J : na_invJT (cif CON Σ)) : iProp Σ :=
    na_inv_acsr ⟦⟧(δ) J.(untag).1.1' J.(untag).1.2' ⟦ J.(untag).2 ⟧(δ).
  (** [na_invJT_sem] is non-expansive *)
  #[export] Instance na_invJT_sem_ne {δ} : NonExpansive (na_invJT_sem δ).
  Proof. move=> ?[[??]][[??]][/=/leibniz_equiv_iff<-?]. solve_proper. Qed.
  (** [Dsem] over [na_invJT] *)
  #[export] Instance na_invJT_dsem
    : Dsem JUDG (na_invJT (cif CON Σ)) (iProp Σ) := DSEM na_invJT_sem _.
End na_invJ.
(** [na_invJS]: Semantics of [na_invJT] registered *)
Notation na_invJS CON JUDG Σ := (inJS (na_invJT (cif CON Σ)) JUDG (iProp Σ)).

Section na_inv_deriv.
  Context `{!inv'GS (cifOF CON) Σ, !invGS_gen hlc Σ, !na_invG Σ,
    !na_invJ (cif CON Σ) JUDG, !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ),
    !na_invJS CON JUDG Σ}.
  Implicit Type Px Qx : cif CON Σ.

  (** Access using [na_invd] *)
  Lemma na_invd_acc {p N Px E F} : ↑N ⊆ E → ↑N ⊆ F →
    na_own p F -∗ na_invd p N Px =[inv_wsat ⟦⟧]{E}=∗
      na_own p (F∖↑N) ∗ ⟦ Px ⟧ ∗
      (na_own p (F∖↑N) -∗ ⟦ Px ⟧ =[inv_wsat ⟦⟧]{E}=∗ na_own p F).
  Proof.
    rewrite na_inv'_unseal. iIntros (NE NF) "F accP".
    iDestruct (der_sound with "accP") as "accP". rewrite in_js.
    iApply ("accP" $! _ _ NE NF with "F").
  Qed.

  Context `{!Deriv (JUDG:=JUDG) ih δ}.

  (** Weaken the namespace of [na_inv'] *)
  Lemma na_inv'_subset {p N N' Px} : ↑N ⊆@{coPset} ↑N' →
    na_inv' δ p N Px ⊢ na_inv' δ p N' Px.
  Proof.
    rewrite na_inv'_unseal=> ?. iIntros "#δ !>". iApply (Deriv_map with "[] δ").
    iIntros (????). rewrite !in_js /=. iIntros "acc" (????) "p"=>/=.
    iMod ("acc" with "[%] [%] p") as "/=(p & $ & cl)"; [set_solver..|].
    iModIntro. iDestruct (na_own_acc with "p") as "[$ →p]"; [set_solver|].
    iIntros "p Px". iDestruct ("→p" with "p") as "p". iApply ("cl" with "p Px").
  Qed.

  (** Turn [na_inv_acsr] into [na_inv'] *)
  Lemma na_inv_acsr_inv' {p N Px} :
    □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      na_inv_acsr ⟦⟧(δ') p N ⟦ Px ⟧(δ')) ⊢
      na_inv' δ p N Px.
  Proof.
    rewrite na_inv'_unseal. iIntros "#big !>". iApply Deriv_factor.
    iIntros (????). rewrite in_js. by iApply "big".
  Qed.

  (** Turn [na_inv_tok] into [na_inv'] *)
  Lemma na_inv_tok_na_inv' {p N Px} : na_inv_tok p N Px ⊢ na_inv' δ p N Px.
  Proof.
    rewrite -na_inv_acsr_inv'. iIntros "#i !>" (????????) "F".
    by iApply (na_inv_tok_acc with "F i").
  Qed.

  (** Allocate [na_inv'] *)
  Lemma na_inv'_alloc_suspend p Px N :
    inv_wsat ⟦⟧(δ) ==∗ na_inv' δ p N Px ∗ (⟦ Px ⟧(δ) -∗ inv_wsat ⟦⟧(δ)).
  Proof. rewrite -na_inv_tok_na_inv'. exact: na_inv_tok_alloc_suspend. Qed.
  Lemma na_inv'_alloc p Px N :
    ⟦ Px ⟧(δ) =[inv_wsat ⟦⟧(δ)]=∗ na_inv' δ p N Px.
  Proof. rewrite -na_inv_tok_na_inv'. exact: na_inv_tok_alloc. Qed.
  Lemma na_inv'_alloc_open p N E F Px :
    ↑N ⊆ E → ↑N ⊆ F →
    na_own p F =[inv_wsat ⟦⟧(δ)]{E}=∗
      na_own p (F∖↑N) ∗ na_inv' δ p N Px ∗
      (na_own p (F∖↑N) -∗ ⟦ Px ⟧(δ) =[inv_wsat ⟦⟧(δ)]{E}=∗ na_own p F).
  Proof. rewrite -na_inv_tok_na_inv'. exact: na_inv_tok_alloc_open. Qed.

  (** Convert [na_inv'] with [mod_acsr] *)
  Lemma na_inv'_acsr {p N Px Qx} :
    □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      mod_acsr (fupd ∅ ∅) ⟦ Px ⟧(δ') ⟦ Qx ⟧(δ')) -∗
      na_inv' δ p N Px -∗ na_inv' δ p N Qx.
  Proof.
    rewrite na_inv'_unseal. iIntros "#PQP #accP !>". iApply Deriv_factor.
    iIntros (??? to). rewrite to !in_js. iIntros (?? NE NF) "F".
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
    rewrite !in_js. iIntros (????) "F". rewrite eq.
    iMod ("i" with "[%] [%] F") as "(F∖N1 & $ & P→)"; [set_solver..|].
    iMod ("i'" with "[%] [%] F∖N1") as "(F∖N12 & $ & Q→)"; [set_solver..|].
    iDestruct (na_own_acc with "F∖N12") as "[$ F∖N→]"; [set_solver|].
    iApply fupdw_mask_intro; [set_solver|]. iIntros "cl F∖N [Px Qx]".
    iMod "cl" as "_". iDestruct ("F∖N→" with "F∖N") as "F∖N12".
    iMod ("Q→" with "F∖N12 Qx") as "F∖N". iApply ("P→" with "F∖N Px").
  Qed.
End na_inv_deriv.

(** ** Constructor *)

From nola.iris Require Import cif.

(** [na_invCT]: Constructor for [na_inv'] *)
Variant na_invCT_id := .
Definition na_invCT :=
  Cifcon na_invCT_id (na_inv_pool_name *' namespace) (λ _, Empty_set)
    (λ _, unit) (λ _, unitO) _.
(** [na_invC]: [na_invCT] registered *)
Notation na_invC := (inC na_invCT).

Section na_invC.
  Context `{!na_invC CON} {Σ}.
  (** [cif_na_inv]: Formula for [na_inv'] *)
  Definition cif_na_inv p N (Px : cif CON Σ) : cif CON Σ :=
    cif_in na_invCT (p, N)' nullary (unary Px) ().
  (** [cif_na_inv] is non-expansive *)
  #[export] Instance cif_na_inv_ne {p N} : NonExpansive (cif_na_inv p N).
  Proof. solve_proper. Qed.
  #[export] Instance cif_na_inv_proper {p N} :
    Proper ((≡) ==> (≡)) (cif_na_inv p N).
  Proof. apply ne_proper, _. Qed.
  (** [cif_na_inv] is productive *)
  #[export] Instance cif_na_inv_productive {p N} : Productive (cif_na_inv p N).
  Proof.
    move=> ????. apply cif_in_preserv_productive=>//. by apply fun_proeqv_later.
  Qed.

  Context `{!inv'GS (cifOF CON) Σ, !na_invGS (cifOF CON) Σ,
    !na_invJ (cifO CON Σ) JUDG}.
  (** Semantics of [na_invCT] *)
  #[export] Program Instance na_invCT_ecsem : Ecsem na_invCT CON JUDG Σ :=
    ECSEM (λ _ δ '(p, N)' _ Φx _, na_inv' δ p N (Φx ())) _.
  Next Obligation. solve_proper. Qed.
End na_invC.
(** [na_invC] semantics registered *)
Notation na_invCS := (inCS na_invCT).

Section na_invC.
  Context `{!Csem CON JUDG Σ, !na_invC CON, !inv'GS (cifOF CON) Σ,
    !na_invGS (cifOF CON) Σ, !na_invJ (cifO CON Σ) JUDG, !na_invCS CON JUDG Σ}.
  (** Reify [na_inv'] *)
  #[export] Program Instance na_inv'_as_cif {p N Px} :
    AsCif CON (λ δ, na_inv' δ p N Px) := AS_CIF (cif_na_inv p N Px) _.
  Next Obligation. move=>/= >. by rewrite sem_cif_in. Qed.
End na_invC.
