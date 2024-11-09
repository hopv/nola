(** * Direct dinvariants relaxed with derivability *)

From nola.util Require Import tagged.
From nola.bi Require Export deriv.
From nola.iris Require Export dinv.
From iris.proofmode Require Import proofmode.
Import iPropAppNotation ModwNotation DsemNotation.

Implicit Type (Σ : gFunctors) (FM : ofe).

(** ** [dinvJT]: Judgment type for [dinv] *)
Variant dinvJT_id FM := .
Definition dinvJT (FM : ofe) : ofe :=
  (** Accessor judgment *) tagged (dinvJT_id FM) FM.

(** ** [dinvJ]: [dinvJT] registered *)
Notation dinvJ FM := (inJ (dinvJT FM)).

Section dinvJ.
  Context `{dinv_j : !dinvJ FM JUDG} {Σ}.
  Implicit Type (δ : JUDG -n> iProp Σ) (Px : FM).

  (** Accessor judgment *)
  Local Definition dinv_jacsr Px : JUDG := dinv_j (Tagged Px).
  Local Instance dinv_jacsr_ne : NonExpansive dinv_jacsr.
  Proof. solve_proper. Qed.

  (** [dinv]: Relaxed direct invariant *)
  Local Definition dinv_def δ (Px : FM) : iProp Σ := □ δ (dinv_jacsr Px).
  Local Lemma dinv_aux : seal dinv_def. Proof. by eexists. Qed.
  Definition dinv := dinv_aux.(unseal).
  Local Lemma dinv_unseal : dinv = dinv_def. Proof. exact: seal_eq. Qed.

  (** [dinv] is persistent *)
  #[export] Instance dinv_persistent {δ Px} : Persistent (dinv δ Px).
  Proof. rewrite dinv_unseal. exact _. Qed.

  (** [dinv] is non-expansive *)
  #[export] Instance dinv_ne {δ} : NonExpansive (dinv δ).
  Proof. rewrite dinv_unseal. solve_proper. Qed.
  #[export] Instance dinv_proper {δ} : Proper ((≡) ==> (⊣⊢)) (dinv δ).
  Proof. apply ne_proper, _. Qed.
End dinvJ.

(** Notation *)
Notation dinvd := (dinv der).

Section dinvJ.
  Context `{!dinvGS FML Σ, !dinvJ (FML $oi Σ) JUDG,
    !Dsem JUDG (FML $oi Σ) (iProp Σ)}.
  Implicit Type δ : JUDG -n> iProp Σ.

  (** ** [dinvJT_sem]: Semantics of [dinvJT] *)
  Definition dinvJT_sem δ (J : dinvJT (FML $oi Σ)) : iProp Σ :=
    dinv_wsat ⟦⟧(δ) -∗ ⟦ J.(untag) ⟧(δ) ∗ (⟦ J.(untag) ⟧(δ) -∗ dinv_wsat ⟦⟧(δ)).
  (** [dinvJT_sem] is non-expansive *)
  #[export] Instance dinvJT_sem_ne {δ} : NonExpansive (dinvJT_sem δ).
  Proof. solve_proper. Qed.
  (** [Dsem] over [dinvJT] *)
  #[export] Instance dinvJT_dsem : Dsem JUDG (dinvJT (FML $oi Σ)) (iProp Σ) :=
    DSEM dinvJT_sem _.
End dinvJ.
Arguments dinvJT_sem _ _ /.

(** ** [dinvJS]: Semantics of [dinvJT] registered *)
Notation dinvJS FML JUDG Σ := (inJS (dinvJT (FML $oi Σ)) JUDG (iProp Σ)).

Section dinv_deriv.
  Context `{!dinvGS FML Σ, !dinvJ (FML $oi Σ) JUDG,
    !Dsem JUDG (FML $oi Σ) (iProp Σ), !Jsem JUDG (iProp Σ), !dinvJS FML JUDG Σ}.
  Implicit Type Px Qx : FML $oi Σ.

  (** Access using [dinvd] *)
  Lemma dinvd_acc {Px} :
    dinvd Px -∗ dinv_wsat ⟦⟧ -∗ ⟦ Px ⟧ ∗ (⟦ Px ⟧ -∗ dinv_wsat ⟦⟧).
  Proof.
    rewrite dinv_unseal. iIntros "accPx".
    iDestruct (der_sound with "accPx") as "accPx". by rewrite in_js.
  Qed.

  Context `{!Deriv (JUDG:=JUDG) ih δ}.

  (** Turn an accessor into [dinv] *)
  Lemma dinv_acsr_dinv {Px} :
    □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      dinv_wsat ⟦⟧(δ') -∗ ⟦ Px ⟧(δ') ∗ (⟦ Px ⟧(δ') -∗ dinv_wsat ⟦⟧(δ'))) ⊢
      dinv δ Px.
  Proof.
    rewrite dinv_unseal. iIntros "#big !>". iApply Deriv_factor. iIntros (????).
    rewrite in_js /=. by iApply "big".
  Qed.

  (** Turn [dinv_tok] into [dinv] *)
  Lemma dinv_tok_dinv {Px} : dinv_tok Px ⊢ dinv δ Px.
  Proof.
    rewrite -dinv_acsr_dinv. iIntros "#? !>" (????). by iApply dinv_tok_acc.
  Qed.

  (** Allocate [dinv] *)
  Lemma dinv_alloc_suspend Px :
    dinv_wsat ⟦⟧(δ) ==∗ dinv δ Px ∗ (⟦ Px ⟧(δ) -∗ dinv_wsat ⟦⟧(δ)).
  Proof. rewrite -dinv_tok_dinv. exact: dinv_tok_alloc_suspend. Qed.
  Lemma dinv_alloc Px : ⟦ Px ⟧(δ) =[dinv_wsat ⟦⟧(δ)]=∗ dinv δ Px.
  Proof. rewrite -dinv_tok_dinv. exact: dinv_tok_alloc. Qed.

  (** Convert [dinv] with an accessor *)
  Lemma dinv_acsr {Px Qx} :
    □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Px ⟧(δ') -∗ ⟦ Qx ⟧(δ') ∗ (⟦ Qx ⟧(δ') -∗ ⟦ Px ⟧(δ'))) -∗
      dinv δ Px -∗ dinv δ Qx.
  Proof.
    rewrite dinv_unseal. iIntros "#PQP #accPx !>". iApply Deriv_factor.
    iIntros (??? to). rewrite to !in_js /=. iIntros "W".
    iDestruct ("accPx" with "W") as "[Px cl]".
    iDestruct ("PQP" with "[//] [//] [//] Px") as "[$ QP]". iIntros "Qx".
    iApply "cl". by iApply "QP".
  Qed.
  Lemma dinv_iff {Px Qx} :
    □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Px ⟧(δ') ∗-∗ ⟦ Qx ⟧(δ')) -∗
      dinv δ Px -∗ dinv δ Qx.
  Proof.
    iIntros "#big". iApply dinv_acsr. iIntros "!>" (????).
    iApply (wand_iff_mod_acsr (M:=id)). iModIntro. by iApply "big".
  Qed.

  (** Split [dinv] over [∗] *)
  Local Lemma dinv_sep' {PQx Px Qx} :
    (∀ δ', ⟦ PQx ⟧(δ') ≡ (⟦ Px ⟧(δ') ∗ ⟦ Qx ⟧(δ'))%I) →
    dinv δ PQx ⊢ dinv δ Px.
  Proof.
    iIntros (eq). iApply (dinv_acsr with "[]"). iIntros "!>" (????).
    rewrite eq. iApply (mod_acsr_sep_l (M:=id)).
  Qed.
  Lemma dinv_sep {PQx Px Qx} :
    (∀ δ', ⟦ PQx ⟧(δ') ≡ (⟦ Px ⟧(δ') ∗ ⟦ Qx ⟧(δ'))%I) →
    dinv δ PQx ⊢ dinv δ Px ∗ dinv δ Qx.
  Proof.
    iIntros (eq) "#i". iSplit; [by iApply dinv_sep'|].
    iApply (dinv_sep' with "i"). iIntros (?). by rewrite eq comm.
  Qed.
End dinv_deriv.

(** ** Constructor *)

From nola.iris Require Import cif.

(** [dinvCT]: Constructor for [dinv] *)
Variant dinvCT_id := .
Definition dinvCT :=
  Cifcon dinvCT_id unit (λ _, Empty_set) (λ _, unit) (λ _, unitO) _.
(** [dinvC]: [dinvCT] registered *)
Notation dinvC := (inC dinvCT).

Section dinvC.
  Context `{!dinvC CON} {Σ}.
  (** [cif_dinv]: Formula for [dinv] *)
  Definition cif_dinv (Px : cif CON Σ) : cif CON Σ :=
    cif_in dinvCT () nullary (unary Px) ().
  (** [cif_dinv] is non-expansive *)
  #[export] Instance cif_dinv_ne : NonExpansive (cif_dinv).
  Proof. solve_proper. Qed.
  #[export] Instance cif_dinv_proper : Proper ((≡) ==> (≡)) (cif_dinv).
  Proof. apply ne_proper, _. Qed.
  (** [cif_dinv] is productive *)
  #[export] Instance cif_dinv_productive : Productive (cif_dinv).
  Proof.
    move=> ????. apply cif_in_preserv_productive=>//. by apply fun_proeqv_later.
  Qed.

  Context `{!dinvGS (cifOF CON) Σ, !dinvJ (cifO CON Σ) JUDG}.
  (** Semantics of [dinvCT] *)
  #[export] Program Instance dinvCT_ecsem : Ecsem dinvCT CON JUDG Σ :=
    ECSEM (λ _ δ _ _ Φx _, dinv δ (Φx ())) _.
  Next Obligation. solve_proper. Qed.
End dinvC.
(** [dinvC] semantics registered *)
Notation dinvCS := (inCS dinvCT).

(** Reify [dinv] *)
#[export] Program Instance dinv_as_cif `{!Csem CON JUDG Σ, !dinvC CON}
  `{!dinvGS (cifOF CON) Σ, !dinvJ (cifO CON Σ) JUDG, !dinvCS CON JUDG Σ} {Px} :
  AsCif CON (λ δ, dinv δ Px) := AS_CIF (cif_dinv Px) _.
Next Obligation. move=>/= >. by rewrite sem_cif_in. Qed.
