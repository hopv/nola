(** * Judgments *)

From nola.util Require Import tagged.
From nola.bi Require Export deriv modw.
From iris.proofmode Require Import proofmode.
Import ModwNotation DsemNotation.

Implicit Type (FM : ofe) (PROP : bi).

(** ** [bupdJT]: Judgment type for a magic wand under the basic update *)
Variant bupdJT_id FM := .
Definition bupdJT (FM : ofe) : ofe :=
  tagged (bupdJT_id FM) (FM * FM).
(** [bupdJ]: [bupdJT] registered *)
Notation bupdJ FM JUDG := (inJ (bupdJT FM) JUDG).

Section bupdJ.
  Context `{bupd_j : !bupdJ FM JUDG}.

  (** [jbupd]: Judgment *)
  Definition jbupd Px Qx : JUDG := bupd_j (Tagged (Px, Qx)).
  (** [jbupd] is non-expansive *)
  #[export] Instance jbupd_ne : NonExpansive2 jbupd.
  Proof. solve_proper. Qed.

  Context `{!Dsem JUDG FM PROP, !BiBUpd PROP}.
  Implicit Type δ : JUDG -n> PROP.

  (** [bupdJT_sem]: Semantics of [bupdJT] *)
  Definition bupdJT_sem δ (J : bupdJT FM) : PROP :=
    ⟦ J.(untag).1 ⟧(δ) ==∗ ⟦ J.(untag).2 ⟧(δ).
  (** [bupdJT_sem] is non-expansive *)
  #[export] Instance bupdJT_sem_ne {δ} : NonExpansive (bupdJT_sem δ).
  Proof. solve_proper. Qed.
  (** [Dsem] over [bupdJT] *)
  #[export] Instance bupdJT_dsem : Dsem JUDG (bupdJT FM) PROP :=
    DSEM bupdJT_sem _.
End bupdJ.
(** [bupdJS]: Semantics of [bupdJT] registered *)
Notation bupdJS FM := (inJS (bupdJT FM)).

Section bupdJ.
  Context `{!bupdJ FM JUDG, !BiBUpd PROP, !Dsem JUDG FM PROP,
    !Jsem JUDG PROP, !bupdJS FM JUDG PROP, !Deriv (JUDG:=JUDG) ih δ}.

  (** Lemmas for [jbupd] *)
  Lemma jbupd_refl {Px} : ⊢ δ (jbupd Px Px).
  Proof.
    iApply Deriv_factor. iIntros (????). rewrite in_js. by iIntros "$".
  Qed.
  Lemma jbupd_trans {Px Qx Rx} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Px ⟧(δ') ==∗ ⟦ Qx ⟧(δ')) -∗
    δ (jbupd Qx Rx) -∗ δ (jbupd Px Rx).
  Proof.
    iIntros "big". iApply Deriv_map. iIntros (????). rewrite !in_js.
    iIntros "QR Px". iMod ("big" with "[//] [//] [//] Px"). by iApply "QR".
  Qed.
  Lemma jbupd_trans' {Px Qx Rx} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ → ⟦ Qx ⟧(δ') ==∗ ⟦ Rx ⟧(δ'))
      -∗ δ (jbupd Px Qx) -∗ δ (jbupd Px Rx).
  Proof.
    iIntros "big". iApply Deriv_map. iIntros (????). rewrite !in_js.
    iIntros "PQ Px". iMod ("PQ" with "Px"). by iApply "big".
  Qed.
  Lemma der_jbupd {Px Qx} : der (jbupd Px Qx) ⊢ (⟦ Px ⟧ ==∗ ⟦ Qx ⟧).
  Proof. by rewrite der_sound in_js. Qed.
End bupdJ.

