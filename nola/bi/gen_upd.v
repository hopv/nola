(** * General update *)

From nola Require Export prelude.
From iris.bi Require Export bi.
From iris.proofmode Require Import proofmode.

(** ** [GenUpd]: General update *)

Class GenUpd `{!BiBUpd PROP} (M : PROP → PROP) : Prop := GEN_UPD {
  gen_upd_ne :: NonExpansive M;
  gen_upd_from_bupd {P} : (|==> P) ⊢ M P;
  gen_upd_mono {P Q} : (P ⊢ Q) → M P ⊢ M Q;
  gen_upd_trans {P} : M (M P) ⊢ M P;
  gen_upd_frame_r {P Q} : M P ∗ Q ⊢ M (P ∗ Q);
}.
Hint Mode GenUpd + - ! : typeclass_instances.

(** [bupd] and [fupd] satisfy [GenUpd] *)
#[export] Instance gen_upd_bupd `{!BiBUpd PROP} : GenUpd (PROP:=PROP) bupd.
Proof.
  split=> >. { exact _. } { done. } { by move=> ->. } { iIntros ">$". }
  { by iIntros "[>$$]". }
Qed.
#[export] Instance gen_upd_fupd `{!BiBUpd PROP, !BiFUpd PROP, !BiBUpdFUpd PROP}
  {E} : GenUpd (PROP:=PROP) (fupd E E).
Proof.
  split=> >. { exact _. } { done. } { by move=> ->. } { iIntros ">$". }
  { by iIntros "[>$$]". }
Qed.

Section gen_upd.
  Context `{!BiBUpd PROP, !GenUpd (PROP:=PROP) M}.

  (** Monotonicity *)

  #[export] Instance gen_upd_mono' : Proper ((⊢) ==> (⊢)) M | 10.
  Proof. move=> ??. apply gen_upd_mono. Qed.
  #[export] Instance gen_upd_flip_mono' : Proper (flip (⊢) ==> flip (⊢)) M | 10.
  Proof. move=>/= ??. apply gen_upd_mono. Qed.
  #[export] Instance gen_upd_proper : Proper ((⊣⊢) ==> (⊣⊢)) M | 10.
  Proof. apply ne_proper, _. Qed.

  (** Introduce *)

  Lemma gen_upd_intro {P} : P ⊢ M P.
  Proof. rewrite -gen_upd_from_bupd. by iIntros. Qed.
  #[export] Instance from_modal_gen_upd {P} :
    FromModal True modality_id (M P) (M P) P | 10.
  Proof. move=> _. rewrite /FromModal /=. apply gen_upd_intro. Qed.
  #[export] Instance from_assumption_gen_upd `{!FromAssumption p P Q} :
    KnownRFromAssumption p P (M Q) | 10.
  Proof.
    rewrite /KnownRFromAssumption /FromAssumption from_assumption.
    apply gen_upd_intro.
  Qed.
  #[export] Instance from_pure_gen_upd `{!FromPure a P φ} :
    FromPure a (M P) φ | 10.
  Proof. rewrite /FromPure -(from_pure _ P). apply gen_upd_intro. Qed.
  #[export] Instance elim_modal_gen_upd_from_bupd {p P Q} :
    ElimModal True p false (|==> P) P (M Q) (M Q) | 10.
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim gen_upd_frame_r
      bi.wand_elim_r (gen_upd_from_bupd (M:=M)) gen_upd_trans.
  Qed.

  (** Frame *)

  Lemma gen_upd_frame_l {P Q} : P ∗ M Q ⊢ M (P ∗ Q).
  Proof. by rewrite comm gen_upd_frame_r comm. Qed.
  #[export] Instance frame_gen_upd `{!Frame p R P Q} :
    Frame p R (M P) (M Q) | 10.
  Proof. move: Frame0. rewrite /Frame=> <-. apply gen_upd_frame_l. Qed.

  (** Transitivity *)

  #[export] Instance elim_modal_gen_upd {p P Q} :
    ElimModal True p false (M P) P (M Q) (M Q) | 10.
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim gen_upd_frame_r
      bi.wand_elim_r gen_upd_trans.
  Qed.
  #[export] Instance add_modal_gen_upd {P Q} : AddModal (M P) P (M Q) | 10.
  Proof. by rewrite /AddModal gen_upd_frame_r bi.wand_elim_r gen_upd_trans. Qed.

  (** More instances *)

  #[export] Instance from_sep_gen_upd `{!FromSep P Q Q'} :
    FromSep (M P) (M Q) (M Q') | 10.
  Proof. rewrite /FromSep -(from_sep P). by iIntros "[>$ >$]". Qed.
  #[export] Instance from_or_gen_upd `{!FromOr P Q Q'} :
    FromOr (M P) (M Q) (M Q') | 10.
  Proof.
    rewrite /FromOr -(from_or P). iIntros "[>?|>?] !>"; by [iLeft|iRight].
  Qed.
  #[export] Instance from_exist_gen_upd `{!FromExist (A:=A) P Φ} :
    FromExist (M P) (λ x, M (Φ x)) | 10.
  Proof.
    rewrite /FromExist -(from_exist P). iIntros "[% >?] !>". by iExists _.
  Qed.
  #[export] Instance into_and_gen_upd `{!IntoAnd false P Q R} :
    IntoAnd false (M P) (M Q) (M R) | 10.
  Proof.
    move: IntoAnd0. rewrite /IntoAnd=>/=->. iIntros "∧".
    iSplit; by [iMod "∧" as "[$ _]"|iMod "∧" as "[_ $]"].
  Qed.
  #[export] Instance into_forall_gen_upd `{!IntoForall (A:=A) P Φ} :
    IntoForall (M P) (λ x, M (Φ x)) | 10.
  Proof.
    rewrite /IntoForall (into_forall P). iIntros "Φ %". iMod "Φ". iApply "Φ".
  Qed.
End gen_upd.

(** Adding [◇] inside lets [M] absorb [◇] for introduceable [M] *)
Lemma is_except_0_intro {PROP : bi} {M : PROP → PROP} {P} :
  (∀ P, P ⊢ M P) → IsExcept0 (M (◇ P))%I.
Proof.
  rewrite /IsExcept0 /bi_except_0=> intro. iIntros "[?|$]". iApply intro.
  by iLeft.
Qed.
#[export] Instance is_except_0_gen_upd `{!BiBUpd PROP, !GenUpd (PROP:=PROP) M}
  {P} : IsExcept0 (M (◇ P))%I | 10.
Proof. apply is_except_0_intro. by iIntros. Qed.

(** [◇] preserves [GenUpd] *)
#[export] Instance gen_upd_except_0 `{!BiBUpd PROP, !GenUpd (PROP:=PROP) M} :
  GenUpd (λ P, M (◇ P))%I | 10.
Proof.
  split=> >. { solve_proper. }
  { rewrite (gen_upd_from_bupd (M:=M)). f_equiv. by iIntros. }
  { move=> PQ. by do 2 f_equiv. } { iIntros ">>$". } { by iIntros "[?$]". }
Qed.

Section acsr.
  Context `{!BiBUpd PROP}.

  (** ** [acsr]: Accessor getting [P] from [Q] via the modality [M] *)
  Definition acsr M P Q : PROP := Q -∗ M (P ∗ (P -∗ M Q))%I.

  Context `{!GenUpd (PROP:=PROP) M}.

  (** [acsr] is proper *)
  #[export] Instance acsr_ne : NonExpansive2 (acsr M).
  Proof. solve_proper. Qed.

  (** [acsr] is reflexive and transitive *)
  Lemma acsr_refl {P} : ⊢ acsr M P P.
  Proof. by iIntros "$ !> $". Qed.
  Lemma acsr_trans {P Q R} :
    acsr M P Q -∗ acsr M Q R -∗ acsr M P R.
  Proof.
    iIntros "QPQ RQR R". iMod ("RQR" with "R") as "[Q QR]".
    iMod ("QPQ" with "Q") as "[$ PQ]". iIntros "!> P".
    iMod ("PQ" with "P") as "Q". by iApply "QR".
  Qed.

  (** [acsr] over [∗] *)
  Lemma acsr_sep_l {P Q} : ⊢ acsr M P (P ∗ Q).
  Proof. by iIntros "[$$] !> $". Qed.
  Lemma acsr_sep_r {P Q} : ⊢ acsr M Q (P ∗ Q).
  Proof. by iIntros "[$$] !> $". Qed.

  (** [∗-∗] into [acsr] *)
  Lemma wand_iff_acsr {P Q} : □ (P ∗-∗ Q) ⊢ acsr M P Q.
  Proof.
    iIntros "#[PQ QP] Q". iDestruct ("QP" with "Q") as "$". iIntros "!> ? !>".
    by iApply "PQ".
  Qed.
End acsr.
