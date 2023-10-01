(** * On updates *)

From nola Require Export prelude.
From iris.base_logic Require Import fancy_updates.
From iris.proofmode Require Import proofmode.

(** ** Utility *)

(* [M] can be eliminated under [M'] *)
Notation ElimModalS M M' :=
  (∀ p P Q, ElimModal True p false (M P) P (M' Q) (M' Q)).

(** ** General update *)

Class GenUpd (PROP : bi) (M : PROP → PROP) : Prop := {
  gen_upd_ne :: NonExpansive M;
  gen_upd_intro {P} : P ⊢ M P;
  gen_upd_mono {P Q} : (P ⊢ Q) → M P ⊢ M Q;
  gen_upd_trans {P} : M (M P) ⊢ M P;
  gen_upd_frame_r {P Q} : M P ∗ Q ⊢ M (P ∗ Q);
}.

(** [bupd] and [fupd] satisfy [GenUpd] *)
#[export] Instance gen_upd_bupd `{!BiBUpd PROP} : GenUpd PROP bupd.
Proof.
  split. { apply _. } { by iIntros "%$". } { by move=> ??->. }
  { iIntros "%>$". } { by iIntros "%%[>$$]". }
Qed.
#[export] Instance gen_upd_fupd `{!BiFUpd PROP} {E} : GenUpd PROP (fupd E E).
Proof.
  split. { apply _. } { by iIntros "%$". } { by move=> ??->. }
  { iIntros "%>$". } { by iIntros "%%[>$$]". }
Qed.

Section gen_upd.
  Context `{!GenUpd PROP M}.

  (** Monotonicity *)

  #[export] Instance gen_upd_mono' : Proper ((⊢) ==> (⊢)) M | 10.
  Proof. move=> ??. apply gen_upd_mono. Qed.
  #[export] Instance gen_upd_flip_mono' : Proper (flip (⊢) ==> flip (⊢)) M | 10.
  Proof. move=>/= ??. apply gen_upd_mono. Qed.
  #[export] Instance gen_upd_proper : Proper ((⊣⊢) ==> (⊣⊢)) M | 10.
  Proof. apply ne_proper, _. Qed.

  (** Introduce *)

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

  (** Frame *)

  Lemma gen_upd_frame_l {P Q} : P ∗ M Q ⊢ M (P ∗ Q).
  Proof. by rewrite comm gen_upd_frame_r comm. Qed.
  #[export] Instance frame_gen_upd {p R P Q} :
    Frame p R P Q → Frame p R (M P) (M Q) | 10.
  Proof. rewrite /Frame=> <-. apply gen_upd_frame_l. Qed.

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

(** ** Update with a custom world satisfaction [W] *)

(** Basic update with a world satisfaction *)
Definition bupdw `{!BiBUpd PROP} (W P : PROP) : PROP := W ==∗ W ∗ P.
Arguments bupdw : simpl never.

(** Fancy update with a world satisfaction *)
Definition fupdw `{!BiFUpd PROP} (E E' : coPset) (W P : PROP) : PROP :=
  W ={E,E'}=∗ W ∗ P.
Arguments fupdw : simpl never.

(** Notation *)

Notation "|=[ W ] => P" := (bupdw W P)
  (at level 99, P at level 200, format "'[  ' |=[ W ] =>  '/' P ']'")
  : bi_scope.
Notation "P =[ W ]=∗ Q" := (P -∗ |=[W]=> Q)%I
  (at level 99, Q at level 200, format "'[' P  =[ W ]=∗  '/' '[' Q ']' ']'")
  : bi_scope.
Notation "P =[ W ]=∗ Q" := (P -∗ |=[W]=> Q) : stdpp_scope.

Notation "|=[ W ] { E , E' }=> P" := (fupdw E E' W P)
  (at level 99, P at level 200,
    format "'[  ' |=[ W ] '/' { E , E' }=>  '/' P ']'") : bi_scope.
Notation "|=[ W ] { E }=> P" := (fupdw E E W P)
  (at level 99, P at level 200, format "'[  ' |=[ W ] '/' { E }=>  '/' P ']'")
  : bi_scope.
Notation "P =[ W ] { E , E' }=∗ Q" := (P -∗ |=[W]{E,E'}=> Q)%I
  (at level 99, Q at level 200,
    format "'[' P  =[ W ] '/' { E , E' }=∗  '/' '[' Q ']' ']'") : bi_scope.
Notation "P =[ W ] { E , E' }=∗ Q" := (P -∗ |=[W]{E,E'}=> Q) : stdpp_scope.
Notation "P =[ W ] { E }=∗ Q" := (P -∗ |=[W]{E}=> Q)%I
  (at level 99, Q at level 200,
    format "'[' P  =[ W ] '/' { E }=∗  '/' '[' Q ']' ']'") : bi_scope.
Notation "P =[ W ] { E }=∗ Q" := (P -∗ |=[W]{E}=> Q) : stdpp_scope.

(** We move the position of [▷] to make the notation work *)
Notation "|=[ W ] { E }▷[ E' ] => P" := (|=[W]{E,E'}=> ▷ |=[W]{E',E}=> P)%I
  (at level 99, P at level 200,
    format "'[  ' |=[ W ] '/' { E }▷[ E' ] =>  '/' P ']'") : bi_scope.
Notation "|=[ W ] { E }▷=> P" := (|=[W]{E}=> ▷ |=[W]{E}=> P)%I
  (at level 99, P at level 200,
    format "'[  ' |=[ W ] '/' { E }▷=>  '/' P ']'") : bi_scope.
Notation "|=[ W ] { E }▷[ E' ] =>^ n P" :=
  (Nat.iter n (λ Q, |=[W]{E}▷[E'] => Q) P)%I
  (at level 99, P at level 200, n at level 9,
    format "'[  ' |=[ W ] '/' { E }▷[ E' ] =>^ n  '/' P ']'") : bi_scope.
Notation "|=[ W ] { E }▷=>^ n P" :=
  (Nat.iter n (λ Q, |=[W]{E}▷=> Q) P)%I
  (at level 99, P at level 200, n at level 9,
    format "'[  ' |=[ W ] '/' { E }▷=>^ n  '/' P ']'") : bi_scope.

(** ** Lemmas *)
Section lemmas.
  Context {PROP : bi}.
  Implicit Type W P Q R : PROP.

  (** [step_fupdN] is non-expansive *)
  Lemma step_fupdN_ne `{!BiFUpd PROP} {n E E' k P Q} :
    P ≡{n}≡ Q → (|={E}[E']▷=>^k P)%I ≡{n}≡ (|={E}[E']▷=>^k Q)%I.
  Proof. move=> PQ. by elim k; [done|]=>/= ? ->. Qed.
  Lemma step_fupdN_proper `{!BiFUpd PROP} {E E' k P Q} :
    P ⊣⊢ Q → (|={E}[E']▷=>^k P) ⊣⊢ |={E}[E']▷=>^k Q.
  Proof.
    move=> PQ. apply equiv_dist=> n. apply step_fupdN_ne. by rewrite PQ.
  Qed.

  (** [bupdw] is non-expansive *)
  #[export] Instance bupdw_ne `{!BiBUpd PROP} :
    NonExpansive2 (bupdw (PROP:=PROP)).
  Proof. solve_proper. Qed.
  #[export] Instance bupdw_proper `{!BiBUpd PROP} :
    Proper ((⊣⊢) ==> (⊣⊢) ==> (⊣⊢)) (bupdw (PROP:=PROP)).
  Proof. solve_proper. Qed.

  (** [fupdw] is non-expansive *)
  #[export] Instance fupdw_ne `{!BiFUpd PROP} {E E'} :
    NonExpansive2 (fupdw (PROP:=PROP) E E').
  Proof. solve_proper. Qed.
  #[export] Instance fupdw_proper `{!BiFUpd PROP} :
    Proper ((=) ==> (=) ==> (⊣⊢) ==> (⊣⊢) ==> (⊣⊢)) (fupdw (PROP:=PROP)).
  Proof. solve_proper. Qed.

  (** [fupdw] absorbs [◇] *)
  #[export] Instance is_except_0_fupdw `{!BiFUpd PROP} {E E' W P} :
    IsExcept0 (|=[W]{E,E'}=> P).
  Proof. rewrite /IsExcept0. by iIntros ">?". Qed.

  (** [bupdw] is monotone *)
  Lemma bupdw_mono `{!BiBUpd PROP} {W P Q} : (P ⊢ Q) → (|=[W]=> P) ⊢ |=[W]=> Q.
  Proof. by rewrite /bupdw=> ->. Qed.
  #[export] Instance bupdw_mono' `{!BiBUpd PROP} {W} :
    Proper ((⊢) ==> (⊢)) (bupdw (PROP:=PROP) W).
  Proof. move=> ??. apply bupdw_mono. Qed.
  #[export] Instance bupdw_flip_mono' `{!BiBUpd PROP} {W} :
    Proper (flip (⊢) ==> flip (⊢)) (bupdw (PROP:=PROP) W).
  Proof. move=>/= ??. apply bupdw_mono. Qed.

  (** [fupdw] is monotone *)
  Lemma fupdw_mono `{!BiFUpd PROP} {E E' W P Q} :
    (P ⊢ Q) → (|=[W]{E,E'}=> P) ⊢ |=[W]{E,E'}=> Q.
  Proof. by rewrite /fupdw=> ->. Qed.
  #[export] Instance fupdw_mono' `{!BiFUpd PROP} {E E' W} :
    Proper ((⊢) ==> (⊢)) (fupdw (PROP:=PROP) E E' W).
  Proof. move=> ??. apply fupdw_mono. Qed.
  #[export] Instance fupdw_flip_mono' `{!BiFUpd PROP} {E E' W} :
    Proper (flip (⊢) ==> flip (⊢)) (fupdw (PROP:=PROP) E E' W).
  Proof. move=>/= ??. apply fupdw_mono. Qed.

  (** Introduce [bupdw] *)
  Lemma bupdw_intro `{!BiBUpd PROP} {W P} : P ⊢ |=[W]=> P.
  Proof. by iIntros "$$". Qed.
  #[export] Instance from_modal_bupdw `{!BiBUpd PROP} {W P} :
    FromModal True modality_id (|=[W]=> P) (|=[W]=> P) P.
  Proof. by rewrite /FromModal /= -bupdw_intro. Qed.
  #[export] Instance from_assumption_bupdw
    `{!BiBUpd PROP, !FromAssumption p P Q} {W} :
    KnownRFromAssumption p P (|=[W]=> Q).
  Proof.
    rewrite /KnownRFromAssumption /FromAssumption from_assumption.
    apply bupdw_intro.
  Qed.
  #[export] Instance from_pure_bupdw `{!BiBUpd PROP, !FromPure a P φ} {W} :
    FromPure a (|=[W]=> P) φ.
  Proof. rewrite /FromPure -(from_pure _ P). apply bupdw_intro. Qed.

  (** Introduce [fupdw] *)
  Lemma fupdw_intro `{!BiFUpd PROP} {E W P} : P ⊢ |=[W]{E}=> P.
  Proof. by iIntros "$$". Qed.
  #[export] Instance from_modal_fupdw `{!BiFUpd PROP} {E W P} :
    FromModal True modality_id (|=[W]{E}=> P) (|=[W]{E}=> P) P.
  Proof. by rewrite /FromModal /= -fupdw_intro. Qed.
  #[export] Instance from_modal_fupdw_wrong_mask `{!BiFUpd PROP} {E E' W P} :
    FromModal
      (pm_error "Only non-mask-changing update modalities can be introduced directly.
Use [iApply fupd_mask_intro] to introduce mask-changing update modalities")
      modality_id (|=[W]{E,E'}=> P) (|=[W]{E,E'}=> P) P | 100.
  Proof. by intros []. Qed.
  Lemma bupdw_fupdw `{!BiBUpd PROP, !BiFUpd PROP, !BiBUpdFUpd PROP} E {W P} :
    (|=[W]=> P) ⊢ |=[W]{E}=> P.
  Proof. apply bi.wand_mono; by [|rewrite bupd_fupd]. Qed.
  #[export] Instance from_assumption_fupdw
    `{!BiFUpd PROP, !FromAssumption p P Q} {E W} :
    KnownRFromAssumption p P (|=[W]{E}=> Q).
  Proof.
    rewrite /KnownRFromAssumption /FromAssumption from_assumption.
    apply fupdw_intro.
  Qed.
  #[export] Instance from_pure_fupdw `{!BiFUpd PROP, !FromPure a P φ} {E W} :
    FromPure a (|=[W]{E}=> P) φ.
  Proof. rewrite /FromPure -(from_pure _ P). apply fupdw_intro. Qed.
  Lemma fupdw_mask_intro `{!BiFUpd PROP} {E E' W P} : E' ⊆ E →
    ((|={E',E}=> emp) -∗ P) ⊢ |=[W]{E,E'}=> P.
  Proof. iIntros (?) "? $". by iApply fupd_mask_intro. Qed.

  (** Frame on [bupdw] *)
  #[export] Instance frame_bupdw `{!BiBUpd PROP} {p R P Q W} :
    Frame p R P Q → Frame p R (|=[W]=> P) (|=[W]=> Q) | 2.
  Proof. exact _. Qed.
  Lemma bupdw_frame_r `{!BiBUpd PROP} {W P Q} : (|=[W]=> P) ∗ Q ⊢ |=[W]=> P ∗ Q.
  Proof. by iIntros "[? $]". Qed.

  (** Frame on [fupdw] *)
  #[export] Instance frame_fupdw `{!BiFUpd PROP} {p R P Q E E' W} :
    Frame p R P Q → Frame p R (|=[W]{E,E'}=> P) (|=[W]{E,E'}=> Q) | 2.
  Proof. exact _. Qed.
  Lemma fupdw_frame_r `{!BiFUpd PROP} {E E' W P Q} :
    (|=[W]{E,E'}=> P) ∗ Q ⊢ |=[W]{E,E'}=> P ∗ Q.
  Proof. by iIntros "[? $]". Qed.

  (** Compose [bupdw] *)
  Lemma bupdw_trans `{!BiBUpd PROP} {W P} : (|=[W]=> |=[W]=> P) ⊢ |=[W]=> P.
  Proof.
    iIntros "WWP W". iMod ("WWP" with "W") as "[W WP]". iApply ("WP" with "W").
  Qed.
  #[export] Instance elim_modal_bupdw `{!BiBUpd PROP} {p W P Q} :
    ElimModal True p false (|=[W]=> P) P (|=[W]=> Q) (|=[W]=> Q).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim bupdw_frame_r
      bi.wand_elim_r bupdw_trans.
  Qed.
  #[export] Instance elim_modal_bupd_bupdw `{!BiBUpd PROP} {p W P Q} :
    ElimModal True p false (|==> P) P (|=[W]=> Q) (|=[W]=> Q).
  Proof. exact _. Qed.
  #[export] Instance add_modal_bupdw `{!BiBUpd PROP} {W P Q} :
    AddModal (|=[W]=> P) P (|=[W]=> Q).
  Proof. by rewrite /AddModal bupdw_frame_r bi.wand_elim_r bupdw_trans. Qed.

  (** Compose [fupdw] *)
  Lemma fupdw_trans `{!BiFUpd PROP} {E E' E'' W P} :
    (|=[W]{E,E'}=> |=[W]{E',E''}=> P) ⊢ |=[W]{E,E''}=> P.
  Proof.
    iIntros "WWP W". iMod ("WWP" with "W") as "[W WP]". iApply ("WP" with "W").
  Qed.
  #[export] Instance elim_modal_fupdw_fupdw `{!BiFUpd PROP} {p E E' E'' W P Q} :
    ElimModal True p false (|=[W]{E,E'}=> P) P
      (|=[W]{E,E''}=> Q) (|=[W]{E',E''}=> Q).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim fupdw_frame_r
      bi.wand_elim_r fupdw_trans.
  Qed.
  #[export] Instance elim_modal_bupdw_fupdw
    `{!BiBUpd PROP, !BiFUpd PROP, !BiBUpdFUpd PROP} {p E E' W P Q} :
    ElimModal True p false (|=[W]=> P) P (|=[W]{E,E'}=> Q) (|=[W]{E,E'}=> Q)
    | 10.
  Proof. move=> ?. by rewrite (bupdw_fupdw E) elim_modal_fupdw_fupdw. Qed.
  #[export] Instance elim_modal_fupd_fupdw `{!BiFUpd PROP} {p E E' E'' W P Q} :
    ElimModal True p false (|={E,E'}=> P) P
      (|=[W]{E,E''}=> Q) (|=[W]{E',E''}=> Q).
  Proof. exact _. Qed.
  #[export] Instance elim_modal_bupd_fupdw
    `{!BiBUpd PROP, !BiFUpd PROP, !BiBUpdFUpd PROP} {p E E' W P Q} :
    ElimModal True p false (|==> P) P (|=[W]{E,E'}=> Q) (|=[W]{E,E'}=> Q) | 10.
  Proof. exact _. Qed.
  #[export] Instance elim_modal_fupdw_fupdw_wrong_mask
    `{!BiFUpd PROP} {p E E' E'' E''' P Q W} :
    ElimModal
      (pm_error "Goal and eliminated modality must have the same mask.
Use [iMod (fupd_mask_subseteq E')] to adjust the mask of your goal to [E']")
      p false (|=[W]{E,E'}=> P) False (|=[W]{E'',E'''}=> Q) False | 100.
  Proof. intros []. Qed.
  #[export] Instance add_modal_fupdw `{!BiFUpd PROP} {E E' W P Q} :
    AddModal (|=[W]{E}=> P) P (|=[W]{E,E'}=> Q).
  Proof. by rewrite /AddModal fupdw_frame_r bi.wand_elim_r fupdw_trans. Qed.
  #[export] Instance add_modal_fupd_fupdw `{!BiFUpd PROP} {E E' W P Q} :
    AddModal (|={E}=> P) P (|=[W]{E,E'}=> Q).
  Proof. rewrite /AddModal fupd_frame_r bi.wand_elim_r. iIntros ">$". Qed.

  (** More instances for [bupdw] *)
  #[export] Instance from_sep_bupdw `{!BiBUpd PROP, !FromSep P Q Q'} {W} :
    FromSep (|=[W]=> P) (|=[W]=> Q) (|=[W]=> Q').
  Proof. rewrite /FromSep -(from_sep P). by iIntros "[>$ >$]". Qed.
  #[export] Instance from_or_bupdw `{!BiBUpd PROP, !FromOr P Q Q'} {W} :
    FromOr (|=[W]=> P) (|=[W]=> Q) (|=[W]=> Q').
  Proof.
    rewrite /FromOr -(from_or P). iIntros "[>?|>?] !>"; by [iLeft|iRight].
  Qed.
  #[export] Instance from_exist_bupdw `{!BiBUpd PROP, !FromExist (A:=A) P Φ}
    {W} : FromExist (|=[W]=> P) (λ x, |=[W]=> (Φ x))%I.
  Proof.
    rewrite /FromExist -(from_exist P). iIntros "[% >?] !>". by iExists _.
  Qed.
  #[export] Instance into_and_bupdw `{!BiBUpd PROP, !IntoAnd false P Q R} {W} :
    IntoAnd false (|=[W]=> P) (|=[W]=> Q) (|=[W]=> R).
  Proof.
    move: IntoAnd0. rewrite /IntoAnd=>/=->. iIntros "∧".
    iSplit; by [iMod "∧" as "[$ _]"|iMod "∧" as "[_ $]"].
  Qed.
  #[export] Instance into_forall_bupdw `{!BiBUpd PROP, !IntoForall (A:=A) P Φ}
    {W} : IntoForall (|=[W]=> P) (λ x, |=[W]=> (Φ x))%I.
  Proof.
    rewrite /IntoForall (into_forall P). iIntros "Φ %". iMod "Φ". iApply "Φ".
  Qed.

  (** More instances for [fupdw] *)
  #[export] Instance from_sep_fupdw `{!BiFUpd PROP, !FromSep P Q Q'} {E W} :
    FromSep (|=[W]{E}=> P) (|=[W]{E}=> Q) (|=[W]{E}=> Q').
  Proof. rewrite /FromSep -(from_sep P). by iIntros "[>$ >$]". Qed.
  #[export] Instance from_or_fupdw `{!BiFUpd PROP, !FromOr P Q Q'} {E W} :
    FromOr (|=[W]{E}=> P) (|=[W]{E}=> Q) (|=[W]{E}=> Q').
  Proof.
    rewrite /FromOr -(from_or P). iIntros "[>?|>?] !>"; by [iLeft|iRight].
  Qed.
  #[export] Instance from_exist_fupdw `{!BiFUpd PROP, !FromExist (A:=A) P Φ}
    {E E' W} : FromExist (|=[W]{E,E'}=> P) (λ x, |=[W]{E,E'}=> (Φ x))%I.
  Proof.
    rewrite /FromExist -(from_exist P). iIntros "[% >?] !>". by iExists _.
  Qed.
  #[export] Instance into_and_fupdw
    `{!BiFUpd PROP, !IntoAnd false P Q R} {E E' W} :
    IntoAnd false (|=[W]{E,E'}=> P) (|=[W]{E,E'}=> Q) (|=[W]{E,E'}=> R).
  Proof.
    move: IntoAnd0. rewrite /IntoAnd=>/=->. iIntros "∧".
    iSplit; by [iMod "∧" as "[$ _]"|iMod "∧" as "[_ $]"].
  Qed.
  #[export] Instance into_forall_fupdw
    `{!BiFUpd PROP, !IntoForall (A:=A) P Φ} {E E' W} :
    IntoForall (|=[W]{E,E'}=> P) (λ x, |=[W]{E,E'}=> (Φ x))%I.
  Proof.
    rewrite /IntoForall (into_forall P). iIntros "Φ %". iMod "Φ". iApply "Φ".
  Qed.
  #[export] Instance elim_acc_fupdw `{!BiFUpd PROP} {X E E' E'' W α β γ P} :
    ElimAcc (X:=X) True (fupd E E') (fupd E' E) α β γ (|=[W]{E,E''}=> P)
      (λ x, |=[W]{E'}=> β x ∗ (γ x -∗? |=[W]{E,E''}=> P))%I | 10.
  Proof.
    iIntros (_) "→P ∝ W". iMod "∝" as (x) "[α β→]".
    iMod ("→P" with "α W") as "[W[β γ→]]".
    iMod ("β→" with "β") as "γ". by iApply ("γ→" with "γ").
  Qed.

  (** [bupdw] and [fupdw] satisfy [GenUpd] *)
  #[export] Instance gen_upd_bupdw `{!BiBUpd PROP} {W} : GenUpd PROP (bupdw W).
  Proof.
    split. { apply _. } { by iIntros "%$". } { by move=> ??->. }
    { iIntros "%>$". } { by iIntros "%%[>$$]". }
  Qed.
  #[export] Instance gen_upd_fupdw `{!BiFUpd PROP} {E W} :
    GenUpd PROP (fupdw E E W).
  Proof.
    split. { apply _. } { by iIntros "%$". } { by move=> ??->. }
    { iIntros "%>$". } { by iIntros "%%[>$$]". }
  Qed.

  (** Expand the world satisfaction of [bupdw] *)
  Lemma bupdw_expand_bupd `{!BiBUpd PROP} {W W' P} :
    (W' ==∗ W ∗ (W ==∗ W')) -∗ (|=[W]=> P) =[W']=∗ P.
  Proof.
    iIntros "W'W WP W'". iMod ("W'W" with "W'") as "[W WW']".
    iMod ("WP" with "W") as "[W $]". by iApply "WW'".
  Qed.
  Lemma bupdw_expand `{!BiBUpd PROP} {W W' P} :
    (W' -∗ W ∗ (W -∗ W')) -∗ (|=[W]=> P) =[W']=∗ P.
  Proof.
    iIntros "W'W WP W'". iDestruct ("W'W" with "W'") as "[W WW']".
    iMod ("WP" with "W") as "[W $]". by iApply "WW'".
  Qed.

  (** Expand the world satisfaction of [fupdw] *)
  Lemma fupdw_expand_fupd `{!BiFUpd PROP} {W W' E E' P} :
    (W' ={E}=∗ W ∗ (W ={E'}=∗ W')) -∗ (|=[W]{E,E'}=> P) =[W']{E,E'}=∗ P.
  Proof.
    iIntros "W'W WP W'". iMod ("W'W" with "W'") as "[W WW']".
    iMod ("WP" with "W") as "[W $]". by iApply "WW'".
  Qed.
  Lemma fupdw_expand `{!BiFUpd PROP} {W W' E E' P} :
    (W' -∗ W ∗ (W -∗ W')) -∗ (|=[W]{E,E'}=> P) =[W']{E,E'}=∗ P.
  Proof.
    iIntros "W'W WP W'". iDestruct ("W'W" with "W'") as "[W WW']".
    iMod ("WP" with "W") as "[W $]". iApply "WW'". by iModIntro.
  Qed.

  (** Turn [step_fupdwN] into [step_fupdN]

    Combining this with adequacy lemmas for [step_fupdN],
    one can prove adequacy lemmas for [step_fupdwN]. *)
  Lemma step_fupdwN_step_fupdN `{!BiFUpd PROP} {W n E E' P} :
    (|=[W]{E}▷[E']=>^n P) ⊢ W -∗ |={E}[E']▷=>^n W ∗ P.
  Proof.
    elim: n=>/=; [by iIntros; iFrame|]=> n ->.
    iIntros "big W". iMod ("big" with "W") as "[W big]". iModIntro. iNext.
    iMod ("big" with "W") as "[W big]". iModIntro. by iApply "big".
  Qed.
End lemmas.
