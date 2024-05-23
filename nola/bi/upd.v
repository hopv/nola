(** * On updates *)

From nola Require Export prelude.
From iris.base_logic.lib Require Export fancy_updates.
From iris.proofmode Require Import proofmode.

(** ** On [step_fupdN] *)

(** [step_fupdN] is non-expansive *)
Lemma step_fupdN_ne `{!BiFUpd PROP} {n E E' k} {P Q : PROP} :
  P ≡{n}≡ Q → (|={E}[E']▷=>^k P)%I ≡{n}≡ (|={E}[E']▷=>^k Q)%I.
Proof. move=> PQ. by elim k; [done|]=>/= ? ->. Qed.
Lemma step_fupdN_proper `{!BiFUpd PROP} {E E' k} {P Q : PROP} :
  P ⊣⊢ Q → (|={E}[E']▷=>^k P) ⊣⊢ |={E}[E']▷=>^k Q.
Proof.
  move=> PQ. apply equiv_dist=> n. apply step_fupdN_ne. by rewrite PQ.
Qed.

(** ** General update *)

Class GenUpd `{!BiBUpd PROP} (M : PROP → PROP) : Prop := GEN_UPD {
  gen_upd_ne :: NonExpansive M;
  gen_upd_from_bupd {P} : (|==> P) ⊢ M P;
  gen_upd_mono {P Q} : (P ⊢ Q) → M P ⊢ M Q;
  gen_upd_trans {P} : M (M P) ⊢ M P;
  gen_upd_frame_r {P Q} : M P ∗ Q ⊢ M (P ∗ Q);
}.

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
      bi.wand_elim_r gen_upd_from_bupd gen_upd_trans.
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
  { rewrite gen_upd_from_bupd. f_equiv. by iIntros. }
  { move=> PQ. by do 2 f_equiv. } { iIntros ">>$". } { by iIntros "[?$]". }
Qed.

(** ** World satisfaction inclusion *)

Class WsatIncl {PROP : bi} (W W' Wr : PROP) : Prop :=
  wsat_incl : W ⊣⊢ W' ∗ Wr.
Arguments WsatIncl {_} _%_I _%_I _%_I : simpl never.
Arguments wsat_incl {_} _%_I _%_I _%_I {_}.
Hint Mode WsatIncl + ! ! - : typeclass_instances.

Section wsat_incl.
  Context {PROP : bi}.
  Implicit Types W Wr : PROP.

  #[export] Instance wsat_incl_refl {W} : WsatIncl W W emp.
  Proof. by rewrite /WsatIncl right_id. Qed.
  #[export] Instance wsat_incl_emp {W} : WsatIncl W emp W.
  Proof. by rewrite /WsatIncl left_id. Qed.
  #[export] Instance wsat_incl_True `{!BiAffine PROP} {W} : WsatIncl W True W.
  Proof. by rewrite /WsatIncl bi.True_sep. Qed.
  #[export] Instance wsat_incl_sep_in {W W'1 W'2 Wr Wr'} :
    WsatIncl W W'1 Wr → WsatIncl Wr W'2 Wr' → WsatIncl W (W'1 ∗ W'2) Wr' | 2.
  Proof. rewrite /WsatIncl=> ->->. by rewrite assoc. Qed.
  #[export] Instance wsat_incl_in_sep_l {W1 W2 W' Wr} :
    WsatIncl W1 W' Wr → WsatIncl (W1 ∗ W2) W' (Wr ∗ W2) | 4.
  Proof. rewrite /WsatIncl=> ->. by rewrite assoc. Qed.
  #[export] Instance wsat_incl_in_sep_r {W1 W2 W' Wr} :
    WsatIncl W2 W' Wr → WsatIncl (W1 ∗ W2) W' (W1 ∗ Wr) | 6.
  Proof. rewrite /WsatIncl=> ->. rewrite !assoc. f_equiv. by rewrite comm. Qed.
End wsat_incl.

(** ** Modality with a world satisfaction *)

Definition modw {PROP : bi} (M : PROP → PROP) (W P : PROP) : PROP :=
  W -∗ M (W ∗ P)%I.
Arguments modw : simpl never.

(** *** Lemmas *)
Section lemmas.
  Context {PROP : bi}.
  Implicit Type (M : PROP → PROP) (W P Q R : PROP).

  (** Fold the definition of [modw] *)
  Lemma modw_fold M W P : (W -∗ M (W ∗ P)) ⊣⊢ modw M W P.
  Proof. done. Qed.

  (** [modw] is non-expansive and proper *)
  #[export] Instance modw_ne `{!NonExpansive M} : NonExpansive2 (modw M) | 10.
  Proof. solve_proper. Qed.
  #[export] Instance modw_proper `{!Proper ((⊣⊢) ==> (⊣⊢)) M} :
    Proper ((⊣⊢) ==> (⊣⊢) ==> (⊣⊢)) (modw M) | 10.
  Proof. solve_proper. Qed.
  Lemma modw_ne_mod {n M M' W P} :
    (∀ P, M P ≡{n}≡ M' P) → modw M W P ≡{n}≡ modw M' W P.
  Proof. by unfold modw=> ->. Qed.
  Lemma modw_proper_mod {M M' W P} :
    (∀ P, M P ≡ M' P) → modw M W P ≡ modw M' W P.
  Proof.
    move=> ?. apply equiv_dist=> ?. apply modw_ne_mod=> ?. by apply equiv_dist.
  Qed.

  (** [modw] is monotone for monotone [M] *)
  #[export] Instance modw_mono `{!Proper ((⊢) ==> (⊢)) M} {W} :
    Proper ((⊢) ==> (⊢)) (modw M W) | 10.
  Proof. solve_proper. Qed.
  #[export] Instance modw_mono' `{!Proper ((⊢) ==> (⊢)) M} {W} :
    Proper (flip (⊢) ==> flip (⊢)) (modw M W) | 10.
  Proof. solve_proper. Qed.

  (** Modify the world satisfaction of [modw] for framing [M] *)
  Lemma modw_incl `{!Proper ((⊣⊢) ==> (⊣⊢)) M} {P} `(!WsatIncl W W' Wr) :
    (∀ P Q, M P ∗ Q ⊢ M (P ∗ Q)) → modw M W' P ⊢ modw M W P.
  Proof.
    rewrite (wsat_incl W W')=> fr. iIntros "→P [W' Wr]".
    iDestruct ("→P" with "W'") as "→P". rewrite -assoc [(Wr ∗ _)%I]comm assoc.
    iApply fr. iFrame.
  Qed.
  Lemma modw_incl_gen_upd `{!BiBUpd PROP, !GenUpd M} {P} `(!WsatIncl W W' Wr) :
    modw M W' P ⊢ modw M W P.
  Proof. apply (modw_incl WsatIncl0)=> *. exact gen_upd_frame_r. Qed.

  (** [modw] preserves [IsExcept0] *)
  #[export] Instance is_except_0_modw `{!∀ P, IsExcept0 (M P)} {W P} :
    IsExcept0 (modw M W P) | 10.
  Proof. unfold IsExcept0. by iIntros ">?". Qed.

  (** Introduce [modw] *)
  Lemma modw_intro {M W P} : (∀ P, P ⊢ M P) → P ⊢ modw M W P.
  Proof. iIntros (toM) "??". iApply toM. iFrame. Qed.
  Lemma from_modal_modw {M W P} :
    (∀ P, P ⊢ M P) → FromModal True modality_id (modw M W P) (modw M W P) P.
  Proof. rewrite /FromModal=> ? _. by apply modw_intro. Qed.
  Lemma from_assumption_modw {M W} `{!FromAssumption p P Q} :
    (∀ P, P ⊢ M P) → KnownRFromAssumption p P (modw M W Q).
  Proof.
    move: FromAssumption0. rewrite /KnownRFromAssumption /FromAssumption=> -> ?.
    by apply modw_intro.
  Qed.
  Lemma from_pure_modw {M W} `{!FromPure a P φ} :
    (∀ P, P ⊢ M P) → FromPure a (modw M W P) φ.
  Proof. move: FromPure0. rewrite /FromPure=> -> ?. by apply modw_intro. Qed.

  (** Compose [modw]s composing the modalities *)
  Lemma modw_compose `{!Proper ((⊢) ==> (⊢)) M} {M' M'' W P} :
    (∀ P, M (M' P) ⊢ M'' P) → modw M W (modw M' W P) ⊢ modw M'' W P.
  Proof.
    iIntros (toM'') "→P W". iDestruct ("→P" with "W") as "→P". iApply toM''.
    iStopProof. f_equiv. iIntros "[W →P]". by iApply "→P".
  Qed.

  (** [modw] frames for framing [M] *)
  Lemma modw_frame_r `{!Proper ((⊣⊢) ==> (⊣⊢)) M} {W P Q} :
    (∀ P Q, M P ∗ Q ⊢ M (P ∗ Q)) → modw M W P ∗ Q ⊢ modw M W (P ∗ Q).
  Proof.
    iIntros (fr) "[→P Q] W". iDestruct ("→P" with "W") as "→P". rewrite assoc.
    iApply fr. iFrame.
  Qed.
  Lemma modw_frame_l `{!Proper ((⊣⊢) ==> (⊣⊢)) M} {W P Q} :
    (∀ P Q, M P ∗ Q ⊢ M (P ∗ Q)) → Q ∗ modw M W P ⊢ modw M W (Q ∗ P).
  Proof. rewrite !(comm _ Q). apply modw_frame_r. Qed.

  (** [modw] preserves [GenUpd] *)
  #[export] Instance gen_upd_modw `{!BiBUpd PROP, !GenUpd M} {W} :
    GenUpd (modw M W) | 10.
  Proof.
    split=> >. { exact _. } { by iIntros ">$$". } { by move=> ->. }
    { apply modw_compose=> ?. exact gen_upd_trans. }
    { apply modw_frame_r=> *. exact gen_upd_frame_r. }
  Qed.

  (** Compose [modw]s accumulating the world satisfaction *)
  Lemma modw_modw_sep `{!Proper ((⊣⊢) ==> (⊣⊢)) M} {W W' P} :
    modw (modw M W) W' P ⊣⊢ modw M (W ∗ W') P.
  Proof.
    iSplit.
    - iIntros "→P [W W']". iDestruct ("→P" with "W'") as "→P".
      iDestruct ("→P" with "W") as "→P". iStopProof. apply bi.equiv_entails.
      f_equiv. by rewrite assoc.
    - iIntros "→P W' W". iDestruct ("→P" with "[$W $W']") as "→P". iStopProof.
      apply bi.equiv_entails. f_equiv. by rewrite assoc.
  Qed.

  (** [modw] on [emp] world satisfaction *)
  Lemma modw_emp `{!Proper ((⊣⊢) ==> (⊣⊢)) M} {P} : modw M emp P ⊣⊢ M P.
  Proof. by rewrite /modw !left_id. Qed.
End lemmas.

(** ** Update with a custom world satisfaction [W] *)

(** Basic update with a world satisfaction *)
Definition bupdw `{!BiBUpd PROP} (W P : PROP) : PROP := modw bupd W P.
(** Fancy update with a world satisfaction *)
Definition fupdw `{!BiFUpd PROP} (W : PROP) (E E' : coPset) (P : PROP) : PROP :=
  modw (fupd E E') W P.

(** *** Notation *)

Module UpdwNotation.
  Notation "|=[ W ] => P" := (bupdw W P)
    (at level 99, P at level 200, format "'[  ' |=[ W ] =>  '/' P ']'")
    : bi_scope.
  Notation "P =[ W ]=∗ Q" := (P -∗ |=[W]=> Q)%I
    (at level 99, Q at level 200, format "'[' P  =[ W ]=∗  '/' '[' Q ']' ']'")
    : bi_scope.
  Notation "P =[ W ]=∗ Q" := (P -∗ |=[W]=> Q) : stdpp_scope.

  Notation "|=[ W ] { E , E' }=> P" := (fupdw W E E' P)
    (at level 99, P at level 200,
      format "'[  ' |=[ W ] '/' { E , E' }=>  '/' P ']'") : bi_scope.
  Notation "|=[ W ] { E }=> P" := (fupdw W E E P)
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
End UpdwNotation.
Import UpdwNotation.

(** *** Lemmas *)
Section lemmas.
  Context {PROP : bi}.
  Implicit Type (M : PROP → PROP) (W P Q R : PROP).

  (** [bupdw W] and [fupdw W E E] satisfy [GenUpd] *)
  #[export] Instance gen_upd_bupdw `{!BiBUpd PROP} {W} : GenUpd (bupdw W).
  Proof. exact _. Qed.
  #[export] Instance gen_upd_fupdw
    `{!BiBUpd PROP, !BiFUpd PROP, !BiBUpdFUpd PROP} {W E} :
    GenUpd (fupdw W E E).
  Proof. exact _. Qed.

  (** For [modw M] on [GenUpd] [M] *)
  Lemma bupdw_modw_gen_upd `{!BiBUpd PROP, !GenUpd M} {W P} :
    (|=[W]=> P) ⊢ modw M W P.
  Proof. rewrite /bupdw /modw. f_equiv. apply gen_upd_from_bupd. Qed.
  #[export] Instance elim_modal_modw_gen_upd {p P Q}
    `{!BiBUpd PROP, !GenUpd M, !WsatIncl W W' Wr} :
    ElimModal True p false (modw M W' P) P (modw M W Q) (modw M W Q) | 10.
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim gen_upd_frame_r
      bi.wand_elim_r (modw_incl_gen_upd (W:=W)) gen_upd_trans.
  Qed.
  #[export] Instance elim_modal_bupdw_modw_gen_upd {p P Q}
    `{!BiBUpd PROP, !GenUpd M, !WsatIncl W W' Wr} :
    ElimModal True p false (|=[W']=> P) P (modw M W Q) (modw M W Q) | 10.
  Proof. move=> ?. by rewrite bupdw_modw_gen_upd elim_modal_modw_gen_upd. Qed.

  (** [bupdw] is non-expansive *)
  #[export] Instance bupdw_ne `{!BiBUpd PROP} :
    NonExpansive2 (bupdw (PROP:=PROP)).
  Proof. exact _. Qed.
  #[export] Instance bupdw_proper `{!BiBUpd PROP} :
    Proper ((⊣⊢) ==> (⊣⊢) ==> (⊣⊢)) (bupdw (PROP:=PROP)).
  Proof. exact _. Qed.

  (** [fupdw] is non-expansive *)
  #[export] Instance fupdw_ne `{!BiFUpd PROP} {n} :
    Proper ((≡{n}≡) ==> (=) ==> (=) ==> (≡{n}≡) ==> (≡{n}≡))
      (fupdw (PROP:=PROP)).
  Proof. solve_proper. Qed.
  #[export] Instance fupdw_proper `{!BiFUpd PROP} :
    Proper ((⊣⊢) ==> (=) ==> (=) ==> (⊣⊢) ==> (⊣⊢)) (fupdw (PROP:=PROP)).
  Proof. solve_proper. Qed.

  (** [fupdw] absorbs [◇] *)
  #[export] Instance is_except_0_fupdw `{!BiFUpd PROP} {W E E' P} :
    IsExcept0 (|=[W]{E,E'}=> P).
  Proof. rewrite /IsExcept0. by iIntros ">?". Qed.

  (** [bupdw] is monotone *)
  #[export] Instance bupdw_mono `{!BiBUpd PROP} {W} :
    Proper ((⊢) ==> (⊢)) (bupdw (PROP:=PROP) W).
  Proof. exact _. Qed.
  #[export] Instance bupdw_mono' `{!BiBUpd PROP} {W} :
    Proper (flip (⊢) ==> flip (⊢)) (bupdw (PROP:=PROP) W).
  Proof. exact _. Qed.

  (** [fupdw] is monotone *)
  #[export] Instance fupdw_mono `{!BiFUpd PROP} {W E E'} :
    Proper ((⊢) ==> (⊢)) (fupdw (PROP:=PROP) W E E').
  Proof. exact _. Qed.
  #[export] Instance fupdw_flip_mono' `{!BiFUpd PROP} {W E E'} :
    Proper (flip (⊢) ==> flip (⊢)) (fupdw (PROP:=PROP) W E E').
  Proof. exact _. Qed.

  (** Modify the world satisfaction of [bupdw] *)
  Lemma bupdw_incl_bupd `{!BiBUpd PROP} {W W' P} :
    (W ==∗ W' ∗ (W' ==∗ W)) -∗ (|=[W']=> P) =[W]=∗ P.
  Proof.
    iIntros "∝ →P W". iMod ("∝" with "W") as "[W' →W]".
    iMod ("→P" with "W'") as "[W' $]". by iApply "→W".
  Qed.
  Lemma bupdw_incl `{!BiBUpd PROP} {P} `(!WsatIncl W W' Wr) :
    (|=[W']=> P) ⊢ |=[W]=> P.
  Proof. exact (modw_incl_gen_upd WsatIncl0). Qed.

  (** Modify the world satisfaction of [fupdw] *)
  Lemma fupdw_incl_fupd `{!BiFUpd PROP} {W W' E E' P} :
    (W ={E}=∗ W' ∗ (W' ={E'}=∗ W)) -∗ (|=[W']{E,E'}=> P) =[W]{E,E'}=∗ P.
  Proof.
    iIntros "∝ →P W". iMod ("∝" with "W") as "[W' →W]".
    iMod ("→P" with "W'") as "[W' $]". by iApply "→W".
  Qed.
  Lemma fupdw_incl `{!BiFUpd PROP} {E E' P} `(!WsatIncl W W' Wr) :
    (|=[W']{E,E'}=> P) ⊢ |=[W]{E,E'}=> P.
  Proof. apply (modw_incl WsatIncl0). by iIntros "%%[?$]". Qed.

  (** Introduce [bupdw] *)
  #[export] Instance from_modal_bupdw `{!BiBUpd PROP} {W P} :
    FromModal True modality_id (|=[W]=> P) (|=[W]=> P) P.
  Proof. exact _. Qed.
  #[export] Instance from_assumption_bupdw
    `{!BiBUpd PROP, !FromAssumption p P Q} {W} :
    KnownRFromAssumption p P (|=[W]=> Q).
  Proof. exact _. Qed.
  #[export] Instance from_pure_bupdw `{!BiBUpd PROP, !FromPure a P φ} {W} :
    FromPure a (|=[W]=> P) φ.
  Proof. exact _. Qed.

  (** Introduce [fupdw] *)
  #[export] Instance from_modal_fupdw `{!BiFUpd PROP} {W E P} :
    FromModal True modality_id (|=[W]{E}=> P) (|=[W]{E}=> P) P.
  Proof. apply from_modal_modw. iIntros. by iModIntro. Qed.
  #[export] Instance from_modal_fupdw_wrong_mask `{!BiFUpd PROP} {W E E' P} :
    FromModal (pm_error
      "Only non-mask-changing update modalities can be introduced directly.
Use [iApply fupdw_mask_intro] to introduce mask-changing update modalities")
      modality_id (|=[W]{E,E'}=> P) (|=[W]{E,E'}=> P) P | 100.
  Proof. by case. Qed.
  #[export] Instance from_assumption_fupdw
    `{!BiFUpd PROP, !FromAssumption p P Q} {W E} :
    KnownRFromAssumption p P (|=[W]{E}=> Q).
  Proof. apply from_assumption_modw. iIntros. by iModIntro. Qed.
  #[export] Instance from_pure_fupdw `{!BiFUpd PROP, !FromPure a P φ} {W E} :
    FromPure a (|=[W]{E}=> P) φ.
  Proof. apply from_pure_modw. iIntros. by iModIntro. Qed.
  Lemma fupdw_mask_intro `{!BiFUpd PROP} {W E E' P} : E' ⊆ E →
    ((|={E',E}=> emp) -∗ P) ⊢ |=[W]{E,E'}=> P.
  Proof. iIntros (?) "? $". by iApply fupd_mask_intro. Qed.
  Lemma bupdw_fupdw `{!BiBUpd PROP, !BiFUpd PROP, !BiBUpdFUpd PROP} E {W P} :
    (|=[W]=> P) ⊢ |=[W]{E}=> P.
  Proof. exact bupdw_modw_gen_upd. Qed.

  (** Frame on [bupdw] *)
  #[export] Instance frame_bupdw `{!BiBUpd PROP, !Frame p R P Q} {W} :
    Frame p R (|=[W]=> P) (|=[W]=> Q) | 2.
  Proof. exact _. Qed.

  (** Frame on [fupdw] *)
  #[export] Instance frame_fupdw `{!BiFUpd PROP, !Frame p R P Q} {W E E'} :
    Frame p R (|=[W]{E,E'}=> P) (|=[W]{E,E'}=> Q) | 2.
  Proof. exact _. Qed.
  Lemma fupdw_frame_r `{!BiFUpd PROP} {W E E' P Q} :
    (|=[W]{E,E'}=> P) ∗ Q ⊢ |=[W]{E,E'}=> P ∗ Q.
  Proof. by iIntros "[? $]". Qed.

  (** Compose with [bupdw] *)
  #[export] Instance elim_modal_bupdw `{!BiBUpd PROP, !WsatIncl W W' Wr}
    {p P Q} : ElimModal True p false (|=[W']=> P) P (|=[W]=> Q) (|=[W]=> Q).
  Proof. rewrite /ElimModal (bupdw_incl (W:=W)). exact elim_modal_gen_upd. Qed.
  #[export] Instance elim_modal_bupdw_wrong_wsat `{!BiBUpd PROP} {p P Q W W'} :
    ElimModal
      (pm_error "The target world satisfaction doesn't satisfy [WsatIncl]")
      p false (|=[W']=> P) False (|=[W]=> Q) False | 100.
  Proof. case. Qed.
  #[export] Instance elim_modal_bupd_bupdw `{!BiBUpd PROP} {p W P Q} :
    ElimModal True p false (|==> P) P (|=[W]=> Q) (|=[W]=> Q).
  Proof. exact _. Qed.
  #[export] Instance add_modal_bupdw `{!BiBUpd PROP} {W P Q} :
    AddModal (|=[W]=> P) P (|=[W]=> Q).
  Proof. exact _. Qed.

  (** Compose with [fupdw] *)
  Lemma fupdw_trans `{!BiFUpd PROP} {E E' E'' W P} :
    (|=[W]{E,E'}=> |=[W]{E',E''}=> P) ⊢ |=[W]{E,E''}=> P.
  Proof. apply modw_compose. by iIntros "% >?". Qed.
  #[export] Instance elim_modal_fupdw_fupdw
    `{!BiFUpd PROP, !WsatIncl W W' Wr} {p E E' E'' P Q} :
    ElimModal True p false (|=[W']{E,E'}=> P) P
      (|=[W]{E,E''}=> Q) (|=[W]{E',E''}=> Q).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim fupdw_frame_r
      bi.wand_elim_r (fupdw_incl (W:=W)) fupdw_trans.
  Qed.
  #[export] Instance elim_modal_fupdw_fupdw_wrong_mask
    `{!BiFUpd PROP, !WsatIncl W W' Wr} {p E E' E'' E''' P Q} :
    ElimModal
      (pm_error "Goal and eliminated modality must have the same mask.
Use [iMod (fupd_mask_subseteq E')] to adjust the mask of your goal to [E']")
      p false (|=[W']{E,E'}=> P) False (|=[W]{E'',E'''}=> Q) False | 80.
  Proof. case. Qed.
  #[export] Instance elim_modal_fupdw_fupdw_wrong_wsat
    `{!BiFUpd PROP} {p E E' E'' P Q W W'} :
    ElimModal
      (pm_error "The target world satisfaction doesn't satisfy [WsatIncl]")
      p false (|=[W']{E,E'}=> P) False (|=[W]{E,E''}=> Q) False | 100.
  Proof. case. Qed.
  #[export] Instance elim_modal_bupdw_fupdw {p E E' P Q}
    `{!BiBUpd PROP, !BiFUpd PROP, !BiBUpdFUpd PROP, !WsatIncl W W' Wr} :
    ElimModal True p false (|=[W']=> P) P (|=[W]{E,E'}=> Q) (|=[W]{E,E'}=> Q)
    | 10.
  Proof. move=> ?. by rewrite (bupdw_fupdw E) elim_modal_fupdw_fupdw. Qed.
  #[export] Instance elim_modal_bupdw_fupdw_wrong_wsat {p E E' P Q W W'}
    `{!BiBUpd PROP, !BiFUpd PROP, !BiBUpdFUpd PROP} :
    ElimModal
      (pm_error "The target world satisfaction doesn't satisfy [WsatIncl]")
      p false (|=[W']=> P) False (|=[W]{E,E'}=> Q) False | 100.
  Proof. case. Qed.
  #[export] Instance elim_modal_fupd_fupdw `{!BiFUpd PROP} {p E E' E'' W P Q} :
    ElimModal True p false (|={E,E'}=> P) P
      (|=[W]{E,E''}=> Q) (|=[W]{E',E''}=> Q).
  Proof. exact _. Qed.
  #[export] Instance elim_modal_fupd_fupdw_wrong_mask `{!BiFUpd PROP}
    {p E E' E'' E''' P Q W} :
    ElimModal
      (pm_error "Goal and eliminated modality must have the same mask.
Use [iMod (fupd_mask_subseteq E')] to adjust the mask of your goal to [E']")
      p false (|={E,E'}=> P) False (|=[W]{E'',E'''}=> Q) False | 100.
  Proof. case. Qed.
  #[export] Instance elim_modal_bupd_fupdw
    `{!BiBUpd PROP, !BiFUpd PROP, !BiBUpdFUpd PROP} {p W E E' P Q} :
    ElimModal True p false (|==> P) P (|=[W]{E,E'}=> Q) (|=[W]{E,E'}=> Q) | 10.
  Proof. exact _. Qed.
  #[export] Instance add_modal_fupdw `{!BiFUpd PROP} {W E E' P Q} :
    AddModal (|=[W]{E}=> P) P (|=[W]{E,E'}=> Q).
  Proof. by rewrite /AddModal fupdw_frame_r bi.wand_elim_r fupdw_trans. Qed.
  #[export] Instance add_modal_fupd_fupdw `{!BiFUpd PROP} {W E E' P Q} :
    AddModal (|={E}=> P) P (|=[W]{E,E'}=> Q).
  Proof. rewrite /AddModal fupd_frame_r bi.wand_elim_r. iIntros ">$". Qed.

  (** [modw] on [bupdw] *)
  Lemma modw_bupdw `{!BiBUpd PROP} {W W' P} :
    modw (bupdw W) W' P ⊣⊢ |=[W ∗ W']=> P.
  Proof. exact modw_modw_sep. Qed.
  (** [modw] on [fupdw] *)
  Lemma modw_fupdw `{!BiFUpd PROP} {W W' E E' P} :
    modw (fupdw W E E') W' P ⊣⊢ |=[W ∗ W']{E,E'}=> P.
  Proof. exact modw_modw_sep. Qed.

  (** More instances for [bupdw] *)
  #[export] Instance from_sep_bupdw `{!BiBUpd PROP, !FromSep P Q Q'} {W} :
    FromSep (|=[W]=> P) (|=[W]=> Q) (|=[W]=> Q').
  Proof. exact _. Qed.
  #[export] Instance from_or_bupdw `{!BiBUpd PROP, !FromOr P Q Q'} {W} :
    FromOr (|=[W]=> P) (|=[W]=> Q) (|=[W]=> Q').
  Proof. exact _. Qed.
  #[export] Instance from_exist_bupdw `{!BiBUpd PROP, !FromExist (A:=A) P Φ}
    {W} : FromExist (|=[W]=> P) (λ x, |=[W]=> (Φ x))%I.
  Proof. exact _. Qed.
  #[export] Instance into_and_bupdw `{!BiBUpd PROP, !IntoAnd false P Q R} {W} :
    IntoAnd false (|=[W]=> P) (|=[W]=> Q) (|=[W]=> R).
  Proof. exact _. Qed.
  #[export] Instance into_forall_bupdw `{!BiBUpd PROP, !IntoForall (A:=A) P Φ}
    {W} : IntoForall (|=[W]=> P) (λ x, |=[W]=> (Φ x))%I.
  Proof. exact _. Qed.

  (** More instances for [fupdw] *)
  #[export] Instance from_sep_fupdw `{!BiFUpd PROP, !FromSep P Q Q'} {W E} :
    FromSep (|=[W]{E}=> P) (|=[W]{E}=> Q) (|=[W]{E}=> Q').
  Proof. rewrite /FromSep -(from_sep P). by iIntros "[>$ >$]". Qed.
  #[export] Instance from_or_fupdw `{!BiFUpd PROP, !FromOr P Q Q'} {W E} :
    FromOr (|=[W]{E}=> P) (|=[W]{E}=> Q) (|=[W]{E}=> Q').
  Proof.
    rewrite /FromOr -(from_or P). iIntros "[>?|>?] !>"; by [iLeft|iRight].
  Qed.
  #[export] Instance from_exist_fupdw `{!BiFUpd PROP, !FromExist (A:=A) P Φ}
    {W E E'} : FromExist (|=[W]{E,E'}=> P) (λ x, |=[W]{E,E'}=> (Φ x))%I.
  Proof.
    rewrite /FromExist -(from_exist P). iIntros "[% >?] !>". by iExists _.
  Qed.
  #[export] Instance into_and_fupdw
    `{!BiFUpd PROP, !IntoAnd false P Q R} {W E E'} :
    IntoAnd false (|=[W]{E,E'}=> P) (|=[W]{E,E'}=> Q) (|=[W]{E,E'}=> R).
  Proof.
    move: IntoAnd0. rewrite /IntoAnd=>/=->. iIntros "∧".
    iSplit; by [iMod "∧" as "[$ _]"|iMod "∧" as "[_ $]"].
  Qed.
  #[export] Instance into_forall_fupdw
    `{!BiFUpd PROP, !IntoForall (A:=A) P Φ} {W E E'} :
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

Section acsr.
  Context `{!BiBUpd PROP}.

  (** ** [acsr]: Accessor getting [P] from [Q] via the modality [M] *)
  Definition acsr M P Q : PROP := Q -∗ M (P ∗ (P -∗ M Q))%I.

  (** [acsr] is proper *)
  #[export] Instance acsr_ne `{!GenUpd M} : NonExpansive2 (acsr M).
  Proof. solve_proper. Qed.

  (** [acsr] is reflexive and transitive *)
  Lemma acsr_refl `{!GenUpd M} {P} : ⊢ acsr M P P.
  Proof. by iIntros "$ !> $". Qed.
  Lemma acsr_trans `{!GenUpd M} {P Q R} :
    acsr M P Q -∗ acsr M Q R -∗ acsr M P R.
  Proof.
    iIntros "QPQ RQR R". iMod ("RQR" with "R") as "[Q QR]".
    iMod ("QPQ" with "Q") as "[$ PQ]". iIntros "!> P".
    iMod ("PQ" with "P") as "Q". by iApply "QR".
  Qed.

  (** [acsr] over [∗] *)
  Lemma acsr_sep_l `{!GenUpd M} {P Q} : ⊢ acsr M P (P ∗ Q).
  Proof. by iIntros "[$$] !> $". Qed.
  Lemma acsr_sep_r `{!GenUpd M} {P Q} : ⊢ acsr M Q (P ∗ Q).
  Proof. by iIntros "[$$] !> $". Qed.
End acsr.
