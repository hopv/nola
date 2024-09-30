(** * Modality with a custom world satisfaction *)

From nola.bi Require Export mod.
From iris.bi Require Export bi.
From iris.proofmode Require Import proofmode.
Import BUpd0Notation.

Implicit Type PROP : bi.

(** ** World satisfaction inclusion *)

Class WsatIncl {PROP} (W W' Wr : PROP) : Prop := wsat_incl : W ⊣⊢ W' ∗ Wr.
Hint Mode WsatIncl + ! ! - : typeclass_instances.
Arguments WsatIncl {_} _%_I _%_I _%_I : simpl never.
Arguments wsat_incl {_} _%_I _%_I _%_I {_}.

Section wsat_incl.
  Context {PROP}.
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

Definition modw {PROP} (M : PROP → PROP) (W P : PROP) : PROP :=
  W -∗ M (W ∗ P)%I.
Arguments modw : simpl never.

(** Basic update with a world satisfaction *)
Notation bupdw := (modw bupd).
Notation bupdw_0 := (modw bupd_0).
(** Fancy update with a world satisfaction *)
Notation fupdw E E' := (modw (fupd E E')).

(** ** Notation for [bupdw] and [fupdw] *)

Module UpdwNotation.
  Notation "|=[ W ] => P" := (bupdw W P)
    (at level 99, P at level 200, format "'[  ' |=[ W ] =>  '/' P ']'")
    : bi_scope.
  Notation "P =[ W ]=∗ Q" := (P -∗ |=[W]=> Q)%I
    (at level 99, Q at level 200, format "'[' P  =[ W ]=∗  '/' '[' Q ']' ']'")
    : bi_scope.
  Notation "P =[ W ]=∗ Q" := (P -∗ |=[W]=> Q) : stdpp_scope.

  Notation "|=[ W ] =>◇ P" := (bupdw_0 W P)
    (at level 99, P at level 200, format "'[  ' |=[ W ] =>◇  '/' P ']'")
    : bi_scope.
  Notation "P =[ W ]=∗◇ Q" := (P -∗ |=[W]=>◇ Q)%I
    (at level 99, Q at level 200, format "'[' P  =[ W ]=∗◇  '/' '[' Q ']' ']'")
    : bi_scope.
  Notation "P =[ W ]=∗◇ Q" := (P -∗ |=[W]=>◇ Q) : stdpp_scope.

  Notation "|=[ W ] { E , E' }=> P" := (fupdw E E' W P)
    (at level 99, P at level 200,
      format "'[  ' |=[ W ] { E , E' }=>  '/' P ']'") : bi_scope.
  Notation "|=[ W ] { E }=> P" := (fupdw E E W P)
    (at level 99, P at level 200, format "'[  ' |=[ W ] { E }=>  '/' P ']'")
    : bi_scope.
  Notation "P =[ W ] { E , E' }=∗ Q" := (P -∗ |=[W]{E,E'}=> Q)%I
    (at level 99, Q at level 200,
      format "'[' P  =[ W ] { E , E' }=∗  '/' '[' Q ']' ']'") : bi_scope.
  Notation "P =[ W ] { E , E' }=∗ Q" := (P -∗ |=[W]{E,E'}=> Q) : stdpp_scope.
  Notation "P =[ W ] { E }=∗ Q" := (P -∗ |=[W]{E}=> Q)%I
    (at level 99, Q at level 200,
      format "'[' P  =[ W ] { E }=∗  '/' '[' Q ']' ']'") : bi_scope.
  Notation "P =[ W ] { E }=∗ Q" := (P -∗ |=[W]{E}=> Q) : stdpp_scope.

  (** We move the position of [▷] to make the notation work *)
  Notation "|=[ W ] { E }▷[ E' ] => P" := (|=[W]{E,E'}=> ▷ |=[W]{E',E}=> P)%I
    (at level 99, P at level 200,
      format "'[  ' |=[ W ] { E }▷[ E' ] =>  '/' P ']'") : bi_scope.
  Notation "|=[ W ] { E }▷=> P" := (|=[W]{E}=> ▷ |=[W]{E}=> P)%I
    (at level 99, P at level 200,
      format "'[  ' |=[ W ] { E }▷=>  '/' P ']'") : bi_scope.
  Notation "|=[ W ] { E }▷[ E' ] =>^ n P" :=
    (Nat.iter n (λ Q, |=[W]{E}▷[E'] => Q) P)%I
    (at level 99, P at level 200, n at level 9,
      format "'[  ' |=[ W ] { E }▷[ E' ] =>^ n  '/' P ']'") : bi_scope.
  Notation "|=[ W ] { E }▷=>^ n P" :=
    (Nat.iter n (λ Q, |=[W]{E}▷=> Q) P)%I
    (at level 99, P at level 200, n at level 9,
      format "'[  ' |=[ W ] { E }▷=>^ n  '/' P ']'") : bi_scope.
End UpdwNotation.
Import UpdwNotation.

(** ** Modality classes of [modw] *)
#[export] Instance modw_mod `{!@Mod PROP M} {W} : Mod (modw M W).
Proof. split; solve_proper. Qed.
#[export] Instance modw_mod_intro `{!@ModIntro PROP M} {W} :
  ModIntro (modw M W).
Proof. iIntros "% ?? !>". iFrame. Qed.
#[export] Instance modw_mod_trans `{!@Mod PROP M, !ModTrans M} {W} :
  ModTrans (modw M W).
Proof.
  iIntros "%P →P W". iDestruct ("→P" with "W") as "?". iStopProof.
  rewrite -[(M (W ∗ P))%I]mod_trans. f_equiv. iIntros "[W →P]". by iApply "→P".
Qed.
#[export] Instance modw_mod_frame `{!@Mod PROP M, !ModFrame M} {W} :
  ModFrame (modw M W).
Proof. by iIntros "%%[$?]". Qed.
#[export] Instance modw_mod_upd `{!@ModUpd PROP M} {W} : ModUpd (modw M W).
Proof. split; exact _. Qed.
#[export] Instance modw_absorb_bupd
  `{!BiBUpd PROP, !AbsorbBUpd (PROP:=PROP) M} {W} :
  AbsorbBUpd (modw M W) | 10.
Proof. by iIntros (?) ">$$". Qed.
#[export] Instance modw_mod_plain `{!BiPlainly PROP, !BiBUpd PROP}
  `{!@Mod PROP M, !ModPlain M, !Affine W} :
  ModPlain (modw M W) | 10.
Proof.
  split.
  - move=> >. iIntros "[→P R] W". rewrite [(W ∗ _)%I]comm -assoc.
    rewrite -mod_plain_keep_l. iFrame "R W". iIntros "[R W]".
    iDestruct ("→P" with "R W") as "?". iStopProof. f_equiv. iIntros "[_ $]".
  - move=> ? Φ ?. iIntros "→Φ W".
    iApply (mod_plain_keep_r (M:=M) (P:=∀ a, Φ a)). iFrame "W".
    iIntros "W". iApply (mod_plain_forall (M:=M) (Φ:=Φ)). iIntros (a).
    iDestruct ("→Φ" $! a with "W") as "?". iStopProof. f_equiv. iIntros "[_ $]".
Qed.

(** ** Lemmas on [modw] *)
Section modw.
  Context {PROP}.
  Implicit Type (M : PROP → PROP) (W P Q R : PROP).

  (** Fold the definition of [modw] *)
  Lemma modw_fold M W P : (W -∗ M (W ∗ P)) ⊣⊢ modw M W P.
  Proof. done. Qed.

  (** [modw] is non-expansive and proper *)
  #[export] Instance modw_ne_gen {n} :
    Proper (((≡{n}≡) ==> (≡{n}≡)) ==> (≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡))
      (@modw PROP).
  Proof. unfold modw=> ?? eqv ?*?*. f_equiv=>//. apply eqv. solve_proper. Qed.
  #[export] Instance modw_proper_gen :
    Proper (((≡) ==> (≡)) ==> (≡) ==> (≡) ==> (≡)) (@modw PROP).
  Proof. unfold modw=> ?? eqv ?*?*. f_equiv=>//. apply eqv. solve_proper. Qed.

  Context `{!Mod M}.

  (** Modify the world satisfaction of [modw] under [ModFrame M] *)
  Lemma modw_incl `{!ModFrame M, !WsatIncl W W' Wr} {P} :
    modw M W' P ⊢ modw M W P.
  Proof. rewrite (wsat_incl W W'). iIntros "→P [W' $]". by iApply "→P". Qed.

  (** [modw] preserves [ModExcept0] *)
  #[export] Instance mod_except_0_modw `{!ModExcept0 M} {W} :
    ModExcept0 (modw M W).
  Proof. unfold IsExcept0. by iIntros "% >?". Qed.

  (** Compose [modw]s composing the modalities *)
  Lemma modw_compose {M' M'' W P} :
    (∀ P, M (M' P) ⊢ M'' P) → modw M W (modw M' W P) ⊢ modw M'' W P.
  Proof.
    iIntros (toM'') "→P W". iDestruct ("→P" with "W") as "→P". iApply toM''.
    iStopProof. f_equiv. iIntros "[W →P]". by iApply "→P".
  Qed.

  (** Compose [modw]s accumulating the world satisfaction *)
  Lemma modw_modw_sep {W W' P} :
    modw (modw M W) W' P ⊣⊢ modw M (W ∗ W') P.
  Proof.
    iSplit.
    - iIntros "→P [W W']". iDestruct ("→P" with "W'") as "→P".
      iDestruct ("→P" with "W") as "→P". iStopProof. apply bi.equiv_entails.
      f_equiv. by rewrite assoc.
    - iIntros "→P W' W". iDestruct ("→P" with "[$W $W']") as "→P". iStopProof.
      apply bi.equiv_entails. f_equiv. by rewrite assoc.
  Qed.

  (** [modw] over [emp] world satisfaction *)
  Lemma modw_emp {P} : modw M emp P ⊣⊢ M P.
  Proof. by rewrite /modw !left_id. Qed.

  (** Over [∨] *)
  #[export] Instance from_or_modw `{!FromOr P Q Q'} {W} :
    FromOr (modw M W P) (modw M W Q) (modw M W Q').
  Proof. exact _. Qed.
  (** Over [∃] *)
  #[export] Instance from_exist_modw `{!FromExist (A:=A) P Φ} {W} :
    FromExist (modw M W P) (λ x, modw M W (Φ x)).
  Proof. exact _. Qed.
  (** Over [∧] *)
  #[export] Instance into_and_modw `{!IntoAnd false P Q R} {W} :
    IntoAnd false (modw M W P) (modw M W Q) (modw M W R).
  Proof. exact _. Qed.
  (** Over [∀] *)
  #[export] Instance into_forall_modw `{!IntoForall (A:=A) P Φ} {W} :
    IntoForall (modw M W P) (λ x, modw M W (Φ x)).
  Proof. exact _. Qed.
End modw.

(** Under [ModIntro] *)
Section mod_intro.
  Context `{!@Mod PROP M, !ModIntro M}.

  (** Introduce [modw] *)
  #[export] Instance from_modal_modw_intro {W P} :
    FromModal True modality_id (modw M W P) (modw M W P) P.
  Proof. exact _. Qed.
  #[export] Instance from_assumption_modw_intro `{!FromAssumption p P Q} {W} :
    KnownRFromAssumption p P (modw M W Q).
  Proof. exact _. Qed.
  #[export] Instance from_pure_modw_intro `{!FromPure a P φ} {W} :
    FromPure a (modw M W P) φ.
  Proof. exact _. Qed.
End mod_intro.

(** Under [ModFrame] *)
Section mod_frame.
  Context `{!@Mod PROP M, !ModFrame M}.

  (** Frame over [modw] *)
  #[export] Instance frame_modw_frame `{!Frame p R P Q} {W} :
    Frame p R (modw M W P) (modw M W Q) | 2.
  Proof. exact _. Qed.
End mod_frame.

(** Eliminate [modw] from [modw] *)
#[export] Instance elim_modal_modw_modw `{!@Mod PROP M', !@Mod PROP M''} {φ}
  `{!∀ R R', ElimModal φ false false (M R) R (M' R') (M'' R')}
  `{!WsatIncl W W' Wr} {p P Q} :
  ElimModal φ p false (@modw PROP M W' P) P (modw M' W Q) (modw M'' W Q).
Proof.
  rewrite /ElimModal bi.intuitionistically_if_elim /= (wsat_incl W W')=> ?.
  iIntros "[→P →Q][W' Wr]". iMod ("→P" with "W'") as "[W' P]".
  iApply ("→Q" with "P"). iFrame.
Qed.

(** Eliminate a usual modality from [modw] *)
#[export] Instance elim_modal_mod_modw `{!@Mod PROP M', !@Mod PROP M''} {φ}
  `{!∀ R R', ElimModal φ false false (M R) R (M' R') (M'' R')} {p P Q W} :
  ElimModal φ p false (M P) P (modw M' W Q) (modw M'' W Q) | 50.
Proof.
  rewrite /ElimModal bi.intuitionistically_if_elim=>/= ?. iIntros "[>P →Q]W".
  iApply ("→Q" with "P W").
Qed.

(** Under [ModTrans] and [ModFrame] *)
Section mod_upd.
  Context `{!@Mod PROP M, !ModTrans M, !ModFrame M}.

  (** [FromSep] over [modw] *)
  #[export] Instance from_sep_modw_upd `{!FromSep P Q Q'} {W} :
    FromSep (modw M W P) (modw M W Q) (modw M W Q').
  Proof. exact _. Qed.
End mod_upd.

(** Under [AbsorbBUpd] *)
Section absorb_bupd.
  Context `{!BiBUpd PROP, !@Mod PROP M, !AbsorbBUpd M}.

  (** Turn from [bupdw] under [ModIntro] *)
  Lemma from_bupdw `{!ModIntro M} {W P} : (|=[W]=> P) ⊢ modw M W P.
  Proof. by rewrite /bupdw /modw -(absorb_bupd (M:=M)) -(mod_intro (M:=M)). Qed.

  (** Turn from [bupdw_0] under [ModIntro] *)
  Lemma from_bupdw_0 `{!ModIntro M, !ModExcept0 M} {W P} :
    (|=[W]=>◇ P) ⊢ modw M W P.
  Proof.
    by rewrite /bupdw_0 /modw -(absorb_bupd (M:=M)) -[M _]is_except_0
      -(mod_intro (M:=M)).
  Qed.

  (** Eliminate [bupdw] *)
  #[export] Instance elim_modal_bupdw_modw_modw_upd `{!WsatIncl W W' Wr}
    {p P Q} :
    ElimModal True p false (|=[W']=> P) P (modw M W Q) (modw M W Q).
  Proof. exact _. Qed.

  (** Eliminate [bupdw_0] *)
  #[export] Instance elim_modal_bupdw_0_modw_modw_upd
    `{!WsatIncl W W' Wr, !ModExcept0 M} {p P Q} :
    ElimModal True p false (|=[W']=>◇ P) P (modw M W Q) (modw M W Q).
  Proof. exact _. Qed.

  (** Absorb [bupdw] *)
  Lemma absorb_bupdw `{!WsatIncl W W' Wr} {P} :
    (|=[W']=> modw M W P) ⊢ modw M W P.
  Proof. by iIntros ">?". Qed.

  (** Absorb [bupdw_0] *)
  Lemma absorb_bupdw_0 `{!WsatIncl W W' Wr, !ModExcept0 M} {P} :
    (|=[W']=>◇ modw M W P) ⊢ modw M W P.
  Proof. by iIntros ">?". Qed.
End absorb_bupd.

(** ** Lemmas on [bupdw] *)
Section bupdw.
  Context `{!BiBUpd PROP}.
  Implicit Type W P Q : PROP.

  (** Modify the world satisfaction of [bupdw] *)
  Lemma bupdw_incl_bupd {W W' P} :
    (W ==∗ W' ∗ (W' ==∗ W)) -∗ (|=[W']=> P) =[W]=∗ P.
  Proof.
    iIntros "∝ →P W". iMod ("∝" with "W") as "[W' →W]".
    iMod ("→P" with "W'") as "[W' $]". by iApply "→W".
  Qed.
  Lemma bupdw_incl `{!WsatIncl W W' Wr} {P} : (|=[W']=> P) ⊢ |=[W]=> P.
  Proof. exact modw_incl. Qed.

  (** [ElimModal] *)
  #[export] Instance elim_modal_bupdw_bupdw_wrong_wsat {p P Q W W'} :
    ElimModal
      (pm_error "The target world satisfaction doesn't satisfy [WsatIncl]")
      p false (|=[W']=> P) False (|=[W]=> Q) False | 100.
  Proof. case. Qed.
  (** [AddModal] *)
  #[export] Instance add_modal_bupdw {W P Q} :
    AddModal (|=[W]=> P) P (|=[W]=> Q).
  Proof. exact _. Qed.

  (** [modw] over [bupdw] *)
  Lemma modw_bupdw {W W' P} : modw (bupdw W) W' P ⊣⊢ |=[W ∗ W']=> P.
  Proof. exact modw_modw_sep. Qed.
End bupdw.

(** ** Lemmas on [bupdw_0] *)
Section bupdw_0.
  Context `{!BiBUpd PROP}.
  Implicit Type W P Q : PROP.

  (** Modify the world satisfaction of [bupdw_0] *)
  Lemma bupdw_0_incl_bupd {W W' P} :
    (W ==∗◇ W' ∗ (W' ==∗◇ W)) -∗ (|=[W']=>◇ P) =[W]=∗◇ P.
  Proof.
    iIntros "∝ →P W". iMod ("∝" with "W") as "[W' →W]".
    iMod ("→P" with "W'") as "[W' $]". by iApply "→W".
  Qed.
  Lemma bupdw_0_incl `{!WsatIncl W W' Wr} {P} : (|=[W']=>◇ P) ⊢ |=[W]=>◇ P.
  Proof. exact modw_incl. Qed.

  (** [ElimModal] *)
  #[export] Instance elim_modal_bupdw_bupdw_0_wrong_wsat {p P Q W W'} :
    ElimModal
      (pm_error "The target world satisfaction doesn't satisfy [WsatIncl]")
      p false (|=[W']=> P) False (|=[W]=>◇ Q) False | 100.
  Proof. case. Qed.
  #[export] Instance elim_modal_bupdw_0_bupdw_0_wrong_wsat {p P Q W W'} :
    ElimModal
      (pm_error "The target world satisfaction doesn't satisfy [WsatIncl]")
      p false (|=[W']=>◇ P) False (|=[W]=>◇ Q) False | 100.
  Proof. case. Qed.
  (** [AddModal] *)
  #[export] Instance add_modal_bupdw_0 {W P Q} :
    AddModal (|=[W]=>◇ P) P (|=[W]=>◇ Q).
  Proof. exact _. Qed.

  (** [modw] over [bupdw_0] *)
  Lemma modw_bupdw_0 {W W' P} : modw (bupdw_0 W) W' P ⊣⊢ |=[W ∗ W']=>◇ P.
  Proof. exact modw_modw_sep. Qed.
End bupdw_0.

(** ** Lemmas on [fupdw] *)

Section fupdw.
  Context `{!BiFUpd PROP}.
  Implicit Type W P Q : PROP.

  (** Modify the world satisfaction of [fupdw] *)
  Lemma fupdw_incl_fupd {W W' E E' P} :
    (W ={E}=∗ W' ∗ (W' ={E'}=∗ W)) -∗ (|=[W']{E,E'}=> P) =[W]{E,E'}=∗ P.
  Proof.
    iIntros "∝ →P W". iMod ("∝" with "W") as "[W' →W]".
    iMod ("→P" with "W'") as "[W' $]". by iApply "→W".
  Qed.
  Lemma fupdw_incl `{!WsatIncl W W' Wr} {E E' P} :
    (|=[W']{E,E'}=> P) ⊢ |=[W]{E,E'}=> P.
  Proof. exact modw_incl. Qed.

  (** Introduce [fupdw] *)
  Lemma fupdw_mask_intro {E E' W P} : E' ⊆ E →
    ((|={E',E}=> emp) -∗ P) ⊢ |=[W]{E,E'}=> P.
  Proof. iIntros (?) "? $". by iApply fupd_mask_intro. Qed.
  Lemma bupdw_fupdw `{!BiBUpd PROP, !BiBUpdFUpd PROP} E {W P} :
    (|=[W]=> P) ⊢ |=[W]{E}=> P.
  Proof. exact from_bupdw. Qed.
  Lemma bupdw_0_fupdw `{!BiBUpd PROP, !BiBUpdFUpd PROP} E {W P} :
    (|=[W]=>◇ P) ⊢ |=[W]{E}=> P.
  Proof. exact from_bupdw_0. Qed.

  (** Compose [fupdw]s *)
  Lemma fupdw_trans {E E' E'' W P} :
    (|=[W]{E,E'}=> |=[W]{E',E''}=> P) ⊢ |=[W]{E,E''}=> P.
  Proof. apply modw_compose. by iIntros "% >?". Qed.

  (** [FromModal] *)
  #[export] Instance from_modal_fupdw_wrong_mask {E E' W P} :
    FromModal (pm_error
      "Only non-mask-changing update modalities can be introduced directly.
Use [iApply fupdw_mask_intro] to introduce mask-changing update modalities")
      modality_id (|=[W]{E,E'}=> P) (|=[W]{E,E'}=> P) P | 100.
  Proof. by case. Qed.
  (** [ElimModal] *)
  #[export] Instance elim_modal_fupdw_fupdw `{!WsatIncl W W' Wr}
    {p E E' E'' P Q} :
    ElimModal True p false (|=[W']{E,E'}=> P) P
      (|=[W]{E,E''}=> Q) (|=[W]{E',E''}=> Q).
  Proof. exact _. Qed.
  #[export] Instance elim_modal_fupdw_fupdw_wrong_mask `{!WsatIncl W W' Wr}
    {p E E' E'' E''' P Q} :
    ElimModal
      (pm_error "Goal and eliminated modality must have the same mask.
Use [iMod (fupd_mask_subseteq E')] to adjust the mask of your goal to [E']")
      p false (|=[W']{E,E'}=> P) False (|=[W]{E'',E'''}=> Q) False | 80.
  Proof. case. Qed.
  #[export] Instance elim_modal_fupdw_fupdw_wrong_wsat {p E E' E'' P Q W W'} :
    ElimModal
      (pm_error "The target world satisfaction doesn't satisfy [WsatIncl]")
      p false (|=[W']{E,E'}=> P) False (|=[W]{E,E''}=> Q) False | 100.
  Proof. case. Qed.
  #[export] Instance elim_modal_bupdw_fupdw_wrong_wsat {p E E' P Q W W'}
    `{!BiBUpd PROP, !BiBUpdFUpd PROP} :
    ElimModal
      (pm_error "The target world satisfaction doesn't satisfy [WsatIncl]")
      p false (|=[W']=> P) False (|=[W]{E,E'}=> Q) False | 100.
  Proof. case. Qed.
  #[export] Instance elim_modal_bupdw_0_fupdw_wrong_wsat {p E E' P Q W W'}
    `{!BiBUpd PROP, !BiBUpdFUpd PROP} :
    ElimModal
      (pm_error "The target world satisfaction doesn't satisfy [WsatIncl]")
      p false (|=[W']=>◇ P) False (|=[W]{E,E'}=> Q) False | 100.
  Proof. case. Qed.
  #[export] Instance elim_modal_fupd_fupdw {p E E' E'' W P Q} :
    ElimModal True p false (|={E,E'}=> P) P
      (|=[W]{E,E''}=> Q) (|=[W]{E',E''}=> Q).
  Proof. exact _. Qed.
  #[export] Instance elim_modal_fupd_fupdw_wrong_mask {p E E' E'' E''' P Q W} :
    ElimModal
      (pm_error "Goal and eliminated modality must have the same mask.
Use [iMod (fupd_mask_subseteq E')] to adjust the mask of your goal to [E']")
      p false (|={E,E'}=> P) False (|=[W]{E'',E'''}=> Q) False | 100.
  Proof. case. Qed.
  (** [AddModal] *)
  #[export] Instance add_modal_fupdw {E E' W P Q} :
    AddModal (|=[W]{E}=> P) P (|=[W]{E,E'}=> Q).
  Proof. by rewrite /AddModal mod_frame_r bi.wand_elim_r fupdw_trans. Qed.

  (** [modw] over [fupdw] *)
  Lemma modw_fupdw {W W' E E' P} :
    modw (fupdw E E' W) W' P ⊣⊢ |=[W ∗ W']{E,E'}=> P.
  Proof. exact modw_modw_sep. Qed.

  (** [ElimAcc] for [fupdw] *)
  #[export] Instance elim_acc_fupdw {X E E' E'' W α β γ P} :
    ElimAcc (X:=X) True (fupd E E') (fupd E' E) α β γ (|=[W]{E,E''}=> P)
      (λ x, |=[W]{E'}=> β x ∗ (γ x -∗? |=[W]{E,E''}=> P))%I.
  Proof.
    iIntros (_) "→P ∝ W". iMod "∝" as (x) "[α β→]".
    iMod ("→P" with "α W") as "[W[β γ→]]".
    iMod ("β→" with "β") as "γ". by iApply ("γ→" with "γ").
  Qed.

  (** Turn [step_fupdwN] into [step_fupdN]

    Combining this with adequacy lemmas for [step_fupdN],
    one can prove adequacy lemmas for [step_fupdwN]. *)
  Lemma step_fupdwN_step_fupdN {W n E E' P} :
    (|=[W]{E}▷[E']=>^n P) ⊢ W -∗ |={E}[E']▷=>^n W ∗ P.
  Proof.
    elim: n=>/=; [by iIntros; iFrame|]=> n ->.
    iIntros "big W". iMod ("big" with "W") as "[W big]". iModIntro. iNext.
    iMod ("big" with "W") as "[W big]". iModIntro. by iApply "big".
  Qed.
End fupdw.
