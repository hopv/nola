(** * On updates *)

From nola Require Export prelude.
From iris.base_logic Require Import fancy_updates.
From iris.proofmode Require Import proofmode.

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
  (at level 99, W at level 50, P at level 200,
    format "'[  ' |=[ W ] =>  '/' P ']'") : bi_scope.
Notation "P =[ W ]=∗ Q" := (P -∗ |=[W]=> Q)%I
  (at level 99, W at level 50, Q at level 200,
    format "'[' P  =[ W ]=∗  '/' '[' Q ']' ']'") : bi_scope.
Notation "P =[ W ]=∗ Q" := (P -∗ |=[W]=> Q) : stdpp_scope.

Notation "|=[ W ] { E , E' }=> P" := (fupdw E E' W P)
  (at level 99, W at level 50, P at level 200,
    format "'[  ' |=[ W ] '/' { E , E' }=>  '/' P ']'") : bi_scope.
Notation "|=[ W ] { E }=> P" := (fupdw E E W P)
  (at level 99, W at level 50, P at level 200,
    format "'[  ' |=[ W ] '/' { E }=>  '/' P ']'") : bi_scope.
Notation "P =[ W ] { E , E' }=∗ Q" := (P -∗ |=[W]{E,E'}=> Q)%I
  (at level 99, W at level 50, Q at level 200,
    format "'[' P  =[ W ] '/' { E , E' }=∗  '/' '[' Q ']' ']'") : bi_scope.
Notation "P =[ W ] { E , E' }=∗ Q" := (P -∗ |=[W]{E,E'}=> Q) : stdpp_scope.
Notation "P =[ W ] { E }=∗ Q" := (P -∗ |=[W]{E}=> Q)%I
  (at level 99, W at level 50, Q at level 200,
    format "'[' P  =[ W ] '/' { E }=∗  '/' '[' Q ']' ']'") : bi_scope.
Notation "P =[ W ] { E }=∗ Q" := (P -∗ |=[W]{E}=> Q) : stdpp_scope.

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
  #[export] Instance from_assumption_bupdw `{!BiBUpd PROP} {p W P Q} :
    FromAssumption p P Q → KnownRFromAssumption p P (|=[W]=> Q).
  Proof.
    rewrite /KnownRFromAssumption /FromAssumption=>->. apply bupdw_intro.
  Qed.
  #[export] Instance from_pure_bupdw `{!BiBUpd PROP} {a W P φ} :
    FromPure a P φ → FromPure a (|=[W]=> P) φ.
  Proof. rewrite /FromPure=> <-. apply bupdw_intro. Qed.

  (** Introduce [fupdw] *)
  Lemma fupdw_intro `{!BiFUpd PROP} {E W P} : P ⊢ |=[W]{E}=> P.
  Proof. by iIntros "$$". Qed.
  #[export] Instance from_modal_fupdw `{!BiFUpd PROP} {E W P} :
    FromModal True modality_id (|=[W]{E}=> P) (|=[W]{E}=> P) P.
  Proof. by rewrite /FromModal /= -fupdw_intro. Qed.
  Lemma bupdw_fupdw `{!BiBUpd PROP, !BiFUpd PROP, !BiBUpdFUpd PROP} E {W P} :
    (|=[W]=> P) ⊢ |=[W]{E}=> P.
  Proof. apply bi.wand_mono; by [|rewrite bupd_fupd]. Qed.
  #[export] Instance from_assumption_fupdw
    `{!BiBUpd PROP, !BiFUpd PROP, !BiBUpdFUpd PROP} {E p W P Q} :
    FromAssumption p P (|=[W]=> Q) → KnownRFromAssumption p P (|=[W]{E}=> Q).
  Proof.
    rewrite /KnownRFromAssumption /FromAssumption=>->. apply bupdw_fupdw.
  Qed.
  #[export] Instance from_pure_fupdw `{!BiFUpd PROP} {a E W P φ} :
    FromPure a P φ → FromPure a (|=[W]{E}=> P) φ.
  Proof. rewrite /FromPure=> <-. apply fupdw_intro. Qed.
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

  (** Eliminate [bupdw] *)
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

  (** Eliminate [fupdw] *)
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
  #[export] Instance add_modal_fupdw `{!BiFUpd PROP} {E E' W P Q} :
    AddModal (|=[W]{E}=> P) P (|=[W]{E,E'}=> Q).
  Proof. by rewrite /AddModal fupdw_frame_r bi.wand_elim_r fupdw_trans. Qed.

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
End lemmas.
