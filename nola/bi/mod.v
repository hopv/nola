(** * Modality classes *)

From nola Require Export prelude.
From nola.bi Require Import util.
From iris.bi Require Export bi.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre total_weakestpre.

Implicit Type PROP : bi.

(** ** [relax_0]: Relax modality with [◇] *)
Definition relax_0 {PROP} (M : PROP → PROP) (P : PROP) : PROP := M (◇ P)%I.
Notation bupd_0 := (relax_0 bupd).

(** ** [ModExcept0]: Modality absorbing [◇] *)
Notation ModExcept0 M := (∀ P, IsExcept0 (M P)).

Module BUpd0Notation.
  Notation "|==>◇ P" := (bupd_0 P) (at level 99, P at level 200,
    format "'[  ' |==>◇  '/' P ']'") : bi_scope.
  Notation "P ==∗◇ Q" := (P -∗ |==>◇ Q)%I (at level 99, Q at level 200,
    format "'[' P  ==∗◇  '/' Q ']'") : bi_scope.
  Notation "P ==∗◇ Q" := (P -∗ |==>◇ Q) : stdpp_scope.
End BUpd0Notation.
Import BUpd0Notation.

(** ** [Mod]: Modality *)
Class Mod {PROP} (M : PROP → PROP) : Prop := MOD {
  mod_ne :: NonExpansive M; (** Non-expansive *)
  mod_mono :: Proper ((⊢) ==> (⊢)) M; (** Monotone *)
}.
Hint Mode Mod + ! : typeclass_instances.
#[export] Instance mod_flip_mono `{!@Mod PROP M} :
  Proper (flip (⊢) ==> flip (⊢)) M.
Proof. move=>/= ??. apply mod_mono. Qed.
#[export] Instance mod_proper `{!@Mod PROP M} : Proper ((⊣⊢) ==> (⊣⊢)) M.
Proof. apply ne_proper, _. Qed.

(** Under [Mod] *)
Section Mod.
  Context `{!@Mod PROP M}.

  (** Over [∨] *)
  Lemma mod_or {P Q} : M P ∨ M Q ⊢ M (P ∨ Q).
  Proof.
    iIntros "[?|?]"; iStopProof; f_equiv; iIntros "?"; by [iLeft|iRight].
  Qed.
  #[export] Instance from_or_mod `{!FromOr P Q Q'} :
    FromOr (M P) (M Q) (M Q') | 10.
  Proof. by rewrite /FromOr -(from_or P) mod_or. Qed.
  (** Over [∃] *)
  Lemma mod_exist {A} {Φ : A → _} : (∃ a, M (Φ a)) ⊢ M (∃ a, Φ a).
  Proof. iIntros "[% ?]". iStopProof. f_equiv. iIntros "?". by iExists _. Qed.
  #[export] Instance from_exist_mod `{!FromExist (A:=A) P Φ} :
    FromExist (M P) (λ x, M (Φ x)) | 10.
  Proof. by rewrite /FromExist -(from_exist P) mod_exist. Qed.
  (** Over [∧] *)
  Lemma mod_and {P Q} : M (P ∧ Q) ⊢ M P ∧ M Q.
  Proof.
    iIntros "∧".
    iSplit; iStopProof; f_equiv; by [iIntros "[? _]"|iIntros "[_ ?]"].
  Qed.
  #[export] Instance into_and_mod `{!IntoAnd false P Q R} :
    IntoAnd false (M P) (M Q) (M R) | 10.
  Proof.
    move: IntoAnd0. rewrite /IntoAnd=>/= ->. by rewrite mod_and.
  Qed.
  (** Over [∀] *)
  Lemma mod_forall {A} {Φ : A → _} : M (∀ a, Φ a) ⊢ ∀ a, M (Φ a).
  Proof. iIntros "Φ %". iStopProof. f_equiv. iIntros "Φ". iApply "Φ". Qed.
  #[export] Instance into_forall_mod `{!IntoForall (A:=A) P Φ} :
    IntoForall (M P) (λ x, M (Φ x)) | 10.
  Proof. by rewrite /IntoForall (into_forall P) mod_forall. Qed.
End Mod.

(** Instances of [Mod] *)
#[export] Instance id_mod {PROP} : @Mod PROP id.
Proof. split; exact _. Qed.
#[export] Instance pers_mod {PROP} : @Mod PROP bi_persistently.
Proof. split; exact _. Qed.
#[export] Instance plainly_mod `{!BiPlainly PROP} : @Mod PROP plainly.
Proof. split; exact _. Qed.
#[export] Instance except_0_mod {PROP} : @Mod PROP bi_except_0.
Proof. split; exact _. Qed.
#[export] Instance later_mod {PROP} : @Mod PROP bi_later.
Proof. split; exact _. Qed.
#[export] Instance bupd_mod `{!BiBUpd PROP} : @Mod PROP bupd.
Proof. split; exact _. Qed.
#[export] Instance fupd_mod `{!BiFUpd PROP} {E E'} : @Mod PROP (fupd E E').
Proof. split; exact _. Qed.
#[export] Instance relax_0_mod `{!@Mod PROP M} : Mod (relax_0 M).
Proof. split; solve_proper. Qed.

(** ** [ModIntro]: Introducable modality *)
Class ModIntro {PROP} (M : PROP → PROP) : Prop := mod_intro : ∀ {P}, P ⊢ M P.
Hint Mode ModIntro + ! : typeclass_instances.

(** Under [ModIntro] *)
Section mod_intro.
  Context `{!@Mod PROP M, !ModIntro M}.

  (** Instances *)
  #[export] Instance from_modal_mod_intro {P} :
    FromModal True modality_id (M P) (M P) P | 10.
  Proof. move=> _. rewrite /FromModal /=. apply mod_intro. Qed.
  #[export] Instance from_assumption_mod_intro `{!FromAssumption p P Q} :
    KnownRFromAssumption p P (M Q) | 10.
  Proof.
    rewrite /KnownRFromAssumption /FromAssumption from_assumption.
    apply mod_intro.
  Qed.
  #[export] Instance from_pure_mod_intro `{!FromPure a P φ} :
    FromPure a (M P) φ | 10.
  Proof. rewrite /FromPure -(from_pure _ P). apply mod_intro. Qed.
  #[export] Instance mod_intro_or_homomorphism :
    MonoidHomomorphism bi_or bi_or (flip (⊢)) M | 10.
  Proof.
    split; [split|]; (try apply _)=>/= >; [apply mod_or|apply mod_intro].
  Qed.

  (** [relax_0 M] absorbs [◇] *)
  #[export] Instance relax_0_mod_intro_except_0 : ModExcept0 (relax_0 M).
  Proof.
    unfold IsExcept0, bi_except_0. iIntros "% [F|$] !>". iMod "F" as %[].
  Qed.

  (** Eat [◇] *)
  Lemma eat_except_0 {P} : ◇ M P ⊢ M (◇ P).
  Proof.
    unfold bi_except_0. iIntros "[?|?]". { iModIntro. by iLeft. }
    iStopProof. f_equiv. iIntros. by iRight.
  Qed.
End mod_intro.

(** Instances of [ModIntro] *)
#[export] Instance id_mod_intro {PROP} : @ModIntro PROP id.
Proof. by move. Qed.
#[export] Instance except_0_mod_intro {PROP} : @ModIntro PROP bi_except_0.
Proof. move. by iIntros. Qed.
#[export] Instance later_mod_intro {PROP} : @ModIntro PROP bi_later.
Proof. move. by iIntros. Qed.
#[export] Instance bupd_mod_intro `{!BiBUpd PROP} : @ModIntro PROP bupd.
Proof. move. by iIntros. Qed.
#[export] Instance fupd_mod_intro `{!BiFUpd PROP} {E} :
  @ModIntro PROP (fupd E E).
Proof. by iIntros "% ? !>". Qed.
#[export] Instance relax_0_mod_intro `{!@ModIntro PROP M} :
  ModIntro (relax_0 M).
Proof. unfold relax_0. by iIntros "% ? !>!>". Qed.

(** ** [ModTrans]: Transitive/idempotent modality *)
Class ModTrans {PROP} (M : PROP → PROP) : Prop :=
  mod_trans : ∀ {P}, M (M P) ⊢ M P.
Hint Mode ModTrans + ! : typeclass_instances.

(** Instances of [ModTrans] *)
#[export] Instance id_mod_trans {PROP} : @ModTrans PROP id.
Proof. by move. Qed.
#[export] Instance except_0_mod_trans {PROP} : @ModTrans PROP bi_except_0.
Proof. move. by iIntros "% >?". Qed.
#[export] Instance bupd_mod_trans `{!BiBUpd PROP} : @ModTrans PROP bupd.
Proof. move. by iIntros "% >?". Qed.
#[export] Instance fupd_mod_trans `{!BiFUpd PROP} {E} :
  @ModTrans PROP (fupd E E).
Proof. move. by iIntros "% >?". Qed.
#[export] Instance relax_0_mod_trans
  `{!@Mod PROP M, !ModIntro M, !ModTrans M} : ModTrans (relax_0 M).
Proof.
  unfold relax_0=> ?. rewrite eat_except_0 mod_trans. f_equiv. by iIntros ">?".
Qed.

(** ** [ModFrame]: Modality with the frame law *)
Class ModFrame {PROP} (M : PROP → PROP) : Prop :=
  mod_frame_l : ∀ {P Q}, P ∗ M Q ⊢ M (P ∗ Q).

(** Under [ModFrame] *)
Section mod_frame.
  Context `{!@Mod PROP M, !ModFrame M}.

  Lemma mod_frame_r {P Q} : M P ∗ Q ⊢ M (P ∗ Q).
  Proof. by rewrite comm mod_frame_l comm. Qed.
  #[export] Instance frame_mod_frame `{!Frame p R P Q} :
    Frame p R (M P) (M Q) | 10.
  Proof. move: Frame0. rewrite /Frame=> <-. apply mod_frame_l. Qed.
End mod_frame.

(** Instances of [ModFrame] *)
#[export] Instance id_mod_frame {PROP} : @ModFrame PROP id.
Proof. by move. Qed.
#[export] Instance except_0_mod_frame {PROP} : @ModFrame PROP bi_except_0.
Proof. iIntros "%%[$$]". Qed.
#[export] Instance bupd_mod_frame `{!BiBUpd PROP} : @ModFrame PROP bupd.
Proof. iIntros "%%[$$]". Qed.
#[export] Instance fupd_mod_frame `{!BiFUpd PROP} {E E'} :
  @ModFrame PROP (fupd E E').
Proof. iIntros "%%[$$]". Qed.
#[export] Instance relax_0_mod_frame `{!@Mod PROP M, !ModFrame M} :
  ModFrame (relax_0 M).
Proof.
  move=> ??. rewrite /relax_0 mod_frame_l. f_equiv. by iIntros "[$ >$]".
Qed.

(** Under [ModFrame] and [ModTrans] *)
Section mod_upd.
  Context `{!@Mod PROP M, !ModFrame M, !ModTrans M}.

  (** Instances *)
  #[export] Instance elim_modal_mod_upd {p P Q} :
    ElimModal True p false (M P) P (M Q) (M Q) | 10.
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim mod_frame_r
      bi.wand_elim_r mod_trans.
  Qed.
  #[export] Instance add_modal_mod_upd {P Q} :
    AddModal (M P) P (M Q) | 10.
  Proof. by rewrite /AddModal mod_frame_r bi.wand_elim_r mod_trans. Qed.
  Lemma mod_upd_sep {P Q} : M P ∗ M Q ⊢ M (P ∗ Q).
  Proof. by iIntros "[>$ ?]". Qed.
  #[export] Instance from_sep_mod_upd `{!FromSep P Q Q'} :
    FromSep (M P) (M Q) (M Q') | 10.
  Proof. by rewrite /FromSep -(from_sep P) mod_upd_sep. Qed.

  (** Plus under [ModIntro] *)
  Context `{!ModIntro M}.

  #[export] Instance mod_upd_sep_homomorphism :
    MonoidHomomorphism bi_sep bi_sep (flip (⊢)) M | 10.
  Proof.
    split; [split|]; (try apply _)=>/= >; [apply mod_upd_sep|apply mod_intro].
  Qed.

  (** Over big operators *)
  Lemma big_sepL_mod_upd {A} (Φ : nat → A → PROP) l :
    ([∗ list] k↦x ∈ l, M (Φ k x)) ⊢ M ([∗ list] k↦x ∈ l, Φ k x).
  Proof. by rewrite (big_opL_commute _). Qed.
  Lemma big_sepM_mod_upd {A} `{Countable K} (Φ : K → A → PROP) l :
    ([∗ map] k↦x ∈ l, M (Φ k x)) ⊢ M ([∗ map] k↦x ∈ l, Φ k x).
  Proof. by rewrite (big_opM_commute _). Qed.
  Lemma big_sepS_mod_upd `{Countable A} (Φ : A → PROP) l :
    ([∗ set] x ∈ l, M (Φ x)) ⊢ M ([∗ set] x ∈ l, Φ x).
  Proof. by rewrite (big_opS_commute _). Qed.
  Lemma big_sepMS_mod_upd `{Countable A} (Φ : A → PROP) l :
    ([∗ mset] x ∈ l, M (Φ x)) ⊢ M ([∗ mset] x ∈ l, Φ x).
  Proof. by rewrite (big_opMS_commute _). Qed.
End mod_upd.

(** ** [ModUpd]: Modality behaving like the update modality *)
Class ModUpd {PROP} (M : PROP → PROP) : Prop := MOD_UPD {
  mod_upd_mod :: Mod M;
  mod_upd_intro :: ModIntro M;
  mod_upd_trans :: ModTrans M;
  mod_upd_frame :: ModFrame M;
}.

(** Instances of [ModUpd] *)
#[export] Instance bupd_mod_upd `{!BiBUpd PROP} : @ModUpd PROP bupd.
Proof. split; exact _. Qed.
#[export] Instance fupd_mod_upd `{!BiFUpd PROP} {E} : @ModUpd PROP (fupd E E).
Proof. split; exact _. Qed.
#[export] Instance relax_0_mod_upd `{!@ModUpd PROP M} : ModUpd (relax_0 M).
Proof. split; exact _. Qed.

(** ** [IsBUpd]: Proposition absorbing [bupd] *)

Class IsBUpd `{!BiBUpd PROP} (P : PROP) : Prop :=
  is_bupd : (|==> P) ⊢ P.
Hint Mode IsBUpd + - ! : typeclass_instances.

(** [ModBUpd]: Modality absorbing [bupd] *)
Notation ModBUpd M := (∀ P, IsBUpd (M P)).

Section is_bupd.
  Context `{!BiBUpd PROP, !IsBUpd (PROP:=PROP) P}.

  (** Eliminate [bupd] under [ModBUpd] *)
  #[export] Instance elim_modal_bupd_is_bupd {p Q} :
    ElimModal True p false (|==> Q) Q P P.
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim mod_frame_r
      bi.wand_elim_r (is_bupd (P:=P)).
  Qed.

  (** Absorb [bupd_0] *)
  Lemma is_bupd_0 `{!IsExcept0 P} : (|==>◇ P) ⊢ P.
  Proof. by rewrite /bupd_0 is_except_0 is_bupd. Qed.
  #[export] Instance elim_modal_bupd_0_is_bupd_except_0 `{!IsExcept0 P} {p Q} :
    ElimModal True p false (|==>◇ Q) Q P P | 0.
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim mod_frame_r
      bi.wand_elim_r is_bupd_0.
  Qed.
End is_bupd.

Section mod_bupd.
  Context `{!BiBUpd PROP, !ModBUpd M, !@ModIntro PROP M}.

  (** Turn from [bupd] *)
  Lemma from_bupd {P} : (|==> P) ⊢ M P.
  Proof. by rewrite {1}[P](mod_intro (M:=M)) is_bupd. Qed.
  Lemma from_bupd_0 `{!ModExcept0 M} {P} : (|==>◇ P) ⊢ M P.
  Proof. by rewrite {1}[P](mod_intro (M:=M)) is_bupd_0. Qed.
End mod_bupd.

(** [bupd] and [fupd] satisfy [ModBUpd] *)
#[export] Instance bupd_mod_bupd `{!BiBUpd PROP} :
  ModBUpd (bupd (PROP:=PROP)).
Proof. unfold IsBUpd. by iIntros "% >?". Qed.
#[export] Instance fupd_mod_bupd
  `{!BiBUpd PROP, !BiFUpd PROP, !BiBUpdFUpd PROP} {E E'} :
  ModBUpd (fupd (PROP:=PROP) E E').
Proof. unfold IsBUpd. by iIntros "% >?". Qed.
(** [relax_0] preserves [ModBUpd] *)
#[export] Instance relax_0_mod_bupd
  `{!BiBUpd PROP, !ModBUpd M} : ModBUpd (relax_0 (PROP:=PROP) M).
Proof. move=> ?. by rewrite /IsBUpd /relax_0 is_bupd. Qed.

Section program.
  Context `{!irisGS_gen hlc Λ Σ}.

  (** [wp] and [twp] are [IsBUpd] *)
  #[export] Instance wp_is_bupd {s E e Φ} : IsBUpd (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /IsBUpd -{2}fupd_wp -bupd_fupd. Qed.
  #[export] Instance twp_is_bupd {s E e Φ} : IsBUpd (WP e @ s; E [{ Φ }]).
  Proof. by rewrite /IsBUpd -{2}fupd_twp -bupd_fupd. Qed.
End program.

(** ** [ModPlain]: Modality behaving nicely over plain propositions

  Analogous to [BiFupdPlainly] *)

Class ModPlain `{!BiPlainly PROP} M : Prop := GEN_UPD_PLAIN {
  (** Eliminate the modality over a plain proposition, keeping the premise *)
  mod_plain_keep_l `{!Plain P} {R} : (R -∗ M P) ∗ R ⊢ M (P ∗ R);
  (** Eliminating a universal quantifier over the modality over plain
    propositions *)
  mod_plain_forall_2 {A} {Φ : A → PROP} `{!∀ a, Plain (Φ a)} :
    (∀ a, M (Φ a)) ⊢ M (∀ a, Φ a);
}.
Hint Mode ModPlain + - ! : typeclass_instances.

(** Instances of [ModPlain] *)
#[export] Instance id_mod_plain `{!BiPlainly PROP, !BiAffine PROP} :
  ModPlain (PROP:=PROP) id.
Proof.
  split=>/=; [|done]. move=> >. iIntros "[→P R]".
  iDestruct ("→P" with "R") as "#?". by iFrame.
Qed.
#[export] Instance except_0_mod_plain `{!BiPlainly PROP, !BiAffine PROP} :
  ModPlain (PROP:=PROP) bi_except_0.
Proof.
  split.
  { move=> >. iIntros "[→P R]". iDestruct ("→P" with "R") as "#?". by iFrame. }
  { move=> >. by iIntros "? %". }
Qed.
#[export] Instance bupd_mod_plain
  `{!BiBUpd PROP, !BiPlainly PROP, !BiBUpdPlainly PROP, !BiAffine PROP} :
  ModPlain (PROP:=PROP) bupd.
Proof.
  split.
  - move=> >. iIntros "[→P R] !>". rewrite bupd_elim.
    iDestruct ("→P" with "R") as "#?". by iFrame.
  - move=> ? Φ ?. have ->: (∀ a, |==> Φ a) ⊢ (∀ a, Φ a); [|by iIntros].
    f_equiv=> ?. by rewrite bupd_elim.
Qed.
#[export] Instance fupd_mod_plain
  `{!BiFUpd PROP, !BiPlainly PROP, !BiFUpdPlainly PROP} {E} :
  ModPlain (PROP:=PROP) (fupd E E).
Proof.
  split=> >. { apply fupd_plain_keep_l, _. } { apply fupd_plain_forall_2, _. }
Qed.
#[export] Instance relax_0_mod_plain
  `{!BiPlainly PROP, !@Mod PROP M, !ModPlain M} :
  ModPlain (relax_0 M).
Proof.
  unfold relax_0. split.
  - move=> >. rewrite mod_plain_keep_l. f_equiv. by iIntros "[>$$]".
  - move=> >. by rewrite mod_plain_forall_2 bi.except_0_forall.
Qed.

Section mod_plain.
  Context `{!BiPlainly PROP, !@Mod PROP M, !ModPlain M}.

  (** Variant of [mod_plain_keep_l] *)
  Lemma mod_plain_keep_r `{!Plain P} {R} : R ∗ (R -∗ M P) ⊢ M (R ∗ P).
  Proof. rewrite comm [(_ ∗ P)%I]comm. apply mod_plain_keep_l. Qed.

  (** Variant of [mod_plain_forall_2] *)
  Lemma mod_plain_forall {A} {Φ : A → PROP} `{!∀ a, Plain (Φ a)} :
    M (∀ a, Φ a) ⊣⊢ ∀ a, M (Φ a).
  Proof.
    apply bi.equiv_entails. split; [|exact mod_plain_forall_2].
    by rewrite mod_forall.
  Qed.
End mod_plain.

(** ** For [bupd_0] *)
Section bupd_0.
  Context `{!BiBUpd PROP}.
  Implicit Type P : PROP.

  #[export] Instance from_or_bupd_0 `{!FromOr P Q Q'} :
    FromOr (|==>◇ P) (|==>◇ Q) (|==>◇ Q').
  Proof. exact _. Qed.
  #[export] Instance from_exist_bupd_0 `{!FromExist (A:=A) P Φ} :
    FromExist (|==>◇ P) (λ x, |==>◇ Φ x)%I.
  Proof. exact _. Qed.
  #[export] Instance into_and_bupd_0 `{!IntoAnd false P Q R} :
    IntoAnd false (|==>◇ P) (|==>◇ Q) (|==>◇ R).
  Proof. exact _. Qed.
  #[export] Instance into_forall_bupd_0 `{!IntoForall (A:=A) P Φ} :
    IntoForall (|==>◇ P) (λ x, |==>◇ (Φ x))%I.
  Proof. exact _. Qed.

  #[export] Instance from_modal_bupd_0 {P} :
    FromModal True modality_id (|==>◇ P) (|==>◇ P) P.
  Proof. exact _. Qed.
  #[export] Instance from_assumption_bupd_0 `{!FromAssumption p P Q} :
    KnownRFromAssumption p P (|==>◇ Q).
  Proof. exact _. Qed.
  #[export] Instance from_pure_bupd_0 `{!FromPure a P φ} :
    FromPure a (|==>◇ P) φ.
  Proof. exact _. Qed.
  #[export] Instance bupd_0_intro_or_homomorphism :
    MonoidHomomorphism (@bi_or PROP) bi_or (flip (⊢)) bupd_0.
  Proof. exact _. Qed.

  #[export] Instance frame_bupd_0 `{!Frame p R P Q} :
    Frame p R (|==>◇ P) (|==>◇ Q).
  Proof. exact _. Qed.

  #[export] Instance add_modal_bupd_0 {P Q} :
    AddModal (|==>◇ P) P (|==>◇ Q) | 2.
  Proof. exact _. Qed.
  #[export] Instance from_sep_bupd_0 `{!FromSep P Q Q'} :
    FromSep (|==>◇ P) (|==>◇ Q) (|==>◇ Q') | 2.
  Proof. exact _. Qed.

  #[export] Instance bupd_0_sep_homomorphism :
    MonoidHomomorphism (@bi_sep PROP) bi_sep (flip (⊢)) bupd_0.
  Proof. exact _. Qed.

  (** Eliminate [bupd_0] over a plain proposition *)
  Lemma bupd_0_elim `{!BiPlainly PROP, !BiBUpdPlainly PROP, !Plain P} :
    (|==>◇ P) ⊢ ◇ P.
  Proof. by rewrite /bupd_0 bupd_elim. Qed.
End bupd_0.

Section mod_acsr.
  Context {PROP}.

  (** ** [mod_acsr]: Accessor from [P] to [Q] via the modality [M] *)
  Definition mod_acsr M P Q : PROP := P -∗ M (Q ∗ (Q -∗ M P))%I.

  (** [mod_acsr] is non-expansive *)
  #[export] Instance mod_acsr_ne_gen {n} :
    Proper (((≡{n}≡) ==> (≡{n}≡)) ==> (≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡)) mod_acsr.
  Proof.
    move=> ?? eqv ??????. unfold mod_acsr. f_equiv=>//. apply eqv.
    do 2 f_equiv=>//. by apply eqv.
  Qed.
  #[export] Instance mod_acsr_ne `{!NonExpansive M} :
    NonExpansive2 (mod_acsr M).
  Proof. exact _. Qed.
  #[export] Instance mod_acsr_proper :
    Proper (((≡) ==> (≡)) ==> (≡) ==> (≡) ==> (≡)) mod_acsr.
  Proof.
    move=> ?? eqv ??????. unfold mod_acsr. f_equiv=>//. apply eqv.
    do 2 f_equiv=>//. by apply eqv.
  Qed.

  Context `{!@Mod PROP M, !ModIntro M}.

  (** [mod_acsr] is reflexive and transitive *)
  Lemma mod_acsr_refl  {P} : ⊢ mod_acsr M P P.
  Proof. iIntros "P !>". iFrame "P". by iIntros. Qed.
  Lemma mod_acsr_trans `{!ModTrans M, !ModFrame M} {P Q R} :
    mod_acsr M P Q -∗ mod_acsr M Q R -∗ mod_acsr M P R.
  Proof.
    iIntros "PQP QRQ P". iMod ("PQP" with "P") as "[Q QP]".
    iMod ("QRQ" with "Q") as "[$ RQ]". iIntros "!> R".
    iMod ("RQ" with "R") as "Q". by iApply "QP".
  Qed.

  (** [mod_acsr] over [∗] *)
  Lemma mod_acsr_sep_l {P Q} : ⊢ mod_acsr M (P ∗ Q) P.
  Proof. iIntros "[P Q] !>". iFrame "P". iIntros "P !>". iFrame. Qed.
  Lemma mod_acsr_sep_r {P Q} : ⊢ mod_acsr M (P ∗ Q) Q.
  Proof. rewrite comm. exact mod_acsr_sep_l. Qed.

  (** [∗-∗] into [mod_acsr] *)
  Lemma wand_iff_mod_acsr {P Q} : □ (P ∗-∗ Q) ⊢ mod_acsr M P Q.
  Proof.
    iIntros "#[PQ QP] P !>". iDestruct ("PQ" with "P") as "$". iIntros "Q !>".
    by iApply "QP".
  Qed.
End mod_acsr.
Arguments mod_acsr : simpl never.

Section mod_iff.
  Context {PROP}.

  (** ** [mod_iff]: Equivalence of [P] and [Q] under the modality [M] *)
  Definition mod_iff M P Q : PROP := ((P -∗ M Q) ∧ (Q -∗ M P))%I.

  (** [mod_iff] is non-expansive *)
  #[export] Instance mod_iff_ne_gen {n} :
    Proper (((≡{n}≡) ==> (≡{n}≡)) ==> (≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡)) mod_iff.
  Proof.
    move=> ?? eqv ??????. unfold mod_iff. do 2 f_equiv=>//; by apply eqv.
  Qed.
  #[export] Instance mod_iff_ne `{!NonExpansive M} : NonExpansive2 (mod_iff M).
  Proof. exact _. Qed.
  #[export] Instance mod_iff_proper_gen :
    Proper (((≡) ==> (≡)) ==> (≡) ==> (≡) ==> (≡)) mod_iff.
  Proof.
    move=> ?? eqv ??????. unfold mod_iff. do 2 f_equiv=>//; by apply eqv.
  Qed.
  #[export] Instance mod_iff_proper `{!Proper ((≡) ==> (≡)) M} :
    Proper ((≡) ==> (≡) ==> (≡)) (mod_iff M).
  Proof. exact _. Qed.

  Context `{!@Mod PROP M, !ModIntro M}.

  (** [mod_iff] is reflexive, symmetric and transitive *)
  Lemma mod_iff_refl {P} : ⊢ mod_iff M P P.
  Proof. iSplit; by iIntros. Qed.
  Lemma mod_iff_sym {P Q} : mod_iff M P Q ⊢ mod_iff M Q P.
  Proof. by rewrite /mod_iff bi.and_comm. Qed.
  Lemma mod_iff_trans `{!ModTrans M, !ModFrame M} {P Q R} :
    mod_iff M P Q -∗ mod_iff M Q R -∗ mod_iff M P R.
  Proof.
    iIntros "PQ QR". iSplit.
    - iIntros "P". iMod ("PQ" with "P"). by iApply "QR".
    - iIntros "R". iMod ("QR" with "R"). by iApply "PQ".
  Qed.

  (** [∗-∗] into [mod_iff] *)
  Lemma wand_iff_mod_iff {P Q} : P ∗-∗ Q ⊢ mod_iff M P Q.
  Proof. iIntros "PQ". iSplit; iIntros "? !>"; by iApply "PQ". Qed.
End mod_iff.
Arguments mod_iff : simpl never.
