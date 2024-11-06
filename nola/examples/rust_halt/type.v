(** * Type model *)

From nola.examples.rust_halt Require Export base.
Import ProdNotation PlistNotation BigSepPLNotation ModwNotation WpwNotation
  iPropAppNotation ProphNotation LftNotation CsemNotation.

Implicit Type (sz d : nat) (X : xty) (t : thread_id) (v : val) (e : expr)
  (l : loc) (α : lft) (CON : cifcon) (Σ : gFunctors).

(** ** Type model *)

(** Ownership formula *)
Definition ownty CON Σ X :=
  thread_id -d> nat -d> clair xty X -d> list val -d> cif CON Σ.
(** Sharing formula *)
Definition shrty CON Σ X :=
  thread_id -d> nat -d> loc -d> lft -d> clair xty X -d> cif CON Σ.
(** Type model *)
Definition ty CON Σ X : Type := ownty CON Σ X * shrty CON Σ X.

(** Simple type, with the sharing formula defined from the ownership formula *)
Definition sty := ownty.
Definition ty_sty `{!rust_haltGS CON Σ, !rust_haltC CON}
  `{!rust_haltJ CON JUDG Σ} {X} (T : ownty CON Σ X) : ty CON Σ X :=
  (T, λ t d l α xπ, ∃ vl, l ↦∗ˢ[α] vl ∗ T t d xπ vl)%cif.
(** Plain type, with the ownership formula ignoring the thread id, the depth,
  and the prophecy assignment *)
Definition pty CON Σ X := X -d> list val -d> cif CON Σ.
Definition sty_pty {CON Σ X} (T : pty CON Σ X) : sty CON Σ X :=
  λ _ _ xπ vl, (∃ x, ⌜xπ = λ _, x⌝ ∗ T x vl)%cif.
Definition ty_pty `{!rust_haltGS CON Σ, !rust_haltC CON}
  `{!rust_haltJ CON JUDG Σ} {X} (T : pty CON Σ X) : ty CON Σ X :=
  ty_sty (sty_pty T).

(** ** Basic properties of a type *)

Section ty.
  Context `{!Csem CON JUDG Σ}.

  (** Basic properties of a type *)
  Class Ty {X} (T : ty CON Σ X) (sz : nat) := TY {
    (** The sharing predicate is persistent *)
    ty_shr_persistent {t d l α xπ δ} :: Persistent ⟦ T.2 t d l α xπ ⟧ᶜ(δ);
    (** The ownership predicate entails the size constraint *)
    ty_own_size {t d xπ vl δ} : ⟦ T.1 t d xπ vl ⟧ᶜ(δ) ⊢ ⌜length vl = sz⌝;
    (** The depth of the ownership and sharing predicates can be bumped up *)
    ty_own_depth {t d d' xπ vl δ} :
      d ≤ d' → ⟦ T.1 t d xπ vl ⟧ᶜ(δ) ⊢ ⟦ T.1 t d' xπ vl ⟧ᶜ(δ);
    ty_shr_depth {t d d' l α xπ δ} :
      d ≤ d' → ⟦ T.2 t d l α xπ ⟧ᶜ(δ) ⊢ ⟦ T.2 t d' l α xπ ⟧ᶜ(δ);
  }.

  (** Basic properties of a simple type *)
  Class Sty {X} (T : sty CON Σ X) (sz : nat) := STY {
    (** The ownership predicate is persistent *)
    sty_persistent {t d xπ vl δ} :: Persistent ⟦ T t d xπ vl ⟧ᶜ(δ);
    (** The ownership predicate entails the size constraint *)
    sty_size {t d xπ vl δ} : ⟦ T t d xπ vl ⟧ᶜ(δ) ⊢ ⌜length vl = sz⌝;
    (** The depth of the ownership predicate can be bumped up *)
    sty_depth {t d d' xπ vl δ} :
      d ≤ d' → ⟦ T t d xπ vl ⟧ᶜ(δ) ⊢ ⟦ T t d' xπ vl ⟧ᶜ(δ);
  }.

  (** Basic properties of a plain type *)
  Class Pty {X} (T : pty CON Σ X) (sz : nat) := PTY {
    (** The ownership predicate is persistent *)
    pty_persistent {x vl δ} :: Persistent ⟦ T x vl ⟧ᶜ(δ);
    (** The ownership predicate entails the size constraint *)
    pty_size {x vl δ} : ⟦ T x vl ⟧ᶜ(δ) ⊢ ⌜length vl = sz⌝;
  }.

  Context `{!rust_haltGS CON Σ, !rust_haltC CON, !rust_haltJ CON JUDG Σ,
    !rust_haltCS CON JUDG Σ}.

  (** [Sty] entails [Ty] *)
  #[export] Instance Ty_Sty `{!@Sty X T sz} : Ty (ty_sty T) sz.
  Proof.
    split=>/= >. { exact _. } { exact sty_size. } { exact sty_depth. }
    { move=> ?. do 3 f_equiv. by apply sty_depth. }
  Qed.

  (** [Pty] entails [Sty] *)
  #[export] Instance Sty_Pty `{!@Pty X T sz} : Sty (sty_pty T) sz.
  Proof.
    split=> > /=; [exact _| |done]. iIntros "[%[% ?]]". iStopProof.
    exact pty_size.
  Qed.
End ty.

(** ** Basic operations on a type *)

Section ty_op.
  Context `{!rust_haltGS CON Σ, rust_haltJ CON JUDG Σ, !Csem CON JUDG Σ,
    !Jsem JUDG (iProp Σ)}.

  (** [TyOpAt]: Basic operations on a type at a depth *)
  Class TyOpAt {X} (T : ty CON Σ X) (β : lft) (d : nat) := TY_OP_AT {
    (** Take out prophecy tokens from ownership and sharing formulas *)
    ty_own_proph {t xπ vl q} :
      q.[β] -∗ ⟦ T.1 t d xπ vl ⟧ᶜ =[rust_halt_wsat]{⊤}=∗ ∃ ξl r,
        ⌜proph_dep xπ ξl⌝ ∗ r:∗[ξl] ∗
        (r:∗[ξl] =[rust_halt_wsat]{⊤}=∗ q.[β] ∗ ⟦ T.1 t d xπ vl ⟧ᶜ);
    ty_shr_proph {t l α xπ q} :
      q.[α ⊓ β] -∗ ⟦ T.2 t d l α xπ ⟧ᶜ =[rust_halt_wsat]{⊤}=∗ ∃ ξl r,
        ⌜proph_dep xπ ξl⌝ ∗ r:∗[ξl] ∗
        (r:∗[ξl] =[rust_halt_wsat]{⊤}=∗ q.[α ⊓ β] ∗ ⟦ T.2 t d l α xπ ⟧ᶜ);
    (** A borrow over the ownership formula can turn into the sharing formula *)
    ty_share {t l α xπ q} :
      q.[α ⊓ β] -∗ bord α (∃ vl, ▷ l ↦∗ vl ∗ T.1 t d xπ vl)%cif
        =[rust_halt_wsat]{⊤}=∗ q.[α ⊓ β] ∗ ⟦ T.2 t d l α xπ ⟧ᶜ;
  }.

  (** [TyOpAt] is monotone *)
  #[export] Instance TyOpAt_mono {X} :
    Proper ((≡) ==> (⊑) --> (=) ==> (→)) (@TyOpAt X).
  Proof.
    move=> T T' [eqvO eqvS] β β' /= inc ?? <- ?. split.
    - move=> >. setoid_rewrite <-(eqvO _ _ _ _). iIntros "β' T".
      iDestruct (lft_incl_live_acc with "β'") as (?) "[β →β']"; [done|].
      iMod (ty_own_proph with "β T") as (??) "($ & $ & →T)". iModIntro.
      iIntros "ξl". iMod ("→T" with "ξl") as "[β $]". iModIntro.
      by iApply "→β'".
    - move=> ?? α ??. setoid_rewrite <-(eqvS _ _ _ _ _). iIntros "αβ' T".
      iDestruct (lft_incl_live_acc (β:=_ ⊓ β) with "αβ'") as (?) "[αβ →αβ']".
      { apply lft_incl_meet_intro; [exact lft_incl_meet_l|].
        by etrans; [exact lft_incl_meet_r|]. }
      iMod (ty_shr_proph with "αβ T") as (??) "($ & $ & →T)". iModIntro.
      iIntros "ξl". iMod ("→T" with "ξl") as "[β $]". iModIntro.
      by iApply "→αβ'".
    - move=> ?? α ??. rewrite -(eqvS _ _ _ _ _). iIntros "αβ' b".
      iDestruct (lft_incl_live_acc (β:=α ⊓ β) with "αβ'") as (?) "[αβ →αβ']".
      { apply lft_incl_meet_intro; [exact lft_incl_meet_l|].
        by etrans; [exact lft_incl_meet_r|]. }
      iMod (ty_share with "αβ [b]") as "[αβ $]"; last first.
      { iModIntro. by iApply "→αβ'". }
      iStopProof. apply bi.equiv_entails. (do 2 f_equiv)=> ?.
      by rewrite (eqvO _ _ _ _).
  Qed.
  #[export] Instance TyOpAt_flip_mono {X} :
    Proper ((≡) ==> (⊑) ==> (=) ==> flip (→)) (@TyOpAt X).
  Proof. move=> ????????<- /=. by apply TyOpAt_mono. Qed.
  #[export] Instance TyOpAt_proper {X} :
    Proper ((≡) ==> (=) --> (=) ==> (↔)) (@TyOpAt X).
  Proof. move=> ?????<-??<-. split; by apply TyOpAt_mono. Qed.

  (** [TyOpLt]: Basic operations on a type below a depth *)
  Class TyOpLt {X} (T : ty CON Σ X) (α : lft) (d : nat) :=
    ty_op_lt : ∀ {d'}, d' < d → TyOpAt T α d'.

  (** [TyOpLt] is monotone *)
  #[export] Instance TyOpLt_mono {X} :
    Proper ((≡) ==> (⊑) --> (=) ==> (→)) (@TyOpLt X).
  Proof. move=> ???????? <- wl ? lt. move: (wl _ lt). by apply TyOpAt_mono. Qed.
  #[export] Instance TyOpLt_flip_mono {X} :
    Proper ((≡) ==> (⊑) ==> (=) ==> flip (→)) (@TyOpLt X).
  Proof. move=> ????????<- /=. by apply TyOpLt_mono. Qed.
  #[export] Instance TyOpLt_proper {X} :
    Proper ((≡) ==> (=) --> (=) ==> (↔)) (@TyOpLt X).
  Proof. move=> ?????<-??<-. split; by apply TyOpLt_mono. Qed.

  (** Lemmas under [TyOpLt] *)
  Section ty_op_lt.
    Context `{!@TyOpLt X T β d0}.
    Lemma ty_own_proph_lt {t d xπ vl q} : d < d0 →
      q.[β] -∗ ⟦ T.1 t d xπ vl ⟧ᶜ =[rust_halt_wsat]{⊤}=∗ ∃ ξl r,
        ⌜proph_dep xπ ξl⌝ ∗ r:∗[ξl] ∗
        (r:∗[ξl] =[rust_halt_wsat]{⊤}=∗ q.[β] ∗ ⟦ T.1 t d xπ vl ⟧ᶜ).
    Proof. move=> ?. by apply ty_op_lt. Qed.
    Lemma ty_shr_proph_lt {t d l α xπ q} : d < d0 →
      q.[α ⊓ β] -∗ ⟦ T.2 t d l α xπ ⟧ᶜ =[rust_halt_wsat]{⊤}=∗ ∃ ξl r,
        ⌜proph_dep xπ ξl⌝ ∗ r:∗[ξl] ∗
        (r:∗[ξl] =[rust_halt_wsat]{⊤}=∗ q.[α ⊓ β] ∗ ⟦ T.2 t d l α xπ ⟧ᶜ).
    Proof. move=> ?. by apply ty_op_lt. Qed.
    Lemma ty_share_lt {t d l α xπ q} : d < d0 →
      q.[α ⊓ β] -∗ bord α (∃ vl, ▷ l ↦∗ vl ∗ T.1 t d xπ vl)%cif
        =[rust_halt_wsat]{⊤}=∗ q.[α ⊓ β] ∗ ⟦ T.2 t d l α xπ ⟧ᶜ.
    Proof. move=> ?. by apply ty_op_lt. Qed.
  End ty_op_lt.

  Context `{!rust_haltC CON, !rust_haltCS CON JUDG Σ, !rust_haltJS CON JUDG Σ}.

  (** Basic operations on a simple type at a depth *)
  Lemma sty_op_at `{!Sty (X:=X) T sz} {d} β :
    (∀ t xπ vl q,
      q.[β] -∗ ⟦ T t d xπ vl ⟧ᶜ =[rust_halt_wsat]{⊤}=∗ ∃ ξl r,
        ⌜proph_dep xπ ξl⌝ ∗ r:∗[ξl] ∗
        (r:∗[ξl] =[rust_halt_wsat]{⊤}=∗ q.[β] ∗ ⟦ T t d xπ vl ⟧ᶜ)) →
    TyOpAt (ty_sty T) β d.
  Proof.
    move=> sty_proph. split=>/= >; [done| |].
    - iIntros "[$ β] (%vl & ↦ & T)".
      iMod (sty_proph with "β T") as (??) "($ & $ & cl)". iIntros "!> ξl".
      iFrame "↦". by iApply "cl".
    - iIntros "[α $] b".
      iMod (bord_open (M:=borrowM) with "α b") as "/=[o (% & >↦ & #T)]".
      iFrame "T".
      iMod (obord_subdiv (FML:=cifOF _) (M:=borrowM) [▷ _]%cif
        with "[] o [$↦ //] []") as "(α & _ & [b _])"=>/=.
      { iApply lft_sincl_refl. } { by iIntros "_ [$ _]". }
      rewrite sem_cif_spointsto_vec.
      by iMod (spointsto_vecd_alloc with "α b") as "$".
  Qed.

  (** Basic operations on a plain type at a depth *)
  #[export] Instance pty_op_at `{!Pty (X:=X) T sz} {α d} :
    TyOpAt (ty_pty T) α d.
  Proof.
    apply sty_op_at=>/= ????. iIntros "$ (% & -> & ?) !>". iExists [], 1%Qp.
    do 2 iSplit=>//. iIntros "_ !>". iExists _. by iSplit.
  Qed.
End ty_op.
(** [TyOpAt]: Basic operations on a type *)
Notation TyOp T α := (∀ d, TyOpAt T α d).

(** ** Type classes *)

Section classes.
  Context {CON Σ}.

  (** [Send]: the ownership formula does not depend on the thread id *)
  Class Send {X} (T : ty CON Σ X) :=
    send : ∀ {t t'}, T.1 t ≡ T.1 t'.
  (** [Send] is proper *)
  #[export] Instance Send_proper {X} : Proper ((≡) ==> (↔)) (@Send X).
  Proof.
    move=> ??[eqv _]. apply forall_proper=> t. apply forall_proper=> t'.
    by rewrite (eqv t) (eqv t').
  Qed.

  (** [Sync]: the sharing formula does not depend on the thread id *)
  Class Sync {X} (T : ty CON Σ X) :=
    sync : ∀ {t t'}, T.2 t ≡ T.2 t'.
  (** [Sync] is proper *)
  #[export] Instance Sync_proper {X} : Proper ((≡) ==> (↔)) (@Sync X).
  Proof.
    move=> ??[_ eqv]. apply forall_proper=> t. apply forall_proper=> t'.
    by rewrite (eqv t) (eqv t').
  Qed.

  Context `{!rust_haltGS CON Σ, rust_haltJ CON JUDG Σ, !Csem CON JUDG Σ,
    !Jsem JUDG (iProp Σ)}.

  (** [Copy] *)
  Class Copy {X} (T : ty CON Σ X) := COPY {
    (** Persistence of the ownership formula *)
    copy_persistent {t d xπ vl δ} : Persistent ⟦ T.1 t d xπ vl ⟧ᶜ(δ);
    (** Access via the sharing formula *)
    copy_shr_acc {t d l α xπ q} :
      q.[α] -∗ na_own t ⊤ -∗ ⟦ T.2 t d l α xπ ⟧ᶜ =[rust_halt_wsat]{⊤}=∗ ∃ r vl,
          l ↦∗{r} vl ∗ ⟦ T.1 t d xπ vl ⟧ᶜ ∗
          (l ↦∗{r} vl =[rust_halt_wsat]{⊤}=∗ q.[α] ∗ na_own t ⊤);
  }.
  (** [Copy] is proper *)
  #[export] Instance Copy_proper {X} : Proper ((≡) ==> (↔)) (@Copy X).
  Proof.
    have pro: Proper ((≡) ==> (→)) (@Copy X); last first.
    { move=> ???. split; by apply pro. }
    move=> ??[eqvO eqvS][??]. split=> >. { by rewrite -(eqvO _ _ _ _). }
    rewrite -(eqvS _ _ _ _ _). by setoid_rewrite <-(eqvO _ _ _ _).
  Qed.

  Context `{!rust_haltC CON, !rust_haltCS CON JUDG Σ, !rust_haltJS CON JUDG Σ}.

  (** [Send] over [sty] entails [Sync] *)
  #[export] Instance sty_send_sync `{!Send (ty_sty (X:=X) T)} :
    Sync (ty_sty (X:=X) T).
  Proof. move=>//= * ????. f_equiv=> ?. f_equiv. apply Send0. Qed.

  (** [pty] is [Send] and [Sync] *)
  #[export] Instance pty_send {X T} : Send (ty_pty (X:=X) T).
  Proof. move=>//=. Qed.
  #[export] Instance pty_sync {X T} : Sync (ty_pty (X:=X) T).
  Proof. exact _. Qed.

  (** [sty] is [Copy] *)
  #[export] Instance sty_copy `{!Sty (X:=X) T sz} : Copy (ty_sty (X:=X) T).
  Proof.
    split; [exact _|]=>/= ??????. iIntros "α $ (% & ↦ & $)".
    rewrite sem_cif_spointsto_vec.
    iMod (spointsto_vecd_acc with "α ↦") as (?) "[$ cl]". iIntros "!> ↦s".
    by iMod ("cl" with "↦s").
  Qed.
End classes.

(** ** Subtyping *)

Section subty.
  Context `{!rust_haltGS CON Σ, rust_haltJ CON JUDG Σ, !Csem CON JUDG Σ,
    !Jsem JUDG (iProp Σ)}.
  Implicit Type δ : JUDG -n> iProp Σ.

  (** [subty]: Subtyping *)
  Definition subty δ {X Y} (T : ty CON Σ X) (U : ty CON Σ Y) (f : X → Y)
    : iProp Σ :=
    (* Ownership formula conversion *) □ (∀ t d xπ vl,
      ⟦ T.1 t d xπ vl ⟧ᶜ(δ) -∗ ⟦ U.1 t d (λ π, f (xπ π)) vl ⟧ᶜ(δ)) ∧
    (* Sharing formula conversion *) □ (∀ t d l α xπ,
      ⟦ T.2 t d l α xπ ⟧ᶜ(δ) -∗ ⟦ U.2 t d l α (λ π, f (xπ π)) ⟧ᶜ(δ)).

  (** [subty] is persistent *)
  #[export] Instance subty_persistent {δ X Y T U f} :
    Persistent (@subty δ X Y T U f).
  Proof. exact _. Qed.
  (** [subty] is proper *)
  #[export] Instance subty_proper {δ X Y} :
    Proper ((≡) ==> (≡) ==> (=) ==> (⊣⊢)) (@subty δ X Y).
  Proof.
    move=> ??[eqvO eqvS]??[eqvO' eqvS']??<-. unfold subty.
    repeat f_equiv; [exact (eqvO _ _ _ _)|exact (eqvO' _ _ _ _)|
      exact (eqvS _ _ _ _ _)|exact (eqvS' _ _ _ _ _)].
  Qed.
  (** [subty] is reflexive *)
  Lemma subty_refl {δ X T} : ⊢ @subty δ X _ T T id.
  Proof. iSplit; iModIntro; iIntros; iFrame. Qed.
  (** [subty] is transitive *)
  Lemma subty_trans {δ X Y Z T U V f g} :
    @subty δ X Y T U f -∗ @subty δ _ Z U V g -∗ @subty δ X Z T V (g ∘ f).
  Proof.
    iIntros "[#TUo #TUs][#UVo #UVs]". iSplit; iModIntro.
    - iIntros (????) "T". iApply "UVo". by iApply "TUo".
    - iIntros (?????) "T". iApply "UVs". by iApply "TUs".
  Qed.

  Context `{!rust_haltC CON, !rust_haltCS CON JUDG Σ}.

  (** [subty] over [sty] *)
  Lemma subty_sty {δ X Y T U f} :
    □ (∀ t d xπ vl, ⟦ T t d xπ vl ⟧ᶜ(δ) -∗ ⟦ U t d (λ π, f (xπ π)) vl ⟧ᶜ(δ)) ⊢
      @subty δ X Y (ty_sty T) (ty_sty U) f.
  Proof.
    iIntros "#sub". iSplit; [done|]=>/=. iIntros (?????) "!> (% & $ & ?)".
    by iApply "sub".
  Qed.
  (** [subty] over [pty] *)
  Lemma subty_pty {δ X Y T U f} :
    □ (∀ x vl, ⟦ T x vl ⟧ᶜ(δ) -∗ ⟦ U (f x) vl ⟧ᶜ(δ)) ⊢
      @subty δ X Y (ty_pty T) (ty_pty U) f.
  Proof.
    iIntros "#sub". iApply subty_sty=>/=. iIntros (????) "!> (% & -> & ?)".
    iExists _. iSplit; [done|]. by iApply "sub".
  Qed.
End subty.

Notation subtyd := (subty der).

(** ** Type context *)

(** Type context element *)
Variant etcx CON Σ : xty → Type :=
| Owned {X} (vl : list val) (T : ty CON Σ X) : etcx CON Σ X
| Frozen {X} (α : lft) (vl : list val) (T : ty CON Σ X) : etcx CON Σ X
| Lft (α : lft) : etcx CON Σ unitₓ.
Arguments Owned {_ _ _}. Arguments Frozen {_ _ _}. Arguments Lft {_ _}.
Infix "*◁" := Owned (at level 55).
Notation "vl *◁[† α ] T" := (Frozen α vl T)
  (at level 55, format "vl  *◁[† α ]  T").
Notation "v ◁ T" := (Owned [v] T) (at level 55, format "v  ◁  T").
Notation "v ◁[† α ] T" := (Frozen α [v] T)
  (at level 55, format "v  ◁[† α ]  T").
Notation "^[ α ]" := (Lft α) (format "^[ α ]").

(** Type context *)
Notation tcx CON Σ := (plist (etcx CON Σ)).
(** Predicate over [plist] *)
Notation pred Xl := (plist xpty_ty Xl → Prop).

Section tcx.
  Context `{!rust_haltGS CON Σ, rust_haltJ CON JUDG Σ, !Csem CON JUDG Σ,
    !Jsem JUDG (iProp Σ)}.

  (** Semantics of a type context element *)
  Definition sem_etcx {X} t (vT : etcx CON Σ X) : clair xty X → iProp Σ :=
    match vT with
    | vl *◁ T => λ xπ, ∃ d, ⟦ T.1 t d xπ vl ⟧ᶜ
    | vl *◁[†α] T => λ xπ, [†α] =[rust_halt_wsat]{⊤}=∗
        ∃ d xπ', proph_eqz xπ xπ' ∗ ⟦ T.1 t d xπ' vl ⟧ᶜ
    | ^[α] => λ _, ⌜α ≠ ⊤⌝ ∧ 1.[α]
    end%I.

  (** Semantics of a type context *)
  Fixpoint sem_tcx t {Xl} : tcx CON Σ Xl → plist _ Xl → iProp Σ :=
    match Xl with [] => λ _ _, True | _ :: _ =>
      λ '(eΓ, Γ)' '(xπ, xπl)', sem_etcx t eΓ xπ ∗ sem_tcx t Γ xπl end%I.
End tcx.

Section tcx.
  Context `{!rust_haltGS CON Σ, rust_haltJ CON JUDG Σ, !Csem CON JUDG Σ,
    !Jsem JUDG (iProp Σ)}.

  (** [sub]: Inclusion between type contexts *)
  Definition sub_def {Xl Yl} (α : lft) (Γi : tcx CON Σ Xl) (Γo : tcx CON Σ Yl)
    (pre : pred Yl → pred Xl) : iProp Σ :=
    □ ∀ q t postπ xπl,
      q.[α] -∗ na_own t ⊤ -∗ ⟨π, pre (postπ π) (app_clairs π xπl)⟩ -∗
        sem_tcx t Γi xπl =[rust_halt_wsat]{⊤}=∗ ∃ yπl,
        q.[α] ∗ na_own t ⊤ ∗ ⟨π, postπ π (app_clairs π yπl)⟩ ∗ sem_tcx t Γo yπl.
  Lemma sub_aux : seal (@sub_def). Proof. by eexists. Qed.
  Definition sub {Xl Yl} := sub_aux.(unseal) Xl Yl.
  Lemma sub_unseal : @sub = @sub_def. Proof. exact: seal_eq. Qed.
  (** [sub] is persistent *)
  #[export] Instance sub_persistent {Xl Yl α Γi Γo pre} :
    Persistent (@sub Xl Yl α Γi Γo pre).
  Proof. rewrite sub_unseal. exact _. Qed.

  (** [type]: Typing judgment over an expression, ensuring termination *)
  Definition type_def {Xl Yl} (α : lft) (Γi : tcx CON Σ Xl) (e : expr)
    (Γo : val → tcx CON Σ Yl) (pre : pred Yl → pred Xl)
    : iProp Σ :=
    □ ∀ q t postπ xπl,
      q.[α] -∗ na_own t ⊤ -∗ ⟨π, pre (postπ π) (app_clairs π xπl)⟩ -∗
      sem_tcx t Γi xπl -∗ WP[rust_halt_wsat] e [{ v, |=[rust_halt_wsat]{⊤}=>
        ∃ yπl, q.[α] ∗ na_own t ⊤ ∗ ⟨π, postπ π (app_clairs π yπl)⟩ ∗
          sem_tcx t (Γo v) yπl }].
  Lemma type_aux : seal (@type_def). Proof. by eexists. Qed.
  Definition type {Xl Yl} := type_aux.(unseal) Xl Yl.
  Lemma type_unseal : @type = @type_def. Proof. exact: seal_eq. Qed.
  (** [type] is persistent *)
  #[export] Instance type_persistent {Xl Yl α Γi e Γo pre} :
    Persistent (@type Xl Yl α Γi e Γo pre).
  Proof. rewrite type_unseal. exact _. Qed.

  Context `{!rust_haltC CON, !rust_haltCS CON JUDG Σ}.

  (** [sub] is reflexive and transitive *)
  Lemma sub_refl {Xl α Γ} : ⊢ @sub Xl _ α Γ Γ id.
  Proof. rewrite sub_unseal. iIntros (????) "!>/= $ $ ? $ //". Qed.
  Lemma sub_trans {Xl Yl Zl α Γ Γ' Γ'' pre pre'} :
    @sub Xl Yl α Γ Γ' pre -∗ @sub _ Zl α Γ' Γ'' pre' -∗
      sub α Γ Γ'' (pre ∘ pre').
  Proof.
    rewrite sub_unseal. iIntros "#sub #sub' !>" (????) "α t pre Γ".
    iMod ("sub" with "α t pre Γ") as (?) "(α & t & pre & Γ')".
    iApply ("sub'" with "α t pre Γ'").
  Qed.
  (** Modify the predicate transformer of [sub] *)
  Lemma sub_pre {Xl Yl α Γi Γo pre pre'} :
    (∀ post xl, pre' post xl → pre post xl) →
    @sub Xl Yl α Γi Γo pre ⊢ @sub Xl Yl α Γi Γo pre'.
  Proof.
    rewrite sub_unseal=> to. iIntros "#sub !>" (????) "α t #pre Γ".
    iApply ("sub" with "α t [] Γ"). iApply (proph_obs_impl with "pre")=> ?.
    apply to.
  Qed.
  (** Modify the lifetime of [sub] *)
  Lemma sub_lft {Xl Yl α β Γi Γo pre} :
    β ⊑□ α -∗ @sub Xl Yl α Γi Γo pre -∗ sub β Γi Γo pre.
  Proof.
    rewrite sub_unseal. iIntros "#⊑ #ty !>" (????) "β t pre Γi".
    iMod (lft_sincl_live_acc with "⊑ β") as (?) "[α →β]".
    iMod ("ty" with "α t pre Γi") as (?) "[α $]". iModIntro. by iApply "→β".
  Qed.
  (** Frame the head in [sub] *)
  Lemma sub_frame_hd {X Yl Zl α vT Γi Γo pre} :
    @sub Yl Zl α Γi Γo pre ⊢ @sub (X :: _) _ α (vT ᵖ:: Γi) (vT ᵖ:: Γo)
      (λ post '(x, yl)', pre (λ zl, post (x, zl)') yl).
  Proof.
    rewrite sub_unseal. iIntros "#sub !>" (????) "/= α t pre [vT Γi]".
    iMod ("sub" with "α t pre Γi") as (yπl) "($ & $ & ? & ?)". iExists (_,_)'.
    by iFrame.
  Qed.

  (** Modify the input type context of [type] *)
  Lemma type_in {Xl' Xl Yl α Γi' Γi e Γo prei pre} :
    @sub Xl' _ α Γi' Γi prei -∗ @type Xl Yl α Γi e Γo pre -∗
      type α Γi' e Γo (prei ∘ pre).
  Proof.
    rewrite sub_unseal type_unseal.
    iIntros "#sub #type !>" (????) "/= α t pre Γi'".
    iMod ("sub" with "α t pre Γi'") as (?) "(α & t & pre & Γi)".
    iApply ("type" with "α t pre Γi").
  Qed.
  (** Modify the output type context of [type] *)
  Lemma type_out {Xl Yl Yl' α Γi e Γo Γo' pre preo} :
    @type Xl Yl α Γi e Γo pre -∗ (∀ v, @sub Yl Yl' α (Γo v) (Γo' v) preo) -∗
      type α Γi e Γo' (pre ∘ preo).
  Proof.
    rewrite sub_unseal type_unseal.
    iIntros "#type #sub !>" (????) "/= α t pre Γi".
    iDestruct ("type" with "α t pre Γi") as "twp". iApply (twp_wand with "twp").
    iIntros (?) ">(% & α & t & pre & Γo)". iApply ("sub" with "α t pre Γo").
  Qed.
  (** Modify the predicate transformer of [type] *)
  Lemma type_pre {Xl Yl α Γi e Γo pre pre'} :
    (∀ post xl, pre' post xl → pre post xl) →
    @type Xl Yl α Γi e Γo pre ⊢ @type Xl Yl α Γi e Γo pre'.
  Proof.
    rewrite type_unseal=> to. iIntros "#type !>" (????) "α t #pre Γi".
    iApply ("type" with "α t [] Γi"). iApply (proph_obs_impl with "pre")=> ?.
    apply to.
  Qed.
  (** Modify the lifetime of [type] *)
  Lemma type_lft {Xl Yl α β Γi e Γo pre} :
    β ⊑□ α -∗ @type Xl Yl α Γi e Γo pre -∗ @type Xl Yl β Γi e Γo pre.
  Proof.
    rewrite type_unseal. iIntros "#⊑ #type !>" (????) "β t pre Γi".
    iMod (lft_sincl_live_acc with "⊑ β") as (?) "[α →β]".
    iDestruct ("type" with "α t pre Γi") as "twp". iApply (twp_wand with "twp").
    iIntros (?) ">(% & α & $) !>". by iApply "→β".
  Qed.
  (** Frame the head in [type] *)
  Lemma type_frame_hd {X Yl Zl α vT Γi e Γo pre} :
    @type Yl Zl α Γi e Γo pre ⊢
      @type (X :: _) _ α (vT ᵖ:: Γi) e (λ v, vT ᵖ:: Γo v)
        (λ post '(x, yl)', pre (λ zl, post (x, zl)') yl).
  Proof.
    rewrite type_unseal. iIntros "#type !>" (????) "/= α t pre [vT Γi]".
    iDestruct ("type" with "α t pre Γi") as "twp". iApply (twp_wand with "twp").
    iIntros (?) ">(% & $ & $ & ? & ?) !>". iExists (_,_)'. by iFrame.
  Qed.
End tcx.
Arguments type {_ _ _ _ _ _ _ _ _} _ _ _%_E _ _.
