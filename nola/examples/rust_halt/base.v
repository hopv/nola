(** * Basics *)

From iris.proofmode Require Export environments.
From nola.util Require Export fn.
From nola.iris Require Export cif inv_deriv na_inv_deriv store_deriv
  pborrow_deriv fborrow.
From nola.examples Require Export xty.
From nola.rust_lang Require Export proofmode notation.
Export ProdNotation PlistNotation ProeqvNotation FunPRNotation BigSepPLNotation
  ModwNotation WpwNotation iPropAppNotation ProphNotation LftNotation
  CsemNotation XtyNotation.
Open Scope nat_scope.

Implicit Type Σ : gFunctors.

(** ** Notation *)

(** For prophecies *)
Notation prasn := (prasn xty).
Notation clair A := (clair xty A).

(** Value for [list xty] *)
Notation xlist := (plist xpty_ty).
(** Predicate over [xlist] *)
Notation xpred Xl := (xlist Xl → Prop).

(** Thread id *)
Notation thread_id := na_inv_pool_name.

(** ** Ghost state *)

Class rust_haltGS CON Σ : Type := RustHaltGS {
  rust_haltGS_lrust :: lrustGS_gen HasNoLc Σ;
  rust_haltGS_inv :: inv'GS (cifOF CON) Σ;
  rust_haltGS_na_inv :: na_invG Σ;
  rust_haltGS_dinv :: dinvGS (cifOF CON) Σ;
  rust_haltGS_token :: tokenG Σ;
  rust_haltGS_borrow :: borrowGS (cifOF CON) Σ;
  rust_haltGS_proph :: prophGS xty Σ;
  rust_haltGS_proph_ag :: proph_agG nat xty Σ;
  rust_haltGS_fborrow :: fborrowGS (cifOF CON) Σ;
}.

(** ** Custom constructors *)

(** [customCT]: Constructor *)
Variant customCT_id := .
Variant customCT_sel :=
| (** Points-to token *) cifs_pointsto (l : loc) (q : Qp) (v : val)
| (** Prophecy token *) cifs_proph_tok (ξ : aprvar xty) (q : Qp).
Definition customCT := Cifcon customCT_id customCT_sel
  (λ _, Empty_set) (λ _, Empty_set) (λ _, unitO) _.
(** [customC]: [customCT] registered *)
Notation customC := (inC customCT).
Section customC.
  Context `{!customC CON} {Σ}.
  (** [cif_pointsto]: Points-to token *)
  Definition cif_pointsto l q v : cif CON Σ :=
    cif_in customCT (cifs_pointsto l q v) nullary nullary ().
  (** [cif_proph_tok]: Prophecy token *)
  Definition cif_proph_tok ξ q : cif CON Σ :=
    cif_in customCT (cifs_proph_tok ξ q) nullary nullary ().

  Context `{!rust_haltGS TY Σ}.
  (** Semantics of [customCT] *)
  Definition customCT_sem (s : customCT_sel) : iProp Σ :=
    match s with
    | cifs_pointsto l q v => l ↦{q} v
    | cifs_proph_tok ξ q => q:[ξ]
    end.
  #[export] Program Instance customCT_ecsem {JUDG}
    : Ecsem customCT CON JUDG Σ :=
    ECSEM (λ _ _ s _ _ _, customCT_sem s) _.
  Next Obligation. done. Qed.
End customC.
(** [customC] semantics registered *)
Notation customCS := (inCS customCT).
(** Notation *)
Notation "l ↦{ q } v" := (cif_pointsto l q v) : cif_scope.
Notation "l ↦ v" := (cif_pointsto l 1 v) : cif_scope.
Notation "q :[ ξ ]" := (cif_proph_tok ξ q) : cif_scope.

Section customC.
  Context `{!customC CON, !Csem CON JUDG Σ, !rust_haltGS CON Σ,
    !customCS CON JUDG Σ}.

  (** Reify tokens *)
  #[export] Program Instance pointsto_as_cif {l q v} :
    AsCif CON (λ _, l ↦{q} v)%I := AS_CIF (l ↦{q} v) _.
  Next Obligation. move=>/= >. by rewrite sem_cif_in. Qed.
  #[export] Program Instance proph_tok_as_cif {q ξ} :
    AsCif CON (λ _, q:[ξ])%I := AS_CIF q:[ξ] _.
  Next Obligation. move=>/= >. by rewrite sem_cif_in. Qed.
End customC.

(** ** Constructor and judgment constraint *)

(** Constructor constraint *)
Class rust_haltC CON : Type := RUST_HALT_C {
  rust_haltC_inv :: invC CON;
  rust_haltC_na_inv :: na_invC CON;
  rust_haltC_store :: storeC CON;
  rust_haltC_borrow :: borrowC CON;
  rust_haltC_proph_ag :: proph_agC nat xty CON;
  rust_haltC_pborrow :: pborrowC nat xty CON;
  rust_haltC_custom :: customC CON;
}.

(** Judgment constraint *)
Class rust_haltJ CON JUDG Σ : Type := RUST_HALT_J {
  rust_haltJ_inv :: invJ (cifO CON Σ) JUDG;
  rust_haltJ_na_inv :: na_invJ (cifO CON Σ) JUDG;
  rust_haltJ_store :: storeJ (cifO CON Σ) JUDG;
  rust_haltJ_bupd :: bupdJ (cifOF CON $oi Σ) JUDG;
}.

(** Constructor semantics constraint *)
Class rust_haltCS CON JUDG Σ `{!rust_haltGS CON Σ, !rust_haltC CON}
  `{!rust_haltJ CON JUDG Σ, !Csem CON JUDG Σ} : Prop := RUST_HALT_CS {
  rust_haltCS_inv :: invCS CON JUDG Σ;
  rust_haltCS_na_inv :: na_invCS CON JUDG Σ;
  rust_haltCS_store :: storeCS CON JUDG Σ;
  rust_haltCS_borrow :: borrowCS CON JUDG Σ;
  rust_haltCS_proph_ag :: proph_agCS nat xty CON JUDG Σ;
  rust_haltCS_pborrow :: pborrowCS nat xty CON JUDG Σ;
  rust_haltCS_custom :: customCS CON JUDG Σ;
}.

(** Judgment semantics constraint *)
Class rust_haltJS CON JUDG Σ `{!rust_haltGS CON Σ, !rust_haltC CON}
  `{!rust_haltJ CON JUDG Σ, !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ)} : Prop :=
  RUST_HALT_JS {
  rust_haltJS_inv :: invJS (cifOF CON) JUDG Σ;
  rust_haltJS_na_inv :: na_invJS CON JUDG Σ;
  rust_haltJS_store :: storeJS (cifOF CON) JUDG Σ;
  rust_haltJS_bupd :: bupdJS (cifO CON Σ) JUDG (iProp Σ);
}.

(** ** World satisfaction *)

(** Modality for [borrow_wsat] *)
Definition borrowM `{!rust_haltGS CON Σ, !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ)}
  : iProp Σ → iProp Σ :=
  fupdw ⊤ ⊤ (inv_wsat ⟦⟧ᶜ ∗ dinv_wsat ⟦⟧ᶜ).
(** World satisfaction *)
Definition rust_halt_wsat
  `{!rust_haltGS CON Σ, !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ)} : iProp Σ :=
  inv_wsat ⟦⟧ᶜ ∗ dinv_wsat ⟦⟧ᶜ ∗ borrow_wsat borrowM ⟦⟧ᶜ ∗ fborrow_wsat.

(** ** Lifetime inclusion *)

(** [LftIncl]: Type class for lifetime inclusion *)
Class LftIncl (κ α : lft) : Prop :=
  lft_incl' : κ ⊑ α.
Hint Mode LftIncl ! ! : typeclass_instances.

(** Trivial matches *)
#[export] Instance lft_incl'_top {κ} : LftIncl κ ⊤ | 2.
Proof. exact lft_incl_top. Qed.
#[export] Instance lft_incl'_refl {κ} : LftIncl κ κ | 2.
Proof. exact: lft_incl_refl. Qed.
(** Decompose the right-hand side *)
#[export] Instance lft_incl'_meet_intro `{!LftIncl κ α, !LftIncl κ β} :
  LftIncl κ (α ⊓ β) | 5.
Proof. exact: lft_incl_meet_intro. Qed.
(** Decompose the left-hand side *)
#[export] Instance lft_incl'_meet_by_l `{!LftIncl κ α} {κ'} :
  LftIncl (κ ⊓ κ') α | 30.
Proof. unfold LftIncl. etrans; [exact lft_incl_meet_l|done]. Qed.
#[export] Instance lft_incl'_meet_by_r `{!LftIncl κ' α} {κ} :
  LftIncl (κ ⊓ κ') α | 30.
Proof. unfold LftIncl. etrans; [exact lft_incl_meet_r|done]. Qed.

(** [LftIncl] is transitive *)
#[export] Instance lft_incl'_trans : Transitive LftIncl.
Proof. exact: lft_incl_trans. Qed.

Lemma lft_incl'_live_acc `{!lftG Σ} α `(!LftIncl κ α) {q} :
  q.[κ] ⊢ ∃ r, r.[α] ∗ (r.[α] -∗ q.[κ]).
Proof. exact: lft_incl_live_acc. Qed.

(** ** Utility on the language *)

Section lrust.
  Context `{!lrustGS_gen hlc Σ}.

  (** Fuse points-to tokens *)
  Lemma heap_pointsto_vec_fuse {l q vl r wl} :
    l ↦∗{q} vl -∗ (l +ₗ length vl) ↦∗{r} wl -∗ ∃ s, l ↦∗{s} (vl ++ wl) ∗
      (l ↦∗{s} (vl ++ wl) -∗ l ↦∗{q} vl ∗ (l +ₗ length vl) ↦∗{r} wl).
  Proof.
    case (Qp.lower_bound q r)=> s[?[?[->->]]]. iIntros "[↦ ↦'] [↦+ ↦+']".
    iExists s. rewrite heap_pointsto_vec_app. iFrame "↦ ↦+". iIntros "[↦ ↦+]".
    iCombine "↦ ↦'" as "$". iCombine "↦+ ↦+'" as "$".
  Qed.
  Lemma heap_pointsto_just_vec_fuse {l q v r wl} :
    l ↦{q} v -∗ (l +ₗ 1) ↦∗{r} wl -∗ ∃ s, l ↦∗{s} (v :: wl) ∗
      (l ↦∗{s} (v :: wl) -∗ l ↦{q} v ∗ (l +ₗ 1) ↦∗{r} wl).
  Proof.
    setoid_rewrite <-heap_pointsto_vec_singleton. exact: heap_pointsto_vec_fuse.
  Qed.
  Lemma heap_pointsto_vec_just_fuse {l q vl r w} :
    l ↦∗{q} vl -∗ (l +ₗ length vl) ↦{r} w -∗ ∃ s, l ↦∗{s} (vl ++ [w]) ∗
      (l ↦∗{s} (vl ++ [w]) -∗ l ↦∗{q} vl ∗ (l +ₗ length vl) ↦{r} w).
  Proof.
    setoid_rewrite <-heap_pointsto_vec_singleton. exact: heap_pointsto_vec_fuse.
  Qed.
End lrust.

(** ** Shared borrows *)

(** [spointsto]: Shared borrow over a points-to token *)
Definition spointsto `{!rust_haltGS CON Σ, !rust_haltC CON} α l v
  : iProp Σ := fbor_tok α (λ q, l ↦{q} v)%cif.
Notation "l ↦ˢ[ α ] v" := (spointsto α l v)
 (at level 20, format "l  ↦ˢ[ α ]  v") : bi_scope.

(** [spointsto_vec]: Iterative [spointsto] *)
Definition spointsto_vec `{!rust_haltGS CON Σ, !rust_haltC CON} α l vl :=
  ([∗ list] k ↦ v ∈ vl, (l +ₗ k) ↦ˢ[α] v)%I.
Notation "l ↦∗ˢ[ α ] vl" := (spointsto_vec α l vl)
  (at level 20, format "l  ↦∗ˢ[ α ]  vl") : bi_scope.

(** [sproph_tok]: Shared borrow over a prophecy token *)
Definition sproph_tok `{!rust_haltGS CON Σ, !rust_haltC CON} α ξ
  : iProp Σ := fbor_tok α (λ q, q:[ξ])%cif.
Notation "[ ξ ]:ˢ[ α ]" := (sproph_tok α ξ) (format "[ ξ ]:ˢ[ α ]") : bi_scope.

(** [sproph_toks]: Iterative [sproph_tok] *)
Notation sproph_toks α ξl := ([∗ list] ξ ∈ ξl, [ξ]:ˢ[α])%I.
Notation "[ ξl ]:∗ˢ[ α ]" := (sproph_toks α ξl) (format "[ ξl ]:∗ˢ[ α ]")
  : bi_scope.

Section fbor_tok.
  Context `{!rust_haltGS CON Σ, !rust_haltC CON}.

  (** [spointsto] is timeless *)
  #[export] Instance spointsto_timeless {α l v} : Timeless (l ↦ˢ[α] v).
  Proof. exact _. Qed.
  #[export] Instance spointsto_vec_timeless {α l vl} : Timeless (l ↦∗ˢ[α] vl).
  Proof. exact _. Qed.
  (** [sproph_tok] is timeless *)
  #[export] Instance sproph_tok_timeless {α ξ} : Timeless [ξ]:ˢ[α].
  Proof. exact _. Qed.
  #[export] Instance sproph_toks_timeless {α ξl} : Timeless [ξl]:∗ˢ[α].
  Proof. exact _. Qed.

  (** [spointsto_vec] over nil *)
  Lemma spointsto_vec_nil {α l} : l ↦∗ˢ[α] [] ⊣⊢ True.
  Proof. done. Qed.
  (** [spointsto_vec] over cons *)
  Lemma spointsto_vec_cons {α l v vl} :
    l ↦∗ˢ[α] (v :: vl) ⊣⊢ l ↦ˢ[α] v ∗ (l +ₗ 1) ↦∗ˢ[α] vl.
  Proof.
    rewrite /spointsto_vec /= shift_loc_0. do 4 f_equiv. by rewrite shift_loc_S.
  Qed.
  (** [spointsto_vec] over [++] *)
  Lemma spointsto_vec_app {α l vl vl'} :
    l ↦∗ˢ[α] (vl ++ vl') ⊣⊢ l ↦∗ˢ[α] vl ∗ (l +ₗ length vl) ↦∗ˢ[α] vl'.
  Proof.
    rewrite /spointsto_vec big_sepL_app. do 4 f_equiv.
    by rewrite shift_loc_assoc_nat.
  Qed.

  Context `{!rust_haltJ CON JUDG Σ, !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ),
    !rust_haltCS CON JUDG Σ}.

  (** Access [spointsto] *)
  Lemma spointsto_acc {α l v r} :
    r.[α] -∗ l ↦ˢ[α] v =[rust_halt_wsat]{⊤}=∗ ∃ q,
      l ↦{q} v ∗ (l ↦{q} v =[rust_halt_wsat]=∗ r.[α]).
  Proof.
    iIntros "α ↦".
    iMod (fbor_tok_acc (M:=borrowM) with "α ↦") as (?) "/=[↦ →α]".
    { move=>/= ??. by rewrite !sem_cif_in /= heap_pointsto_fractional. }
    rewrite sem_cif_in /=. iFrame "↦". iIntros "!> ↦". by iMod ("→α" with "↦").
  Qed.

  (** Access [spointsto_vec] *)
  Lemma spointsto_vec_acc {α l vl r} :
    r.[α] -∗ l ↦∗ˢ[α] vl =[rust_halt_wsat]{⊤}=∗ ∃ q,
      l ↦∗{q} vl ∗ (l ↦∗{q} vl =[rust_halt_wsat]=∗ r.[α]).
  Proof.
    move: l r. elim: vl=>//=.
    { unfold heap_pointsto_vec=>/=. iIntros (??) "$ _ !>". by iExists 1%Qp. }
    move=> v vl IH l ?. rewrite spointsto_vec_cons. iIntros "[α α'] [↦ ↦s]".
    iMod (spointsto_acc with "α ↦") as (?) "[↦ →α]".
    iMod (IH with "α' ↦s") as (?) "[↦s →α']". iModIntro.
    iDestruct (heap_pointsto_just_vec_fuse with "↦ ↦s") as (?) "[$ →↦↦s]".
    iIntros "↦↦s". iDestruct ("→↦↦s" with "↦↦s") as "[↦ ↦s]".
    iMod ("→α" with "↦") as "$". by iApply "→α'".
  Qed.

  (** Allocate [spointsto] *)
  Lemma spointsto_alloc {α l v r} :
    r.[α] -∗ bor_tok α (▷ l ↦ v)%cif =[rust_halt_wsat]{⊤}=∗ r.[α] ∗ l ↦ˢ[α] v.
  Proof.
    iIntros "α b".
    iMod (bor_tok_open (M:=borrowM) with "α b") as "/=[o >↦]".
    iMod (obor_tok_subdiv (FML:=cifOF _) (M:=borrowM) (sm:=⟦⟧ᶜ) [_ ↦ _]%cif
      with "[] o [↦] []") as "($ & _ & b & _)"=>/=.
    { iApply lft_sincl_refl. } { rewrite sem_cif_in /=. iFrame. }
    { rewrite sem_cif_in /=. by iIntros "_ ($ & _)". }
    by iMod (fbor_tok_alloc (FML:=cifOF _) (λ q, l ↦{q} v)%cif with "b") as "$".
  Qed.

  (** Allocate [spointsto_vec] *)
  Lemma spointsto_vec_alloc {α l vl r} :
    r.[α] -∗ bor_tok α (▷ l ↦∗ vl)%cif =[rust_halt_wsat]{⊤}=∗
      r.[α] ∗ l ↦∗ˢ[α] vl.
  Proof.
    move: l r. elim: vl=>/=.
    { iIntros (??) "$ _". by rewrite spointsto_vec_nil. }
    iIntros (v vl IH l ?) "α b".
    iMod (bor_tok_open (M:=borrowM) with "α b") as "/=[o ↦s]".
    rewrite {2}heap_pointsto_vec_cons. iDestruct "↦s" as "[>↦ ↦s]".
    iMod (obor_tok_subdiv (FML:=cifOF _) (M:=borrowM) (sm:=⟦⟧ᶜ) [_ ↦ _; ▷ _]%cif
      with "[] o [↦ $↦s] []") as "(α & _ & b & b' & _)"=>/=.
    { iApply lft_sincl_refl. } { rewrite sem_cif_in /=. iFrame. }
    { rewrite heap_pointsto_vec_cons sem_cif_in /=.
      by iIntros "_ ($ & $ & _)". }
    rewrite spointsto_vec_cons. iMod (IH with "α b'") as "[$$]".
    by iMod (fbor_tok_alloc (FML:=cifOF _) (λ q, l ↦{q} v)%cif with "b")
      as "$".
  Qed.

  (** Access [sproph_tok] *)
  Lemma sproph_tok_acc {α ξ r} :
    r.[α] -∗ [ξ]:ˢ[α] =[rust_halt_wsat]{⊤}=∗ ∃ q,
      q:[ξ] ∗ (q:[ξ] =[rust_halt_wsat]=∗ r.[α]).
  Proof.
    iIntros "α ξ".
    iMod (fbor_tok_acc (M:=borrowM) with "α ξ") as (?) "/=[ξ →α]".
    { move=>/= ??. by rewrite !sem_cif_in /= proph_tok_fractional. }
    rewrite sem_cif_in /=. iFrame "ξ". iIntros "!> ξ". by iMod ("→α" with "ξ").
  Qed.

  (** Access [sproph_toks] *)
  Lemma sproph_toks_acc {α ξl r} :
    r.[α] -∗ [ξl]:∗ˢ[α] =[rust_halt_wsat]{⊤}=∗ ∃ q,
      q:∗[ξl] ∗ (q:∗[ξl] =[rust_halt_wsat]=∗ r.[α]).
  Proof.
    move: r. elim: ξl=>/=. { iIntros (?) "$ _ !>". by iExists 1%Qp. }
    iIntros (ξ ξl IH ?) "[α α'] [ξ ξl]".
    iMod (sproph_tok_acc with "α ξ") as (?) "[ξ →α]".
    iMod (IH with "α' ξl") as (?) "[ξl →α']". iModIntro.
    iDestruct (proph_tok_toks_fuse with "ξ ξl") as (?) "/=[$ →ξξl]".
    iIntros "ξξl". iDestruct ("→ξξl" with "ξξl") as "[ξ ξl]".
    iMod ("→α" with "ξ") as "$". by iApply "→α'".
  Qed.

  (** Allocate [sproph_tok] *)
  Lemma sproph_tok_alloc {α ξ r} :
    r.[α] -∗ bor_tok α (▷ 1:[ξ])%cif =[rust_halt_wsat]{⊤}=∗ r.[α] ∗ [ξ]:ˢ[α].
  Proof.
    iIntros "α b".
    iMod (bor_tok_open (M:=borrowM) with "α b") as "/=[o >ξ]".
    iMod (obor_tok_subdiv (FML:=cifOF _) (M:=borrowM) (sm:=⟦⟧ᶜ) [1:[ξ]]%cif
      with "[] o [ξ] []") as "($ & _ & b & _)"=>/=.
    { iApply lft_sincl_refl. } { rewrite sem_cif_in /=. iFrame. }
    { rewrite sem_cif_in /=. by iIntros "_ ($ & _)". }
    by iMod (fbor_tok_alloc (FML:=cifOF _) (λ q, q:[ξ])%cif with "b") as "$".
  Qed.

  (** Allocate [sproph_toks] *)
  Lemma sproph_toks_alloc {α ξl r} :
    r.[α] -∗ bor_tok α (▷ 1:∗[ξl])%cif =[rust_halt_wsat]{⊤}=∗
      r.[α] ∗ [ξl]:∗ˢ[α].
  Proof.
    move: r. elim: ξl=>/=; [by iIntros (?) "$ _"|]. iIntros (ξ ξl IH ?) "α b".
    iMod (bor_tok_open (M:=borrowM) with "α b") as "/=[o [>ξ ξl]]".
    iMod (obor_tok_subdiv (FML:=cifOF _) (M:=borrowM) (sm:=⟦⟧ᶜ) [_:[_]; ▷ _]%cif
      with "[] o [ξ $ξl] []") as "(α & _ & b & b' & _)"=>/=.
    { iApply lft_sincl_refl. } { rewrite sem_cif_in /=. iFrame. }
    { rewrite sem_cif_in /=. by iIntros "_ ($ & $ & _)". }
    iMod (IH with "α b'") as "[$$]".
    by iMod (fbor_tok_alloc (FML:=cifOF _) (λ q, q:[ξ])%cif with "b") as "$".
  Qed.
End fbor_tok.
