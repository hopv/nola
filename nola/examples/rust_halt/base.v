(** * Basics *)

From iris.proofmode Require Export environments.
From nola.iris Require Export cif inv_deriv na_inv_deriv store_deriv
  pborrow_deriv fborrow.
From nola.examples Require Export xty.
From nola.rust_lang Require Export proofmode adequacy notation.
Export ProdNotation PlistNotation BigSepPLNotation ModwNotation WpwNotation
  iPropAppNotation ProphNotation LftNotation CsemNotation FunPRNotation.
Open Scope nat_scope.

(** ** Notation *)

(** Clairvoyant value *)
Notation clair A := (clair xty A).
(** List of clairvoyant values *)
Notation clairs := (plist (A:=xty) (λ X, clair X)).

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
Class rust_haltGpreS CON Σ : Type := RustHaltGpreS {
  rust_haltGpreS_lrust :: lrustGpreS Σ;
  rust_haltGoreS_inv :: inv'GpreS (cifOF CON) Σ;
  rust_haltGpreS_na_inv :: na_invG Σ;
  rust_haltGpreS_dinv :: dinvGpreS (cifOF CON) Σ;
  rust_haltGpreS_token :: tokenG Σ;
  rust_haltGpreS_borrow :: borrowGpreS (cifOF CON) Σ;
  rust_haltGpreS_proph :: prophGpreS xty Σ;
  rust_haltGpreS_proph_ag :: proph_agG nat xty Σ;
  rust_haltGpreS_fborrow :: fborrowGpreS (cifOF CON) Σ;
}.
Definition rust_haltΣ CON : gFunctors :=
  #[lrustΣ; inv'Σ (cifOF CON); na_invΣ; dinvΣ (cifOF CON); tokenΣ;
    borrowΣ (cifOF CON); prophΣ xty; proph_agΣ nat xty; fborrowΣ (cifOF CON)].
Global Instance subG_rust_haltGpreS `{!subG (rust_haltΣ CON) Σ} :
  rust_haltGpreS CON Σ.
Proof. solve_inG. Qed.

(** ** Constructor and judgment constraint *)

(** Constructor constraint *)
Class rust_haltC CON : Type := RUST_HALT_C {
  rust_haltC_inv :: invC CON;
  rust_haltC_na_inv :: na_invC CON;
  rust_haltC_store :: storeC CON;
  rust_haltC_borrow :: borrowC CON;
  rust_haltC_proph_ag :: proph_agC nat xty CON;
  rust_haltC_pborrow :: pborrowC nat xty CON;
  rust_haltC_fbor :: fborC CON;
}.

(** Judgment constraint *)
Class rust_haltJ CON JUDG Σ : Type := RUST_HALT_J {
  rust_haltJ_inv :: invJ (cifO CON Σ) JUDG;
  rust_haltJ_na_inv :: na_invJ (cifO CON Σ) JUDG;
  rust_haltJ_dinv :: dinvJ (cifO CON Σ) JUDG;
  rust_haltJ_store :: storeJ (cifO CON Σ) JUDG;
  rust_haltJ_bupd :: bupdJ (cifOF CON $oi Σ) JUDG;
  rust_haltJ_fborrow :: fborrowJ (cifOF CON) JUDG Σ;
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
  rust_haltCS_fbor :: fborCS CON JUDG Σ;
}.

(** Judgment semantics constraint *)
Class rust_haltJS CON JUDG Σ `{!rust_haltGS CON Σ, !rust_haltC CON}
  `{!rust_haltJ CON JUDG Σ, !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ)} : Prop :=
  RUST_HALT_JS {
  rust_haltJS_inv :: invJS (cifOF CON) JUDG Σ;
  rust_haltJS_na_inv :: na_invJS CON JUDG Σ;
  rust_haltJS_dinv :: dinvJS (cifOF CON) JUDG Σ;
  rust_haltJS_store :: storeJS (cifOF CON) JUDG Σ;
  rust_haltJS_bupd :: bupdJS (cifO CON Σ) JUDG (iProp Σ);
  rust_haltJS_fborrow :: fborrowJS (cifOF CON) JUDG Σ;
}.

(** ** World satisfaction *)

(** Modality for [borrow_wsat] *)
Definition borrowM `{!rust_haltGS CON Σ, !rust_haltJ CON JUDG Σ}
  `{!Csem CON JUDG Σ, !Jsem JUDG (iProp Σ)} : iProp Σ → iProp Σ :=
  fupdw ⊤ ⊤ (inv_wsat ⟦⟧ᶜ ∗ dinv_wsat ⟦⟧ᶜ).
(** World satisfaction *)
Definition rust_halt_wsat `{!rust_haltGS CON Σ, !rust_haltJ CON JUDG Σ}
  `{!Csem CON JUDG Σ, !Jsem JUDG (iProp Σ)} : iProp Σ :=
  inv_wsat ⟦⟧ᶜ ∗ dinv_wsat ⟦⟧ᶜ ∗ borrow_wsat borrowM ⟦⟧ᶜ ∗
    fborrow_wsat (JUDG:=JUDG) der.

(** ** Shared borrows *)

(** [spointsto]: Shared borrow over a points-to token *)
Definition spointsto `{!rust_haltGS CON Σ, !rust_haltJ CON JUDG Σ} δ α l v
  : iProp Σ := fbor δ α (λ q, ▷ l ↦{q} v)%cif.
Notation "l ↦ˢ[ α ; δ ] v" := (spointsto δ α l v)
 (at level 20, format "l  ↦ˢ[ α ; δ ]  v") : bi_scope.
Notation spointstod := (spointsto der).
Notation "l ↦ˢ[ α ] v" := (spointstod α l v)
 (at level 20, format "l  ↦ˢ[ α ]  v") : bi_scope.

(** [spointsto_vec]: Iterative [spointsto] *)
Definition spointsto_vec `{!rust_haltGS CON Σ, !rust_haltJ CON JUDG Σ}
  δ α l vl :=
  ([∗ list] k ↦ v ∈ vl, (l +ₗ k) ↦ˢ[α; δ] v)%I.
Notation "l ↦∗ˢ[ α ; δ ] vl" := (spointsto_vec δ α l vl)
  (at level 20, format "l  ↦∗ˢ[ α ; δ ]  vl") : bi_scope.
Notation spointsto_vecd α l vl := (spointsto_vec der α l vl).
Notation "l ↦∗ˢ[ α ] vl" := (spointsto_vecd α l vl)
  (at level 20, format "l  ↦∗ˢ[ α ]  vl") : bi_scope.

(** [sproph_tok]: Shared borrow over a prophecy token *)
Definition sproph_tok `{!rust_haltGS CON Σ, !rust_haltJ CON JUDG Σ} δ α ξ
  : iProp Σ := fbor δ α (λ q, ▷ q:[ξ])%cif.
Notation "[ ξ ]:ˢ[ α ; δ ]" := (sproph_tok δ α ξ) (format "[ ξ ]:ˢ[ α ; δ ]")
  : bi_scope.
Notation sproph_tokd := (sproph_tok der).
Notation "[ ξ ]:ˢ[ α ]" := (sproph_tokd α ξ) (format "[ ξ ]:ˢ[ α ]")
  : bi_scope.

(** [sproph_toks]: Iterative [sproph_tok] *)
Notation sproph_toks δ α ξl := ([∗ list] ξ ∈ ξl, [ξ]:ˢ[α;δ])%I.
Notation "[ ξl ]:∗ˢ[ α ; δ ]" := (sproph_toks δ α ξl)
  (format "[ ξl ]:∗ˢ[ α ; δ ]") : bi_scope.
Notation sproph_toksd α ξl := (sproph_toks der α ξl).
Notation "[ ξl ]:∗ˢ[ α ]" := (sproph_toksd α ξl) (format "[ ξl ]:∗ˢ[ α ]")
  : bi_scope.

(** Formula for [spointsto] *)
Definition cif_spointsto `{!rust_haltGS CON Σ, !rust_haltC CON}
  `{!rust_haltJ CON JUDG Σ} α l v : cif CON Σ :=
  cif_fbor α (λ q, ▷ l ↦{q} v)%cif.
Notation "l ↦ˢ[ α ] v" := (cif_spointsto α l v) : cif_scope.
(** Formula for [spointsto_vec] *)
Notation cif_spointsto_vec α l vl :=
  ([∗ list] k ↦ v ∈ vl, (l +ₗ k) ↦ˢ[α] v)%cif.
Notation "l ↦∗ˢ[ α ] vl" := (cif_spointsto_vec α l vl) : cif_scope.

(** Formula for [sproph_tok] *)
Definition cif_sproph_tok `{!rust_haltGS CON Σ, !rust_haltC CON}
  `{!rust_haltJ CON JUDG Σ} α ξ : cif CON Σ :=
  cif_fbor α (λ q, ▷ q:[ξ])%cif.
Notation "[ ξ ]:ˢ[ α ]" := (cif_sproph_tok α ξ) : cif_scope.
(** Formula for [sproph_toks] *)
Notation cif_sproph_toks α ξl := ([∗ list] ξ ∈ ξl, [ξ]:ˢ[α])%cif.
Notation "[ ξl ]:∗ˢ[ α ]" := (cif_sproph_toks α ξl) : cif_scope.

Section fbor.
  Context `{!rust_haltGS CON Σ, !rust_haltJ CON JUDG Σ}.

  (** [spointsto_vec] over nil *)
  Lemma spointsto_vec_nil {α l δ} : l ↦∗ˢ[α;δ] [] ⊣⊢ True.
  Proof. done. Qed.
  (** [spointsto_vec] over cons *)
  Lemma spointsto_vec_cons {α l v vl δ} :
    l ↦∗ˢ[α;δ] (v :: vl) ⊣⊢ l ↦ˢ[α;δ] v ∗ (l +ₗ 1) ↦∗ˢ[α;δ] vl.
  Proof.
    rewrite /spointsto_vec /= shift_loc_0. do 4 f_equiv. apply reflexive_eq.
    unfold shift_loc=>/=. do 2 f_equal. lia.
  Qed.
  (** [spointsto_vec] over [++] *)
  Lemma spointsto_vec_app {α l vl vl' δ} :
    l ↦∗ˢ[α;δ] (vl ++ vl') ⊣⊢ l ↦∗ˢ[α;δ] vl ∗ (l +ₗ length vl) ↦∗ˢ[α;δ] vl'.
  Proof.
    rewrite /spointsto_vec big_sepL_app. do 4 f_equiv. apply reflexive_eq.
    unfold shift_loc=>/=. do 2 f_equal. lia.
  Qed.

  Context `{!rust_haltC CON, !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ),
    !rust_haltJS CON JUDG Σ}.

  (** Access [spointstod] *)
  Lemma spointstod_acc {α l v r} :
    r.[α] -∗ l ↦ˢ[α] v =[rust_halt_wsat]{⊤}=∗ ∃ q,
      l ↦{q} v ∗ (l ↦{q} v =[rust_halt_wsat]=∗ r.[α]).
  Proof.
    iIntros "α ↦". iMod (fbord_acc (M:=borrowM) with "α ↦") as (?) "/=[>$ →α]".
    { move=>/= ??. by rewrite heap_pointsto_fractional bi.later_sep. }
    iIntros "!> ↦". by iMod ("→α" with "↦").
  Qed.

  (** Access [spointsto_vecd] *)
  Lemma spointsto_vecd_acc {α l vl r} :
    r.[α] -∗ l ↦∗ˢ[α] vl =[rust_halt_wsat]{⊤}=∗ ∃ q,
      l ↦∗{q} vl ∗ (l ↦∗{q} vl =[rust_halt_wsat]=∗ r.[α]).
  Proof.
    move: l r. elim: vl=>//=.
    { unfold heap_pointsto_vec=>/=. iIntros (??) "$ _ !>". by iExists 1%Qp. }
    move=> v vl IH l ?. rewrite spointsto_vec_cons. iIntros "[α α'] [↦ ↦s]".
    iMod (spointstod_acc with "α ↦") as (q) "[↦ →α]".
    iMod (IH with "α' ↦s") as (q') "[↦s →α']". iModIntro.
    case (Qp.lower_bound q q')=> [q''[?[?[->->]]]]. iExists q''.
    rewrite heap_pointsto_vec_cons. iDestruct "↦" as "[$ ↦']".
    iDestruct "↦s" as "[$ ↦s']". iIntros "[↦ ↦s]".
    iMod ("→α" with "[$↦ $↦']") as "$". iApply "→α'".
    rewrite heap_pointsto_vec_fractional. iFrame.
  Qed.

  (** Allocate [spointsto_vecd] *)
  Lemma spointsto_vecd_alloc {α l vl r} :
    r.[α] -∗ bord α (▷ l ↦∗ vl)%cif =[rust_halt_wsat]{⊤}=∗ r.[α] ∗ l ↦∗ˢ[α] vl.
  Proof.
    move: l r. elim: vl=>/=.
    { iIntros (??) "$ _". by rewrite spointsto_vec_nil. }
    iIntros (v vl IH l ?) "α b".
    iMod (bord_open (M:=borrowM) with "α b") as "/=[o ↦s]".
    rewrite {2}heap_pointsto_vec_cons. iDestruct "↦s" as "[↦ ↦s]".
    iMod (obord_subdiv (FML:=cifOF _) (M:=borrowM) [▷ _; ▷ _]%cif
      with "[] o [$↦ $↦s //] []") as "(α & _ & b & b' & _)"=>/=.
    { iApply lft_sincl_refl. }
    { rewrite heap_pointsto_vec_cons. by iIntros "_ ($ & $ & _)". }
    rewrite spointsto_vec_cons. iMod (IH with "α b'") as "[$$]".
    by iMod (fbor_alloc (FML:=cifOF _) (λ q, ▷ l ↦{q} v)%cif with "b") as "$".
  Qed.

  (** Access [sproph_tokd] *)
  Lemma sproph_tok_acc {α ξ r} :
    r.[α] -∗ [ξ]:ˢ[α] =[rust_halt_wsat]{⊤}=∗ ∃ q,
      q:[ξ] ∗ (q:[ξ] =[rust_halt_wsat]=∗ r.[α]).
  Proof.
    iIntros "α ↦". iMod (fbord_acc (M:=borrowM) with "α ↦") as (?) "/=[>$ →α]".
    { move=>/= ??. by rewrite proph_tok_fractional bi.later_sep. }
    iIntros "!> ↦". by iMod ("→α" with "↦").
  Qed.

  (** Access [sproph_toksd] *)
  Lemma sproph_toksd_acc {α ξl r} :
    r.[α] -∗ [ξl]:∗ˢ[α] =[rust_halt_wsat]{⊤}=∗ ∃ q,
      q:∗[ξl] ∗ (q:∗[ξl] =[rust_halt_wsat]=∗ r.[α]).
  Proof.
    move: r. elim: ξl=>/=. { iIntros (?) "$ _ !>". by iExists 1%Qp. }
    iIntros (ξ ξl IH ?) "[α α'] [ξ ξl]".
    iMod (sproph_tok_acc with "α ξ") as (q) "[ξ →α]".
    iMod (IH with "α' ξl") as (q') "[ξl →α']". iModIntro.
    case (Qp.lower_bound q q')=> [q''[?[?[->->]]]]. iExists q''.
    iDestruct "ξ" as "[$ ξ']". iDestruct "ξl" as "[$ ξl']". iIntros "[ξ ξl]".
    iMod ("→α" with "[$ξ $ξ']") as "$". iApply "→α'". iFrame.
  Qed.

  Context `{!rust_haltCS CON JUDG Σ}.

  (** Semantics of [cif_spointsto_vec] *)
  Lemma sem_cif_spointsto_vec {α l vl δ} : ⟦ l ↦∗ˢ[α] vl ⟧ᶜ(δ) ⊣⊢ l ↦∗ˢ[α;δ] vl.
  Proof.
    rewrite sem_cif_big_sepL /spointsto_vec. do 3 f_equiv.
    by rewrite sem_cif_in.
  Qed.
  #[export] Instance sem_cif_spointsto_vec_persistent {α l vl δ} :
    Persistent ⟦ l ↦∗ˢ[α] vl ⟧ᶜ(δ).
  Proof. rewrite sem_cif_spointsto_vec. exact _. Qed.
End fbor.
