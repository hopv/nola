(** * Prophetic borrows *)

From nola.bi Require Export plist.
From nola.bi Require Import order.
From nola.iris Require Export borrow proph_ag cif.
From iris.proofmode Require Import proofmode.
Import ProdNotation BigSepPLNotation FunPNotation BUpd0Notation iPropAppNotation
  LftNotation ProphNotation ModwNotation CsemNotation.

Implicit Type (A : Type) (TY : synty) (FML : oFunctor) (γ : positive) (α : lft)
  (q : Qp) (Σ : gFunctors).

(** ** Constructors for prophetic agreement *)

(** [proph_agCT]: Constructor *)
Variant proph_agCT_id A TY := .
Variant proph_agCT_sel {A TY} :=
| (** Prophecy controller *) cifs_proph_ctrl
    {X : TY} γ (a : A) (xπ : clair TY X) (ξ : prvar X)
| (** Prophecy equalizer *) cifs_proph_eqz {X : TY} (xπ xπ' : clair TY X)
| (** Value observer *) cifs_val_obs {X : TY} γ (a : A) (xπ : clair TY X).
Arguments proph_agCT_sel : clear implicits.
Definition proph_agCT A TY :=
  Cifcon (proph_agCT_id A TY) (proph_agCT_sel A TY)
    (λ _, Empty_set) (λ _, Empty_set) (λ _, unitO) _.
(** [proph_agC]: [proph_agCT] registered *)
Notation proph_agC A TY := (inC (proph_agCT A TY)).
Section proph_agC.
  Context `{!proph_agC A TY CON} {Σ}.
  (** [cif_proph_ctrl]: Prophecy controller *)
  Definition cif_proph_ctrl {X} γ a xπ ξ : cif CON Σ :=
    cif_in (proph_agCT A TY) (cifs_proph_ctrl (X:=X) γ a xπ ξ) nullary nullary
      ().
  (** [cif_proph_eqz]: Prophecy controller *)
  Definition cif_proph_eqz {X} xπ xπ' : cif CON Σ :=
    cif_in (proph_agCT A TY) (cifs_proph_eqz (X:=X) xπ xπ') nullary nullary ().
  (** [cif_val_obs]: Value observer *)
  Definition cif_val_obs {X} γ a xπ : cif CON Σ :=
    cif_in (proph_agCT A TY) (cifs_val_obs (X:=X) γ a xπ) nullary nullary ().

  Context `{!prophGS TY Σ, !proph_agG A TY Σ}.
  (** Semantics of [proph_agCT] *)
  Definition proph_agCT_sem (s : proph_agCT_sel A TY) : iProp Σ :=
    match s with
    | cifs_proph_ctrl γ a xπ ξ => proph_ctrl γ a xπ ξ
    | cifs_proph_eqz xπ xπ' => proph_eqz xπ xπ'
    | cifs_val_obs γ a xπ => val_obs γ a xπ
    end.
  #[export] Program Instance proph_agCT_ecsem {JUDG}
    : Ecsem (proph_agCT A TY) CON JUDG Σ :=
    ECSEM (λ _ _ s _ _ _, proph_agCT_sem s) _.
  Next Obligation. done. Qed.
End proph_agC.
(** [proph_agC] semantics registered *)
Notation proph_agCS A TY := (inCS (proph_agCT A TY)).

Section pborrow.
  Context `{!borrowGS (cifOF CON) Σ, !prophGS TY Σ, !proph_agG A TY Σ,
    !proph_agC A TY CON}.
  Implicit Type (a : A) (X Y : TY) (Xl Yl : list TY) (Px : cif CON Σ).

  (** ** Tokens *)

  (** Formulas for a borrower and a lender *)
  Local Definition cif_xpbor {X} γ ξ (Φx : A -d> clair TY X -d> cif CON Σ)
    : cif CON Σ :=
    ∃ a xπ, cif_proph_ctrl γ a xπ ξ ∗ Φx a xπ.
  Definition cif_xplend {X} (xπ : clair TY X) (Φx : clair TY X -d> cif CON Σ)
    : cif CON Σ :=
    ∃ xπ', cif_proph_eqz xπ xπ' ∗ Φx xπ'.

  (** [cif_xpbor] and [cif_xplend] are non-expansive *)
  Local Instance cif_pbor_ne {X γ ξ} : NonExpansive (@cif_xpbor X γ ξ).
  Proof. unfold cif_xpbor. solve_proper. Qed.
  #[export] Instance cif_plend_ne {X xπ} : NonExpansive (@cif_xplend X xπ).
  Proof. unfold cif_xplend. solve_proper. Qed.

  (** Prophetic borrower token *)
  Local Definition pbor_tok_def {X} α a (xπ : clair TY X) (ξ : prvar X)
    (Φx : A -d> clair TY X -d> cif CON Σ) : iProp Σ :=
    [†α] ∨ ∃ γ, val_obs γ a xπ ∗ bor_tok α (cif_xpbor γ ξ Φx).
  Local Lemma pbor_tok_aux : seal (@pbor_tok_def). Proof. by eexists. Qed.
  Definition pbor_tok {X} := pbor_tok_aux.(unseal) X.
  Local Lemma pbor_tok_unseal : @pbor_tok = @pbor_tok_def.
  Proof. exact: seal_eq. Qed.

  (** Open prophetic borrower token *)
  Local Definition pobor_tok_def {X} α q (ξ : prvar X)
    (Φx : A -d> clair TY X -d> cif CON Σ) : iProp Σ :=
    ∃ γ, (∃ a xπ, val_obs γ a xπ ∗ proph_ctrl γ a xπ ξ) ∗
      obor_tok α q (cif_xpbor γ ξ Φx).
  Local Lemma pobor_tok_aux : seal (@pobor_tok_def). Proof. by eexists. Qed.
  Definition pobor_tok {X} := pobor_tok_aux.(unseal) X.
  Local Lemma pobor_tok_unseal : @pobor_tok = @pobor_tok_def.
  Proof. exact: seal_eq. Qed.

  (** Prophetic lender token *)
  Definition plend_tok {X} α (xπ : clair TY X) (Φx : clair TY X -d> cif CON Σ)
    : iProp Σ :=
    lend_tok α (cif_xplend xπ Φx).

  (** Borrower and lender tokens are non-expansive *)
  #[export] Instance pbor_tok_ne {X α a xπ ξ} :
    NonExpansive (@pbor_tok X α a xπ ξ).
  Proof. rewrite pbor_tok_unseal. solve_proper. Qed.
  #[export] Instance pbor_tok_proper {X α a xπ ξ} :
    Proper ((≡) ==> (⊣⊢)) (@pbor_tok X α a xπ ξ).
  Proof. apply ne_proper, _. Qed.
  #[export] Instance pobor_tok_ne {X α q ξ} :
    NonExpansive (@pobor_tok X α q ξ).
  Proof. rewrite pobor_tok_unseal. solve_proper. Qed.
  #[export] Instance pobor_tok_proper {X α q ξ} :
    Proper ((≡) ==> (⊣⊢)) (@pobor_tok X α q ξ).
  Proof. apply ne_proper, _. Qed.
  #[export] Instance plend_tok_ne {X α xπ} :
    NonExpansive (@plend_tok X α xπ).
  Proof. solve_proper. Qed.
  #[export] Instance plend_tok_proper {X α xπ} :
    Proper ((≡) ==> (⊣⊢)) (@plend_tok X α xπ).
  Proof. apply ne_proper, _. Qed.
  (** Borrower and lender tokens are timeless for discrete formulas *)
  #[export] Instance pbor_tok_timeless
    {X α a xπ ξ} `{!∀ a xπ, Discrete (Φx a xπ)} :
    Timeless (@pbor_tok X α a xπ ξ Φx).
  Proof. rewrite pbor_tok_unseal. exact _. Qed.
  #[export] Instance plend_tok_timeless {X α xπ} `{!∀ xπ, Discrete (Φx xπ)} :
    Timeless (@plend_tok X α xπ Φx).
  Proof. exact _. Qed.

  (** ** Basic lemmas *)

  (** Fake a borrower token from the dead lifetime token *)
  Lemma pbor_tok_fake {X α} a xπ ξ Φx : [†α] ⊢ @pbor_tok X α a xπ ξ Φx.
  Proof. rewrite pbor_tok_unseal. iIntros. by iLeft. Qed.

  (** Modify the lifetime of borrower and lender tokens *)
  Lemma pbor_tok_lft {X α β a xπ ξ Φx} :
    β ⊑□ α -∗ @pbor_tok X α a xπ ξ Φx -∗ pbor_tok β a xπ ξ Φx.
  Proof.
    rewrite pbor_tok_unseal. iIntros "#? [?|[%[vo ?]]]".
    { iLeft. by iApply lft_sincl_dead. }
    iRight. iExists _. iFrame "vo". by iApply bor_tok_lft.
  Qed.
  Lemma pobor_tok_lft {X α β q r ξ Φx} :
    β ⊑□ α -∗ (q.[α] -∗ r.[β]) -∗
      @pobor_tok X α q ξ Φx -∗ pobor_tok β r ξ Φx.
  Proof.
    rewrite pobor_tok_unseal. iIntros "⊑ →β [%[vopc o]]". iExists _.
    iFrame "vopc". iApply (obor_tok_lft with "⊑ →β o").
  Qed.

  (** Take out the full prophecy token from an open prophetic borrower token *)
  Lemma pobor_tok_proph {X α q ξ Φx} :
    @pobor_tok X α q ξ Φx -∗ 1:[ξ] ∗ (1:[ξ] -∗ pobor_tok α q ξ Φx).
  Proof.
    rewrite pobor_tok_unseal. iIntros "[%[(% & % & vo & pc) o]]".
    iDestruct (vo_pc_proph with "vo pc") as "[vo[vo' $]]". iIntros "ξ".
    iExists _. iFrame "o". iExists _. iFrame "vo".
    iApply (vo_proph_pc with "vo' ξ").
  Qed.

  (** ** Borrows *)

  Context `{!Csem CON JUDG Σ, !proph_agCS A TY CON JUDG Σ,
    !@ModUpd (iProp Σ) M, !ModBUpd M}.
  Implicit Type δ : JUDG -n> iProp Σ.

  (** Utility *)
  Local Definition cif_xpborl {Xl}
    (γξaxπΦxl : plist
      (λ X, _ *' _ *' A *' clair TY X *' (A -d> clair TY X -d> _)) Xl)
    : list (cif CON Σ) :=
    of_plist (λ _ '(γ, ξ, _, _, Φx)', cif_xpbor γ ξ Φx) γξaxπΦxl.
  Local Definition cif_xplendl {Xl}
    (xπΦxl : plist (λ X, _ *' (clair TY X -d> _)) Xl) : list (cif CON Σ) :=
    of_plist (λ _ '(xπ, Φx)', cif_xplend xπ Φx) xπΦxl.
  Local Lemma alloc_vol_xpbl {δ Xl ξl} {axπΦxl : plist _ Xl} :
    1:∗[Aprvars ξl] -∗ ([∗ plist] '(a, xπ, Φx)' ∈ axπΦxl, ⟦ Φx a xπ ⟧ᶜ(δ)) ==∗
      ∃ γl, let γξaxπΦxl := plist_zip γl (plist_zip ξl axπΦxl) in
      ([∗ plist] '(γ, _, a, xπ, _)' ∈ γξaxπΦxl, val_obs γ a xπ) ∗
      ([∗ list] Px ∈ cif_xpborl γξaxπΦxl, ⟦ Px ⟧ᶜ(δ)).
  Proof.
    elim: Xl ξl axπΦxl=>/=; [iIntros; by iExists ()|].
    move=> X Xl IH [ξ ξl] [axπΦx axπΦxl]. iIntros "[ξ ξl] [Φx Φxl]".
    iMod (IH with "ξl Φxl") as (γl) "[vol xpbl]".
    iMod (vo_pc_alloc with "ξ") as (γ) "[vo pc]". iModIntro. iExists (γ, γl)'.
    iFrame "vo vol xpbl". iExists _, _. iFrame "Φx". by rewrite sem_cif_in.
  Qed.
  Local Lemma of_vol_bl {α Xl γl} {ξaxπΦxl : plist _ Xl} :
    ([∗ plist] '(γ, _, a, xπ, _)' ∈ plist_zip γl ξaxπΦxl, val_obs γ a xπ) -∗
      ([∗ list] Px ∈ cif_xpborl (plist_zip γl ξaxπΦxl), bor_tok α Px) -∗
      [∗ plist] '(ξ, a, xπ, Φx)' ∈ ξaxπΦxl, pbor_tok α a xπ ξ Φx.
  Proof.
    move: Xl γl ξaxπΦxl. elim=>/=; [by iIntros|]=> ?? IH [??][??].
    iIntros "[vo vol][b bl]". iDestruct (IH with "vol bl") as "$".
    rewrite pbor_tok_unseal. iRight. iFrame.
  Qed.

  (** Body of a lender *)
  Definition xplend {X} δ
    (xπ : clair TY X) (Φx : clair TY X -d> cif CON Σ) : iProp Σ :=
    ∃ xπ', proph_eqz xπ xπ' ∗ ⟦ Φx xπ' ⟧ᶜ(δ).
  Definition xplend_var {X} δ
    (ξ : prvar X) (Φx : clair TY X -d> cif CON Σ) : iProp Σ :=
    xplend δ (λ π, π ξ) Φx.
  (** [xplend] and [xplend_var] are non-expansive *)
  #[export] Instance xplend_ne {X δ xπ} : NonExpansive (@xplend X δ xπ).
  Proof. solve_proper. Qed.
  #[export] Instance xplend_proper {X δ xπ} :
    Proper ((≡) ==> (≡)) (@xplend X δ xπ).
  Proof. solve_proper. Qed.
  #[export] Instance xplend_var_ne {X δ ξ} : NonExpansive (@xplend_var X δ ξ).
  Proof. solve_proper. Qed.
  #[export] Instance xplend_var_proper {X δ ξ} :
    Proper ((≡) ==> (≡)) (@xplend_var X δ ξ).
  Proof. solve_proper. Qed.

  (** Lemma for [pbor_plend_tok_new_list] *)
  Local Lemma xpbl_to_xpll {δ Xl γl} {ξaxπΦxl : plist _ Xl} :
    ([∗ list] Px ∈ cif_xpborl (plist_zip γl ξaxπΦxl), ⟦ Px ⟧ᶜ(δ)) ==∗
      [∗ plist] '(ξ, _, _, Φx)' ∈ ξaxπΦxl,
        xplend_var δ ξ (λ xπ, ∃ a, Φx a xπ)%cif.
  Proof.
    elim: Xl γl ξaxπΦxl=>/=; [by iIntros|]=> X Xl IH [γ γl] [ξaxπΦx ξaxπΦxl].
    iIntros "[(% & % & pc & Φx) xpbl]". iMod (IH with "xpbl") as "$".
    rewrite sem_cif_in /= pc_eqz. iModIntro. iExists _. iFrame.
  Qed.
  (** Create new prophetic borrowers and lenders *)
  Lemma pbor_plend_tok_new_list {δ} Xl α (axπΦxl : plist _ Xl) :
    ⊢ |==> ∃ ξl, ∀ Yl (yπΨxl : plist (λ Y, _ *' (clair TY Y → _)) Yl),
      let ξaxπΦxl := plist_zip ξl axπΦxl in
      ([∗ plist] '(a, xπ, Φx)' ∈ axπΦxl, ⟦ Φx a xπ ⟧ᶜ(δ)) -∗
      ([†α] -∗ ([∗ plist] '(ξ, _, _, Φx)' ∈ ξaxπΦxl,
        xplend_var δ ξ (λ xπ, ∃ a, Φx a xπ)%cif) -∗
        M ([∗ plist] '(yπ, Ψx)' ∈ yπΨxl, xplend δ yπ Ψx))
        =[borrow_wsat M ⟦⟧ᶜ(δ)]=∗
        ([∗ plist] '(ξ, a, xπ, Φx)' ∈ ξaxπΦxl, pbor_tok α a xπ ξ Φx) ∗
        ([∗ plist] '(yπ, Ψx)' ∈ yπΨxl, plend_tok α yπ Ψx).
  Proof.
    iMod (proph_alloc_list (plist_map (λ _ '(_, xπ, _)', xπ inhabitant) axπΦxl))
      as (ξl) "ξl".
    iModIntro. iExists ξl. iIntros (??) "Φxl →Ψxl".
    set ξaxπΦxl := plist_zip ξl axπΦxl.
    iMod (alloc_vol_xpbl with "ξl Φxl") as (γl) "[vol xpbl]".
    iMod (bor_lend_tok_new_list (FML:=cifOF _) (M:=M) α _ (cif_xplendl yπΨxl)
      with "xpbl [→Ψxl]") as "[bl ll]".
    { iStopProof. f_equiv. iIntros "→Ψxl xpbl". iMod (xpbl_to_xpll with "xpbl").
      rewrite big_sepL_of_plist /=. setoid_rewrite sem_cif_in.
      by iApply "→Ψxl". }
    iModIntro. rewrite -big_sepL_of_plist. iFrame "ll".
    iApply (of_vol_bl with "vol bl").
  Qed.
  (** Simply create a prophetic borrower and a prophetic lender *)
  Lemma pbor_plend_tok_new {δ} X α a xπ Φx :
    ⟦ Φx a xπ ⟧ᶜ(δ) =[borrow_wsat M ⟦⟧ᶜ(δ)]=∗ ∃ ξ,
      @pbor_tok X α a xπ ξ Φx ∗ plend_tok α (λ π, π ξ) (λ xπ, ∃ a, Φx a xπ)%cif.
  Proof.
    iIntros "Φx".
    iMod (pbor_plend_tok_new_list [X] α ((_,_,_)',())') as ([ξ[]]) "big".
    iExists ξ.
    iMod ("big" $! [X] ((_,_)',())' with "[Φx] []") as "[[$ _][$ _]]"=>/=;
      by [iFrame|iIntros|].
  Qed.

  (** Split a prophetic lender *)
  Lemma plend_tok_split {δ X α xπ Φx} Yl
    (yπΨxl : plist (λ Y, _ *' (clair TY Y → _)) Yl) :
    @plend_tok X α xπ Φx -∗
    (xplend δ xπ Φx -∗ M ([∗ plist] '(yπ, Ψx)' ∈ yπΨxl, xplend δ yπ Ψx))
      =[borrow_wsat M ⟦⟧ᶜ(δ)]=∗ [∗ plist] '(yπ, Ψx)' ∈ yπΨxl, plend_tok α yπ Ψx.
  Proof.
    iIntros "/=l →Ψxl".
    iMod (lend_tok_split (FML:=cifOF _) (M:=M) (cif_xplendl yπΨxl)
      with "l [→Ψxl]"); rewrite big_sepL_of_plist //=.
    by setoid_rewrite sem_cif_in=>/=.
  Qed.

  (** Retrieve from a prophetic lender *)
  Lemma plend_tok_retrieve {δ X α xπ Φx} :
    [†α] -∗ @plend_tok X α xπ Φx -∗ modw M (borrow_wsat M ⟦⟧ᶜ(δ))
      (xplend δ xπ Φx).
  Proof.
    iIntros "† l". iMod (lend_tok_retrieve (M:=M) with "† l")=>/=.
    by setoid_rewrite sem_cif_in.
  Qed.

  (** Open a prophetic borrower *)
  Lemma pbor_tok_open {δ X α q a xπ ξ Φx} :
    q.[α] -∗ @pbor_tok X α a xπ ξ Φx -∗ modw M (borrow_wsat M ⟦⟧ᶜ(δ))
      (pobor_tok α q ξ Φx ∗ ⟦ Φx a xπ ⟧ᶜ(δ)).
  Proof.
    rewrite pbor_tok_unseal pobor_tok_unseal. iIntros "α [†|[%[vo b]]]".
    { iDestruct (lft_live_dead with "α †") as %[]. }
    iMod (bor_tok_open (M:=M) with "α b") as "/=[o (% & % & pc & Φx)]".
    iModIntro. rewrite sem_cif_in.
    iDestruct (vo_pc_agree with "vo pc") as %[<-<-]. iFrame.
  Qed.

  (** Subdivide a prophetic borrower without changing the prophecy *)
  Lemma pobor_tok_soft_subdiv {δ X α q ξ Φx} Ψx a xπ β :
    β ⊑□ α -∗ @pobor_tok X α q ξ Φx -∗ ⟦ Ψx a xπ ⟧ᶜ(δ) -∗
    (∀ a' xπ', [†β] -∗ ⟦ Ψx a' xπ' ⟧ᶜ(δ) -∗ M ⟦ Φx a' xπ' ⟧ᶜ(δ))
      =[borrow_wsat M ⟦⟧ᶜ(δ)]=∗ q.[α] ∗ pbor_tok β a xπ ξ Ψx.
  Proof.
    rewrite pobor_tok_unseal pbor_tok_unseal.
    iIntros "⊑ [%[(% & % & vo & pc) o]] Ψx →Φx".
    iMod (vo_pc_update with "vo pc") as "[vo pc]".
    iMod (obor_tok_subdiv (FML:=cifOF _) (M:=M) [cif_xpbor _ _ Ψx]
      with "⊑ o [pc Ψx] [→Φx]") as "($ & _ & ? & _)"=>/=.
    { iFrame "Ψx". by rewrite sem_cif_in /=. }
    { iIntros "† [(% & % & $ & Ψx) _]". iApply ("→Φx" with "† Ψx"). }
    iModIntro. iRight. iExists _. iFrame.
  Qed.
  (** Simply close a prophetic borrower *)
  Lemma pobor_tok_close {δ X α q ξ Φx} a xπ :
    @pobor_tok X α q ξ Φx -∗ ⟦ Φx a xπ ⟧ᶜ(δ) =[borrow_wsat M ⟦⟧ᶜ(δ)]=∗
      q.[α] ∗ pbor_tok α a xπ ξ Φx.
  Proof.
    iIntros "o Φx".
    iApply (pobor_tok_soft_subdiv Φx with "[] o Φx"); [|by iIntros].
    iApply lft_sincl_refl.
  Qed.

  (** Reborrow a prophetic borrower getting a non-prophetic borrower *)
  Lemma pobor_tok_soft_reborrow `{!ModExcept0 M} {δ X α q ξ Φx} β a xπ :
    β ⊑□ α -∗ @pobor_tok X α q ξ Φx -∗ ⟦ Φx a xπ ⟧ᶜ(δ) =[borrow_wsat M ⟦⟧ᶜ(δ)]=∗
      q.[α] ∗ ([†β] -∗ pbor_tok α a xπ ξ Φx) ∗
        bor_tok β (▷ 1:[ξ])%cif ∗ bor_tok β (Φx a xπ).
  Proof.
    rewrite pobor_tok_unseal pbor_tok_unseal.
    iIntros "⊑ (% & (% & % & vo & pc) & o) Φx".
    iMod (vo_pc_update with "vo pc") as "[vo pc]".
    iDestruct (vo_pc_proph with "vo pc") as "(vo & vo' & ξ)".
    iMod (obor_tok_subdiv (FML:=cifOF _) (M:=M) [▷ _; _]%cif
      with "⊑ o [ξ Φx] [vo']") as "($ & →b & $ & $ & _)"=>/=. { iFrame. }
    { iIntros "_ /=(>ξ & $ & _) !>". rewrite sem_cif_in /=.
      iApply (vo_proph_pc with "vo' ξ"). }
    iIntros "!> †". iRight. by iDestruct ("→b" with "†") as "$".
  Qed.
  Lemma pbor_tok_soft_reborrow `{!ModExcept0 M} {δ X α q ξ Φx a xπ} β :
    β ⊑□ α -∗ q.[α] -∗ @pbor_tok X α a xπ ξ Φx -∗ modw M (borrow_wsat M ⟦⟧ᶜ(δ))
      (q.[α] ∗ ([†β] -∗ pbor_tok α a xπ ξ Φx) ∗
        bor_tok β (▷ 1:[ξ])%cif ∗ bor_tok β (Φx a xπ)).
  Proof.
    iIntros "⊑ α b". iMod (pbor_tok_open with "α b") as "[o Φx]".
    by iMod (pobor_tok_soft_reborrow with "⊑ o Φx") as "$".
  Qed.

  (** Lemma for [pobor_tok_subdiv] *)
  Local Lemma of_xpbl {δ Yl γl' ηl} {ayπΨxl : plist _ Yl} :
    ([∗ list] Qx ∈ cif_xpborl (plist_zip γl' (plist_zip ηl ayπΨxl)), ⟦ Qx ⟧ᶜ(δ))
      ==∗ ∃ yπl',
      proph_eqz (λ π, app_prvars π ηl) (λ π, app_clairs π yπl') ∗
      [∗ plist] '(yπ', _, _, Ψx)' ∈ plist_zip yπl' ayπΨxl,
        ⟦ ∃ a', Ψx a' yπ' ⟧ᶜ(δ)%cif.
  Proof.
    elim: Yl γl' ηl ayπΨxl=>/=.
    { iIntros "_ _ _ _ !>". iExists (). iSplit=>//. iApply proph_eqz_obs.
      by iApply proph_obs_true. }
    move=> Y Yl IH [γ' γl'] [η ηl] [ayπΨx ayπΨxl].
    iIntros "[(%a' & %yπ' & eqz & Ψx) xpbl]". rewrite sem_cif_in /= pc_eqz.
    iMod (IH with "xpbl") as (yπl') "[eqz' Ψxl]". iModIntro. iExists (_, _)'.
    iFrame "Ψx Ψxl". iApply (proph_eqz_f2 with "eqz eqz'").
  Qed.
  (** Subdivide a prophetic borrower *)
  Lemma pobor_tok_subdiv {δ X α q r ξ Φx}
    Yl (fπ : clair TY (_ → X)) ζl (ayπΨxl : plist _ Yl) Rxl β :
    (∀ π π' p p', fπ π p = fπ π' p' → p = p') →
    (∀ p, proph_dep (λ π, fπ π p) ζl) →
    pobor_tok α q ξ Φx =[r:∗[ζl]]=∗ ∃ ηl,
      ⟨π, π (Aprvar _ ξ) = fπ π (app_prvars π ηl)⟩ ∗
      (β ⊑□ α -∗
        ([∗ plist] '(a, yπ, Ψx)' ∈ ayπΨxl, ⟦ Ψx a yπ ⟧ᶜ(δ)) -∗
        ([∗ list] Rx ∈ Rxl, ⟦ Rx ⟧ᶜ(δ)) -∗
        (∀ yπl', [†β] -∗
          ([∗ plist] '(yπ', _, _, Ψx)' ∈ plist_zip yπl' ayπΨxl,
            ⟦ ∃ a, Ψx a yπ' ⟧ᶜ(δ)%cif) -∗
          ([∗ list] Rx ∈ Rxl, ⟦ Rx ⟧ᶜ(δ)) -∗
            M ⟦ ∃ a, Φx a (λ π, fπ π (app_clairs π yπl')) ⟧ᶜ(δ)%cif)
          =[borrow_wsat M ⟦⟧ᶜ(δ)]=∗
          q.[α] ∗
          ([∗ plist] '(η, a, yπ, Ψx)' ∈ plist_zip ηl ayπΨxl,
            pbor_tok β a yπ η Ψx) ∗
          [∗ list] Rx ∈ Rxl, bor_tok β Rx).
  Proof.
    rewrite pobor_tok_unseal=> ??. iIntros "[%[(% & % & vo & pc) o]] ζl".
    iMod (proph_alloc_list (plist_map (λ _ '(_, yπ, _)', yπ inhabitant) ayπΨxl))
      as (ηl) "ηl".
    iDestruct (proph_toks_fuse with "ζl ηl") as (?) "[ζηl →ζlηl]".
    iMod (vo_pc_preresolve with "vo pc ζηl") as "(ζηl & $ & →pc)".
    { apply proph_dep_fpi; [done|]. apply proph_dep_prvars. }
    iDestruct ("→ζlηl" with "ζηl") as "[$ ηl]". iIntros "!> ⊑ Ψxl Rxl →Φx".
    iMod (alloc_vol_xpbl with "ηl Ψxl") as (?) "[vol xpbl]".
    iMod (obor_tok_subdiv (FML:=cifOF _) (M:=M) (_ ++ Rxl)
      with "⊑ o [xpbl Rxl] [→Φx →pc]") as "($ & _ & big)"; rewrite big_sepL_app.
    { by iStopProof. }
    { iIntros "† [xpbl Rxl] /=".
      iMod (of_xpbl with "xpbl") as (?) "[eqz Ψxl]".
      iMod ("→Φx" with "† Ψxl Rxl") as (?) "$". iModIntro. rewrite sem_cif_in.
      iApply "→pc". by iApply proph_eqz_fpi. }
    iModIntro. iDestruct "big" as "[bl $]". iApply (of_vol_bl with "vol bl").
  Qed.

  (** Resolve the prophecy of a prophetic borrower *)
  Lemma pobor_tok_resolve {δ X α q r ξ Φx} a xπ ηl :
    proph_dep xπ ηl →
    @pobor_tok X α q ξ Φx =[r:∗[ηl]]=∗
      ⟨π, π ξ = xπ π⟩ ∗
      (⟦ Φx a xπ ⟧ᶜ(δ) =[borrow_wsat M ⟦⟧ᶜ(δ)]=∗ q.[α] ∗ bor_tok α (Φx a xπ)).
  Proof.
    iIntros "% o".
    iMod (pobor_tok_subdiv [] (λ π _, xπ π) ηl () [Φx a xπ] with "o")
      as "[%[$ big]]"=>//=. { by move=> ??[][]. }
    iIntros "!> Φx".
    iMod ("big" with "[] [//] [$Φx //] []") as "($ & _ & $ & _)"=>//.
    { iApply lft_sincl_refl. } { by iIntros "_ _ _ [$ _]". }
  Qed.

  (** Reborrow a nested prophetic borrower *)
  Lemma pobor_pbor_tok_reborrow {δ X Y α q ξ Φx β r η Ψx a yπ} fπ :
    (∀ π π' y y', fπ π y = fπ π' y' → y = y') →
    β ⊑□ α -∗ r.[α] -∗
    @pobor_tok X β q ξ Φx -∗ @pbor_tok Y α a yπ η Ψx -∗
    (∀ a' yπ', [†β] -∗ pbor_tok α a' yπ' η Ψx -∗ M
      ⟦ Φx a' (λ π, fπ π (yπ' π)) ⟧ᶜ(δ)) -∗
      modw M (borrow_wsat M ⟦⟧ᶜ(δ)) (1:[η] ∗ ⟦ Ψx a yπ ⟧ᶜ(δ) ∗
        ∀ ζl s, ⌜∀ y, proph_dep (λ π, fπ π y) ζl⌝ → s:∗[ζl] ==∗ ∃ η' : prvar _,
          ⟨π, π ξ = fπ π (π η')⟩ ∗ s:∗[ζl] ∗
          (1:[η] -∗ ⟦ Ψx a yπ ⟧ᶜ(δ) =[borrow_wsat M ⟦⟧ᶜ(δ)]=∗
            q.[β] ∗ r.[α] ∗ pbor_tok β a yπ η' Ψx)).
  Proof.
    iIntros (?) "⊑ α o b' →Φx".
    iMod (pbor_tok_open with "α b'") as "[o' Ψx]". rewrite pobor_tok_unseal.
    iDestruct "o" as "[%γ[(% & % & vo & pc) o]]".
    iDestruct "o'" as "[%γ'[(% & % & vo' & pc') o']]".
    iMod (vo_pc_update with "vo pc") as "[vo pc]".
    iMod (vo_pc_update with "vo' pc'") as "[vo' pc']".
    iMod (obor_tok_reborrow (M:=M) β with "⊑ o' [pc' Ψx]") as "($ & →b' & b)".
    { rewrite /=. iExists _, _. rewrite sem_cif_in /=. iFrame. }
    iMod vo_vo_alloc as (γx) "[vox vox']".
    iMod (obor_tok_subdiv (FML:=cifOF _) (M:=M)
      [∃ a yπ, cif_proph_ctrl γ a (λ π, fπ π (yπ π)) ξ ∗
        cif_val_obs γ' a yπ ∗ cif_val_obs γx a yπ]%cif
      with "[] o [pc vo' vox'] [→Φx →b']") as "([β β'] & _ & b' & _)"=>/=.
    { iApply lft_sincl_refl. }
    { iSplit; [|done]. iExists _, _. rewrite !sem_cif_in /=. iFrame. }
    { iIntros "#† [(% & % & pc & vo' & _) _]". iFrame "pc".
      iApply ("→Φx" with "†"). rewrite pbor_tok_unseal. iRight. iExists _.
      rewrite sem_cif_in /=. iFrame "vo'". by iApply "→b'". }
    iMod (bor_tok_open (M:=M) with "β b") as "/=[o (% & % & pc' & Ψx)]".
    iMod (bor_tok_open (M:=M) with "β' b'")
      as "/=[o' (% & % & pc & vo' & vox')]".
    rewrite !sem_cif_in /=. iDestruct (vo_vo_agree with "vox vox'") as %[<-<-].
    iDestruct (vo_pc_agree with "vo' pc'") as %[<-<-]. iFrame "Ψx".
    iDestruct (vo_pc_proph with "vo' pc'") as "(vo' & →pc' & $)". iModIntro.
    iIntros (ζl s ?) "ζl". iMod (proph_alloc (yπ inhabitant)) as (η') "η'".
    iDestruct (proph_toks_tok_fuse with "ζl η'") as (?) "[ζlη' →ζlη']".
    iMod (vo_pc_preresolve (λ π, fπ π (π η')) with "vo pc ζlη'")
      as "[ζlη' [$ →pc]]".
    { apply proph_dep_fpi=>//. apply proph_dep_one. }
    iDestruct ("→ζlη'" with "ζlη'") as "/=[$ η']". iIntros "!> η Ψx".
    iDestruct (vo_proph_pc with "→pc' η") as "pc'".
    iMod (vo_pc_alloc with "η'") as (γ'') "[vo'' pc'']".
    iMod (obor_tok_merge_subdiv (FML:=cifOF _) (M:=M) [(_,_,_)';(_,_,_)']
      [cif_xpbor γ'' η' Ψx] with "[$o $o'] [pc'' Ψx] [→pc vo' pc' vox vox']")
      as "[([$ _] & [$ _] & _) [b _]]"=>/=.
    { iSplit; [|iSplit=>//]; iApply lft_sincl_refl. }
    { iSplit; [|done]. iExists _, _. iFrame "Ψx". by rewrite sem_cif_in /=. }
    { iIntros "_ [(% & % & eqz & Ψx) _]".
      iMod (vo_pc_update with "vo' pc'") as "[vo' pc']".
      iMod (vo_vo_update with "vox vox'") as "[vox _]". iModIntro.
      rewrite sem_cif_in /= (pc_eqz (γ:=γ'')). iSplitL "pc' Ψx".
      { iExists _, _. rewrite sem_cif_in /=. iFrame. }
      iSplit; [|done]. iExists _, _. rewrite !sem_cif_in /=. iFrame "vo' vox".
      iApply "→pc". by iApply proph_eqz_fpi. }
    iModIntro. rewrite pbor_tok_unseal. iRight. iExists _. iFrame.
  Qed.
End pborrow.

(** ** Notation *)
Notation xplendd := (xplend der).
Notation xplendd_var := (xplend_var der).
