(** * Prophetic borrowing *)

From nola.bi Require Export plist.
From nola.bi Require Import order.
From nola.iris Require Export borrow proph_ag.
From iris.proofmode Require Import proofmode.
Import ProdNotation PlistNotation iPropAppNotation LftNotation ProphNotation
  UpdwNotation.

Implicit Type (TY : synty) (FML : oFunctor) (α : lft) (q : Qp).

(** Formula for prophetic borrowing *)
Local Definition pborrow_fml TY FML : oFunctor :=
  (* Just a formula *) FML +
  (* For prophetic borrower *)
  { X : TY & leibnizO (gname *' prvar X) * (X -d> FML) } +
  (* For prophetic lender *)
  { X : TY & leibnizO (clair TY X) * (X -d> FML) } +
  (* For prophetic reborrowing *)
  leibnizO (gname *' gname *' gname *'
    { X : TY & prvar X *' { Y : TY & Y → X }}).
Local Notation xjust Px := (inl (inl (inl Px))).
Local Notation xjustf := (λ Px, xjust Px).
Local Notation xpbor X γ ξ Φx := (inl (inl (inr (existT X ((γ, ξ)', Φx))))).
Local Notation xplend X xπ Φx := (inl (inr (existT X (xπ, Φx)))).
Local Notation xpreborrow X Y γ γ' γx ξ f :=
  (inr (γ, γ', γx, existT X (ξ, existT Y f)')').

(** Ghost state *)
Class pborrowGS TY FML Σ := PborrowGS {
  pborrowGS_borrow :: borrowGS (pborrow_fml TY FML) Σ;
  pborrowGS_proph :: prophGS TY Σ;
  pborrowGS_proph_ag : proph_agG TY Σ;
}.
Local Existing Instance pborrowGS_proph_ag.
Class pborrowGpreS TY FML Σ := PborrowGpreS {
  pborrowGpreS_borrow :: borrowGpreS (pborrow_fml TY FML) Σ;
  pborrowGpreS_proph :: prophGpreS TY Σ;
  pborrowGpreS_proph_ag : proph_agG TY Σ;
}.
Local Existing Instance pborrowGpreS_proph_ag.
Definition pborrowΣ TY FML `{!oFunctorContractive FML} :=
  #[borrowΣ (pborrow_fml TY FML); prophΣ TY; proph_agΣ TY].
#[export] Instance subG_pborrow
  `{!oFunctorContractive FML, !subG (pborrowΣ TY FML) Σ} :
  pborrowGpreS TY FML Σ.
Proof. solve_inG. Qed.

Section pborrow.
  Context `{!pborrowGS TY FML Σ, !GenUpd (PROP:=iProp Σ) M, !GenUpdB M}.
  Implicit Type (sm : FML $oi Σ -d> iProp Σ) (X Y : TY) (Xl Yl : list TY)
    (Px : FML $oi Σ) (Pb : pborrow_fml TY FML $oi Σ).

  (** ** Tokens *)

  (** Non-prophetic tokens *)
  Definition nbor_tok α Px : iProp Σ := bor_tok α (xjust Px).
  Definition nobor_tok α q Px : iProp Σ := obor_tok α q (xjust Px).
  Definition nlend_tok α Px : iProp Σ := lend_tok α (xjust Px).

  (** Prophetic borrower token *)
  Local Definition pbor_tok_def {X} α (x : X) (ξ : prvar X)
    (Φx : X -d> FML $oi Σ) : iProp Σ :=
    [†α] ∨ ∃ γ, val_obs γ x ∗ bor_tok α (xpbor X γ ξ Φx).
  Local Lemma pbor_tok_aux : seal (@pbor_tok_def). Proof. by eexists. Qed.
  Definition pbor_tok {X} := pbor_tok_aux.(unseal) X.
  Local Lemma pbor_tok_unseal : @pbor_tok = @pbor_tok_def.
  Proof. exact: seal_eq. Qed.

  (** Open prophetic borrower token *)
  Local Definition pobor_tok_def {X} α q (ξ : prvar X) (Φx : X -d> FML $oi Σ)
    : iProp Σ :=
    ∃ γ, (∃ x, val_obs γ x ∗ proph_ctrl γ x ξ) ∗
      obor_tok α q (xpbor X γ ξ Φx).
  Local Lemma pobor_tok_aux : seal (@pobor_tok_def). Proof. by eexists. Qed.
  Definition pobor_tok {X} := pobor_tok_aux.(unseal) X.
  Local Lemma pobor_tok_unseal : @pobor_tok = @pobor_tok_def.
  Proof. exact: seal_eq. Qed.

  (** Prophetic lender token *)
  Definition plend_tok {X} α (xπ : clair TY X) (Φx : X -d> FML $oi Σ)
    : iProp Σ := lend_tok α (xplend X xπ Φx).

  (** Borrower and lender tokens are non-expansive *)
  #[export] Instance nbor_tok_ne {α} : NonExpansive (nbor_tok α).
  Proof. solve_proper. Qed.
  #[export] Instance nobor_tok_ne {α q} : NonExpansive (nobor_tok α q).
  Proof. solve_proper. Qed.
  #[export] Instance nlend_tok_ne {α} : NonExpansive (nlend_tok α).
  Proof. solve_proper. Qed.
  #[export] Instance pbor_tok_ne {X α x ξ} :
    NonExpansive (pbor_tok (X:=X) α x ξ).
  Proof.
    rewrite pbor_tok_unseal /pbor_tok_def=> ????. do 7 f_equiv.
    apply inr_ne. by apply: existT_ne.
  Qed.
  #[export] Instance pobor_tok_ne {X α q ξ} :
    NonExpansive (pobor_tok (X:=X) α q ξ).
  Proof.
    rewrite pobor_tok_unseal /pobor_tok_def=> ????. do 6 f_equiv.
    apply inr_ne. by apply: existT_ne.
  Qed.
  #[export] Instance plend_tok_ne {X α xπ} :
    NonExpansive (plend_tok (X:=X) α xπ).
  Proof.
    unfold plend_tok=> ????. do 2 f_equiv. apply inr_ne. by apply: existT_ne.
  Qed.

  (** Borrower and lender tokens are timeless for discrete formulas *)
  Fact nbor_tok_timeless `{!Discrete Px} {α} : Timeless (nbor_tok α Px).
  Proof. exact _. Qed.
  Fact nobor_tok_timeless `{!Discrete Px} {α q} : Timeless (nobor_tok α q Px).
  Proof. exact _. Qed.
  Fact nlend_tok_timeless `{!Discrete Px} {α} : Timeless (nlend_tok α Px).
  Proof. exact _. Qed.
  #[export] Instance pbor_tok_timeless `{!Discrete (Φx : X -d> _)} {α x ξ} :
    Timeless (pbor_tok α x ξ Φx).
  Proof. rewrite pbor_tok_unseal. exact _. Qed.
  #[export] Instance pobor_tok_timeless `{!Discrete (Φx : X -d> _)} {α q ξ} :
    Timeless (pobor_tok α q ξ Φx).
  Proof. rewrite pobor_tok_unseal. exact _. Qed.
  Fact plend_tok_timeless `{!Discrete (Φx : X -d> _)} {α xπ} :
    Timeless (plend_tok α xπ Φx).
  Proof. exact _. Qed.

  (** Fake a borrower token from the dead lifetime token *)
  Lemma nbor_tok_fake {α} Px : [†α] ⊢ nbor_tok α Px.
  Proof. exact: bor_tok_fake. Qed.
  Lemma pbor_tok_fake {X α} x ξ Φx : [†α] ⊢ pbor_tok (X:=X) α x ξ Φx.
  Proof. rewrite pbor_tok_unseal. iIntros. by iLeft. Qed.

  (** Modify the lifetime of borrower and lender tokens *)
  Lemma nbor_tok_lft {α β Px} : β ⊑□ α -∗ nbor_tok α Px -∗ nbor_tok β Px.
  Proof. exact bor_tok_lft. Qed.
  Lemma nobor_tok_lft {α β q r Px} :
    β ⊑□ α -∗ (q.[α] -∗ r.[β]) -∗ nobor_tok α q Px -∗ nobor_tok β r Px.
  Proof. exact obor_tok_lft. Qed.
  Lemma nlend_tok_lft {α β Px} : α ⊑□ β -∗ nlend_tok α Px -∗ nlend_tok β Px.
  Proof. exact lend_tok_lft. Qed.
  Lemma pbor_tok_lft {X α β x ξ Φx} :
    β ⊑□ α -∗ pbor_tok (X:=X) α x ξ Φx -∗ pbor_tok β x ξ Φx.
  Proof.
    rewrite pbor_tok_unseal. iIntros "#? [?|[%[vo ?]]]".
    { iLeft. by iApply lft_sincl_dead. }
    iRight. iExists _. iFrame "vo". by iApply bor_tok_lft.
  Qed.
  Lemma pobor_tok_lft {X α β q r ξ Φx} :
    β ⊑□ α -∗ (q.[α] -∗ r.[β]) -∗
    pobor_tok (X:=X) α q ξ Φx -∗ pobor_tok β r ξ Φx.
  Proof.
    rewrite pobor_tok_unseal. iIntros "⊑ →β [%[vopc o]]". iExists _.
    iFrame "vopc". iApply (obor_tok_lft with "⊑ →β o").
  Qed.
  Lemma plend_tok_lft {X α β xπ Φx} :
    α ⊑□ β -∗ plend_tok (X:=X) α xπ Φx -∗ plend_tok β xπ Φx.
  Proof. exact lend_tok_lft. Qed.

  (** Take out the full prophecy token from an open prophetic borrower *)
  Lemma pobor_proph_tok {X α q ξ Φx} :
    pobor_tok (X:=X) α q ξ Φx -∗ 1:[ξ] ∗ (1:[ξ] -∗ pobor_tok α q ξ Φx).
  Proof.
    rewrite pobor_tok_unseal. iIntros "[%[[%[vo pc]] o]]".
    iDestruct (vo_pc_vo_proph with "vo pc") as "[vo[vo' $]]". iIntros "ξ".
    iExists _. iFrame "o". iExists _. iFrame "vo".
    iApply (vo_proph_pc with "vo' ξ").
  Qed.

  (** ** World satisfaction *)

  (** Body of a prophetic lender *)
  Definition plend_body sm {X} (xπ : clair TY X) (Φx : X -d> FML $oi Σ)
    : iProp Σ := ∃ x', ⟨π, xπ π = x'⟩ ∗ sm (Φx x').
  Definition plend_body_var sm {X} (ξ : prvar X) (Φx : X -d> FML $oi Σ)
    : iProp Σ := plend_body sm (λ π, π ξ) Φx.

  (** [plend_body] is non-expansive *)
  #[export] Instance plend_body_ne `{!NonExpansive sm} {X xπ} :
    NonExpansive (@plend_body sm X xπ).
  Proof. solve_proper. Qed.
  Fact plend_body_var_ne `{!NonExpansive sm} {X ξ} :
    NonExpansive (@plend_body_var sm X ξ).
  Proof. exact _. Qed.

  (** Semantics of [pborrow_fml] *)
  Definition pbsem sm : _ -d> iProp Σ := λ Pb, match Pb with
    | xjust Px => sm Px
    | xpbor _ γ ξ Φx => ∃ x, proph_ctrl γ x ξ ∗ sm (Φx x)
    | xplend _ xπ Φx => plend_body sm xπ Φx
    | xpreborrow _ _ γ γ' γx ξ f =>
        ∃ y, proph_ctrl γ (f y) ξ ∗ val_obs γ' y ∗ val_obs γx y
    end%I.

  (** [pbsem] is non-expansive *)
  #[export] Instance pbsem_sem_ne `{!NonExpansive sm} :
    NonExpansive (pbsem sm).
  Proof.
    move=> ???[_ _[_ _[|]|]|]; [solve_proper|..].
    - move=> [?[??]][?[??]][/=?]. subst. move=>/= [/=??]. solve_proper.
    - move=> [?[??]][?[??]][/=?]. subst. move=>/= [/=/leibniz_equiv_iff ??].
      solve_proper.
    - move=> ?? /leibniz_equiv_iff. solve_proper.
  Qed.
  #[export] Instance pbsem_ne : NonExpansive pbsem.
  Proof. move=> ????[[[?|[?[??]]]|[?[??]]]|?]//=; solve_proper. Qed.

  (** World satisfaction *)
  Definition pborrow_wsat M sm : iProp Σ := borrow_wsat M (pbsem sm).

  (** [pborrow_wsat] is non-expansive *)
  #[export] Instance pborrow_wsat_ne {n} :
    Proper (((≡{n}≡) ==> (≡{n}≡)) ==> (≡{n}≡) ==> (≡{n}≡)) pborrow_wsat.
  Proof. solve_proper. Qed.
  (** [pborrow_wsat] is monotone over the modality *)
  #[export] Instance pborrow_wsat_mono :
    Mono (OT:=_ → _ : bi) (OT':=_ → _ : bi) pborrow_wsat.
  Proof. move=> ????. by apply: borrow_wsat_mono. Qed.

  Context `{!NonExpansive sm}.

  (** ** For non-prophetic borrowing *)

  (** Create new borrowers and lenders *)
  Lemma nbor_nlend_tok_new_list α Pxl Qxl :
    ([∗ list] Px ∈ Pxl, sm Px) -∗
    ([†α] -∗ ([∗ list] Px ∈ Pxl, sm Px) -∗ M
      ([∗ list] Qx ∈ Qxl, sm Qx)%I) =[pborrow_wsat M sm]=∗
      ([∗ list] Px ∈ Pxl, nbor_tok α Px) ∗ [∗ list] Qx ∈ Qxl, nlend_tok α Qx.
  Proof.
    iIntros "Pxl →Qxl".
    iMod (bor_lend_tok_new_list (M:=M) (sm:=pbsem _) α
      (xjustf <$> Pxl) (xjustf <$> Qxl) with "[Pxl] [→Qxl]");
      by rewrite !big_sepL_fmap.
  Qed.
  Lemma nbor_nlend_tok_new α Px :
    sm Px =[pborrow_wsat M sm]=∗ nbor_tok α Px ∗ nlend_tok α Px.
  Proof.
    iIntros "Px". iMod (nbor_nlend_tok_new_list α [Px] [Px] with "[Px] []")
      as "[[$_][$_]]"; by [iFrame|iIntros|].
  Qed.

  (** Split a lender *)
  Lemma nlend_tok_split {α Px} Qxl :
    nlend_tok α Px -∗ (sm Px -∗ M ([∗ list] Qx ∈ Qxl, sm Qx))
      =[pborrow_wsat M sm]=∗ [∗ list] Qx ∈ Qxl, nlend_tok α Qx.
  Proof.
    iIntros "l →Qxl".
    iMod (lend_tok_split (M:=M) (sm:=pbsem _) (xjustf <$> Qxl)
      with "l [→Qxl]"); by rewrite !big_sepL_fmap.
  Qed.

  (** Retrieve from a lender *)
  Lemma nlend_tok_retrieve {α Px} :
    [†α] -∗ nlend_tok α Px -∗ modw M (pborrow_wsat M sm) (sm Px).
  Proof. exact lend_tok_retrieve. Qed.

  (** Open a borrower *)
  Lemma nbor_tok_open {α q Px} :
    q.[α] -∗ nbor_tok α Px -∗ modw M (pborrow_wsat M sm)
      (nobor_tok α q Px ∗ sm Px).
  Proof. exact bor_tok_open. Qed.

  (** Merge and subdivide/reborrow borrowers *)
  Lemma nobor_tok_merge_subdiv αqPxl Qxl β :
    ([∗ list] '(α, q, Px)' ∈ αqPxl, β ⊑□ α ∗ nobor_tok α q Px) -∗
    ([∗ list] Qx ∈ Qxl, sm Qx) -∗ ([†β] -∗ ([∗ list] Qx ∈ Qxl, sm Qx) -∗ M
      ([∗ list] '(_, _, Px)' ∈ αqPxl, sm Px)%I) =[pborrow_wsat M sm]=∗
      ([∗ list] '(α, q, Px)' ∈ αqPxl, q.[α] ∗ ([†β] -∗ nbor_tok α Px)) ∗
      [∗ list] Qx ∈ Qxl, nbor_tok β Qx.
  Proof.
    iIntros "ol Qxl →Pxl".
    iMod (obor_tok_merge_subdiv (M:=M) (sm:=pbsem _)
      ((λ '(α, q, Px)', (α, q, xjust Px)') <$> αqPxl) (xjustf <$> Qxl)
      with "[ol] [Qxl] [→Pxl]"); by rewrite !big_sepL_fmap /=.
  Qed.
  (** Subdivide/reborrow a borrower *)
  Lemma nobor_tok_subdiv {α q Px} Qxl β :
    β ⊑□ α -∗ nobor_tok α q Px -∗ ([∗ list] Qx ∈ Qxl, sm Qx) -∗
    ([†β] -∗ ([∗ list] Qx ∈ Qxl, sm Qx) -∗ M (sm Px))
      =[pborrow_wsat M sm]=∗
      q.[α] ∗ ([†β] -∗ nbor_tok α Px) ∗ [∗ list] Qx ∈ Qxl, nbor_tok β Qx.
  Proof.
    iIntros "⊑ o Qxl →Px".
    iMod (nobor_tok_merge_subdiv [(_,_,_)'] with "[⊑ o] Qxl [→Px]")
      as "[[[$$]_]$]"=>/=; by [iFrame|rewrite bi.sep_emp|].
  Qed.

  (** Reborrow a borrower *)
  Lemma nobor_tok_reborrow {α q Px} β :
    β ⊑□ α -∗ nobor_tok α q Px -∗ sm Px =[pborrow_wsat M sm]=∗
      q.[α] ∗ ([†β] -∗ nbor_tok α Px) ∗ nbor_tok β Px.
  Proof.
    iIntros "⊑ o Px".
    iMod (nobor_tok_subdiv [Px] with "⊑ o [Px] []") as "($ & $ & $ & _)"=>/=;
      by [iFrame|iIntros "_ [$ _]"|].
  Qed.
  Lemma nbor_tok_reborrow {α q Px} β :
    β ⊑□ α -∗ q.[α] -∗ nbor_tok α Px -∗ modw M (pborrow_wsat M sm)
      (q.[α] ∗ ([†β] -∗ nbor_tok α Px) ∗ nbor_tok β Px).
  Proof.
    iIntros "⊑ α b". iMod (nbor_tok_open with "α b") as "[o Px]".
    by iMod (nobor_tok_reborrow with "⊑ o Px").
  Qed.
  (** Simply close a borrower *)
  Lemma nobor_tok_close {α q Px} :
    nobor_tok α q Px -∗ sm Px =[pborrow_wsat M sm]=∗ q.[α] ∗ nbor_tok α Px.
  Proof.
    iIntros "o Px".
    iMod (nobor_tok_reborrow with "[] o Px") as "($ & _ & $)";
      by [iApply lft_sincl_refl|].
  Qed.

  (** ** On prophetic borrowing *)

  (** Utility *)
  Local Definition pbor_list {Xl}
    (γξxΦxl : plist (λ X, _ *' _ *' X *' (X → _)) Xl)
    : list (pborrow_fml TY FML $oi Σ) :=
    of_plist (λ _ '(γ, ξ, _, Φx)', xpbor _ γ ξ Φx) γξxΦxl.
  Local Definition plend_list {Xl} (xπΦxl : plist (λ X, _ *' (X → _)) Xl)
    : list (pborrow_fml TY FML $oi Σ) :=
    of_plist (λ _ '(xπ, Φx)', xplend _ xπ Φx) xπΦxl.
  Local Lemma vo_pbor_alloc_list {Xl ξl} {xΦxl : plist _ Xl} :
    1:∗[of_plist_prvar ξl] -∗ ([∗ plist] '(x, Φx)' ∈ xΦxl, sm (Φx x)) ==∗ ∃ γl,
      let γξxΦxl := plist_zip γl (plist_zip ξl xΦxl) in
      ([∗ plist] '(γ, _, x, _)' ∈ γξxΦxl, val_obs γ x) ∗
      ([∗ list] Pb ∈ pbor_list γξxΦxl, pbsem sm Pb).
  Proof.
    elim: Xl ξl xΦxl=>/=; [iIntros; by iExists ()|].
    move=> X Xl IH [ξ ξl] [[x Φx] xΦxl]. iIntros "[ξ ξl] [Φx Φxl]".
    iMod (IH with "ξl Φxl") as (γl) "[vol pborl]".
    iMod (vo_pc_alloc with "ξ") as (γ) "[vo pc]". iModIntro. iExists (γ, γl)'.
    iFrame "vo vol pborl". iExists _. iFrame.
  Qed.

  (** Lemma for [pbor_plend_tok_new_list] *)
  Local Lemma pbor_list_sem_to_plend {Xl γl} {ξxΦxl : plist _ Xl} :
    ([∗ list] Pb ∈ pbor_list (plist_zip γl ξxΦxl), pbsem sm Pb) ==∗
      [∗ plist] '(ξ, _, Φx)' ∈ ξxΦxl, plend_body_var sm ξ Φx.
  Proof.
    elim: Xl γl ξxΦxl=>/=; [by iIntros|]=> X Xl IH [γ γl] [[ξ[x Φx]] ξxΦxl].
    iIntros "[[%[pc Φx]] pborl]". iMod (IH with "pborl") as "$".
    iMod (pc_resolve with "pc") as "?". iModIntro. iExists _. iFrame.
  Qed.
  (** Create new prophetic borrowers and lenders *)
  Lemma pbor_plend_tok_new_list Xl α (xΦxl : plist _ Xl) :
    ⊢ |==> ∃ ξl, ∀ Yl (yπΨxl : plist (λ Y, _ *' (Y → _)) Yl),
      let ξxΦxl := plist_zip ξl xΦxl in
      ([∗ plist] '(x, Φx)' ∈ xΦxl, sm (Φx x)) -∗
      ([†α] -∗ ([∗ plist] '(ξ, _, Φx)' ∈ ξxΦxl, plend_body_var sm ξ Φx) -∗
        M ([∗ plist] '(yπ, Ψx)' ∈ yπΨxl, plend_body sm yπ Ψx))
        =[pborrow_wsat M sm]=∗
        ([∗ plist] '(ξ, x, Φx)' ∈ ξxΦxl, pbor_tok α x ξ Φx) ∗
        ([∗ plist] '(yπ, Ψx)' ∈ yπΨxl, plend_tok α yπ Ψx).
  Proof.
    iMod (proph_alloc_list (plist_map (λ _, fst') xΦxl)) as (ξl) "ξl".
    iModIntro. iExists ξl. iIntros (??) "Φxl →Ψxl".
    set ξxΦxl := plist_zip ξl xΦxl.
    iMod (vo_pbor_alloc_list with "ξl Φxl") as (γl) "[vol pborl]".
    iMod (bor_lend_tok_new_list (M:=M) α _ (plend_list yπΨxl)
      with "pborl [→Ψxl]") as "[bl ll]".
    { iStopProof. f_equiv. iIntros "→Ψxl pborl".
      iMod (pbor_list_sem_to_plend with "pborl"). rewrite big_sepL_of_plist.
      by iApply "→Ψxl". }
    iModIntro. rewrite !big_sepL_of_plist /=. iFrame "ll".
    iDestruct (big_sepPL_sep_2 with "vol bl") as "vobl".
    rewrite -(plist_zip_snd (xl:=γl) (yl:=ξxΦxl)) big_sepPL_map.
    iApply (big_sepPL_impl with "vobl"). iIntros "!>" (?[?[?[??]]]) "/= [vo b]".
    rewrite pbor_tok_unseal. iRight. iExists _. iFrame.
  Qed.
  (** Simply create a prophetic borrower and a prophetic lender *)
  Lemma pbor_plend_tok_new X α x Φx :
    sm (Φx x) =[pborrow_wsat M sm]=∗ ∃ ξ,
      pbor_tok (X:=X) α x ξ Φx ∗ plend_tok α (λ π, π ξ) Φx.
  Proof.
    iIntros "Φx".
    iMod (pbor_plend_tok_new_list [X] α ((x, Φx)',())') as ([ξ[]]) "big".
    iExists ξ.
    iMod ("big" $! [X] ((_,_)',())' with "[Φx] []") as "[[$ _][$ _]]"=>/=;
      by [iFrame|iIntros|].
  Qed.

  (** Split a prophetic lender *)
  Lemma plend_tok_split {X α xπ Φx} Yl (yπΨxl : plist (λ Y, _ *' (Y → _)) Yl) :
    plend_tok (X:=X) α xπ Φx -∗
    (plend_body sm xπ Φx -∗
      M ([∗ plist] '(yπ, Ψx)' ∈ yπΨxl, plend_body sm yπ Ψx))
      =[pborrow_wsat M sm]=∗ [∗ plist] '(yπ, Ψx)' ∈ yπΨxl, plend_tok α yπ Ψx.
  Proof.
    iIntros "/=l →Ψxl".
    iMod (lend_tok_split (M:=M) (sm:=pbsem _) (plend_list yπΨxl)
      with "l [→Ψxl]"); by rewrite big_sepL_of_plist.
  Qed.

  (** Retrieve from a prophetic lender *)
  Lemma plend_tok_retrieve {X α xπ Φx} :
    [†α] -∗ plend_tok (X:=X) α xπ Φx -∗ modw M (pborrow_wsat M sm)
      (plend_body sm xπ Φx).
  Proof. exact: lend_tok_retrieve. Qed.

  (** Open a prophetic borrower *)
  Lemma pbor_tok_open {X α q x ξ Φx} :
    q.[α] -∗ pbor_tok (X:=X) α x ξ Φx -∗ modw M (pborrow_wsat M sm)
      (pobor_tok α q ξ Φx ∗ sm (Φx x)).
  Proof.
    rewrite pbor_tok_unseal pobor_tok_unseal. iIntros "α [†|[%[vo b]]]".
    { iDestruct (lft_live_dead with "α †") as %[]. }
    iMod (bor_tok_open (M:=M) (sm:=pbsem _) with "α b") as "[o[%[pc Φx]]]".
    iModIntro. iDestruct (vo_pc_agree with "vo pc") as %<-. iFrame "Φx".
    iExists _. iFrame "o". iExists _. iFrame.
  Qed.

  (** Lemmas for [pobor_tok_merge_subdiv] *)
  Local Lemma pobor_preresolve {Xl Yl β r} {ηl : plist _ Yl}
    {αqξΦxfl : plist (λ X, _ *' _ *' _ *' _ *' (_ → X)) Xl} :
    r:∗[of_plist_prvar ηl] -∗
    ([∗ plist] '(α, q, ξ, Φx, _)' ∈ αqξΦxfl, β ⊑□ α ∗ pobor_tok α q ξ Φx) ==∗
      ∃ γl, let γαqξΦxfl := plist_zip γl αqξΦxfl in
      r:∗[of_plist_prvar ηl] ∗
      ([∗ plist] '(_, _, ξ, _, f)' ∈ αqξΦxfl,
        ⟨π, π (Aprvar _ ξ) = f (app_plist_prvar π ηl)⟩) ∗
      ([∗ list] '(α, q, Pb)' ∈
        of_plist (λ _ '(γ, α, q, ξ, Φx, _)', (α, q, xpbor _ γ ξ Φx)') γαqξΦxfl,
        β ⊑□ α ∗ obor_tok α q Pb) ∗
      ∀ yl', ⟨π, app_plist_prvar π ηl = yl'⟩ -∗
        [∗ plist] '(γ, _, _, ξ, _, f)' ∈ γαqξΦxfl, proph_ctrl γ (f yl') ξ.
  Proof.
    rewrite/= pobor_tok_unseal. elim: Xl αqξΦxfl=>/=.
    { iIntros (_) "$ _ !>". iExists (). do 2 (iSplit; [done|]). by iIntros. }
    move=> X Xl IH [[α[q[ξ[Φx f]]]] αqξΦxfl].
    iIntros "ηl [[$[%[[%[vo pc]]o]]] ol]".
    iMod (IH with "ηl ol") as (γl) "[ηl[$[ol →pcl]]]". iExists (γ, γl)'=>/=.
    iFrame "o ol".
    iMod (vo_pc_preresolve (λ π, f (app_plist_prvar π ηl)) with "ηl vo pc")
      as "[$[$ →pc]]"; [exact: proph_dep_plist|]. iModIntro.
    iIntros (yl') "#obs". iDestruct ("→pcl" with "obs") as "$". iApply "→pc".
    by iApply (proph_obs_impl with "obs")=> ? ->.
  Qed.
  Local Lemma pbor_list_sem_to_obs_sem {Yl γl' ηl} {yΨxl : plist _ Yl} :
    ([∗ list] Qb ∈ pbor_list (plist_zip γl' (plist_zip ηl yΨxl)), pbsem sm Qb)
      ==∗ ∃ yl', ⟨π, app_plist_prvar π ηl = yl'⟩ ∗
      [∗ plist] '(y', _, Ψx)' ∈ plist_zip yl' yΨxl, sm (Ψx y').
  Proof.
    elim: Yl γl' ηl yΨxl=>/=.
    { iIntros (_ [] _ _) "!>". iExists (). iSplit; [|done].
      by iApply proph_obs_true. }
    move=> Y Yl IH [γ' γl'] [η ηl] [[y Ψx] yΨxl].
    iIntros "[[%y'[pc Ψx]] pborl]". iMod (IH with "pborl") as (yl') "[obs Ψxl]".
    iExists (y', yl')'. iFrame "Ψx Ψxl". iMod (pc_resolve with "pc") as "obs'".
    iModIntro. by iApply (proph_obs_impl2 with "obs obs'")=>/= ? <- <-.
  Qed.
  (** Merge and subdivide prophetic borrowers *)
  Lemma pobor_tok_merge_subdiv Xl Yl
    (αqξΦxfl : plist (λ X, _ *' _ *' _ *' _ *' (_ → X)) Xl) (yΨxl : plist _ Yl)
    Rl β :
    ([∗ plist] '(α, q, ξ, Φx, _)' ∈ αqξΦxfl, β ⊑□ α ∗ pobor_tok α q ξ Φx) -∗
    ([∗ plist] '(y, Ψx)' ∈ yΨxl, sm (Ψx y)) -∗ ([∗ list] R ∈ Rl, sm R) -∗
    (∀ yl', [†β] -∗
      ([∗ plist] '(y', _, Ψx)' ∈ plist_zip yl' yΨxl, sm (Ψx y')) -∗
      ([∗ list] R ∈ Rl, sm R) -∗ M
        ([∗ plist] '(_, _, _, Φx, f)' ∈ αqξΦxfl, sm (Φx (f yl'))))
      =[pborrow_wsat M sm]=∗ ∃ ηl,
      ([∗ plist] '(α, q, _)' ∈ αqξΦxfl, q.[α]) ∗
      ([∗ plist] '(_, _, ξ, _, f)' ∈ αqξΦxfl,
        ⟨π, π (Aprvar _ ξ) = f (app_plist_prvar π ηl)⟩) ∗
      ([∗ plist] '(η, y, Ψx)' ∈ plist_zip ηl yΨxl, pbor_tok β y η Ψx) ∗
      [∗ list] R ∈ Rl, nbor_tok β R.
  Proof.
    iIntros "ol Ψxl Rl →Φxl".
    iMod (proph_alloc_list (plist_map (λ _, fst') yΨxl)) as (ηl) "ηl".
    iExists ηl.
    iMod (pobor_preresolve with "ηl ol") as (γl) "[ηl[$[ol →pcl]]]".
    iMod (vo_pbor_alloc_list with "ηl Ψxl") as (γl') "[vol pborl]".
    iMod (obor_tok_merge_subdiv (M:=M) (sm:=pbsem _) _
      (_ ++ (xjustf <$> Rl)) with "ol [pborl Rl] [→Φxl →pcl]")
      as "[αl bl]"; rewrite big_sepL_app !big_sepL_fmap. { by iFrame. }
    { iIntros "† [pborl Rl]".
      iMod (pbor_list_sem_to_obs_sem with "pborl") as (yl') "[obs Ψxl]".
      iMod ("→Φxl" with "† Ψxl Rl") as "Φxl". iModIntro.
      iDestruct ("→pcl" with "obs") as "pcl".
      rewrite big_sepL_of_plist
        -{1}(plist_zip_snd (xl:=γl) (yl:=αqξΦxfl)) big_sepPL_map.
      iDestruct (big_sepPL_sep_2 with "pcl Φxl") as "pcΦxl".
      iApply (big_sepPL_impl with "pcΦxl").
      iIntros "!>" (?[?[?[?[??]]]]) "/=[??]". iExists _. iFrame. }
    iModIntro. rewrite !big_sepL_of_plist /=. iDestruct "bl" as "[bl $]".
    setoid_rewrite (bi.sep_elim_l (_.[_])); [|exact _].
    rewrite -(big_sepPL_map _ (λ _ big, (big.2'.1'.[big.1'])%I)) plist_zip_snd.
    iFrame "αl". iDestruct (big_sepPL_sep_2 with "vol bl") as "vocl".
    rewrite -{2}(plist_zip_snd (xl:=γl') (yl:=plist_zip ηl yΨxl)) big_sepPL_map.
    iApply (big_sepPL_impl with "vocl"). iIntros "!>" (?[?[?[??]]]) "/= [vo b]".
    rewrite pbor_tok_unseal. iRight. iExists _. iFrame.
  Qed.
  (** Subdivide a prophetic borrower *)
  Lemma pobor_tok_subdiv {X α q ξ Φx} Yl (f : _ → X) (yΨxl : plist _ Yl) Rl β :
    β ⊑□ α -∗ pobor_tok α q ξ Φx -∗ ([∗ plist] '(y, Ψx)' ∈ yΨxl, sm (Ψx y)) -∗
    ([∗ list] R ∈ Rl, sm R) -∗
    (∀ yl', [†β] -∗
      ([∗ plist] '(y', _, Ψx)' ∈ plist_zip yl' yΨxl, sm (Ψx y')) -∗
      ([∗ list] R ∈ Rl, sm R) -∗ M (sm (Φx (f yl'))))
      =[pborrow_wsat M sm]=∗ ∃ ηl,
      q.[α] ∗ ⟨π, π (Aprvar _ ξ) = f (app_plist_prvar π ηl)⟩ ∗
      ([∗ plist] '(η, y, Ψx)' ∈ plist_zip ηl yΨxl, pbor_tok β y η Ψx) ∗
      [∗ list] R ∈ Rl, nbor_tok β R.
  Proof.
    iIntros "⊑ o Ψxl Rl →Φx".
    iMod (pobor_tok_merge_subdiv [_] _ ((_,_,_,_,_)',())'
      with "[$⊑ $o //] Ψxl Rl [→Φx]") as (ηl) "big"=>/=.
    { iIntros (?). by rewrite bi.sep_emp. }
    iExists ηl. by iDestruct "big" as "/=[[$ _][[$ _]$]]".
  Qed.

  (** Resolve the prophecy of a prophetic borrower *)
  Lemma pobor_tok_resolve {X α q ξ Φx} x :
    pobor_tok (X:=X) α q ξ Φx -∗ sm (Φx x) =[pborrow_wsat M sm]=∗
      q.[α] ∗ ⟨π, π ξ = x⟩ ∗ nbor_tok α (Φx x).
  Proof.
    iIntros "o Φx".
    iMod (pobor_tok_subdiv [] (λ _, x) () [Φx x] with "[] o [//] [Φx] []")
      as (?) "[$[$[_[$ _]]]]"=>/=;
      by [iApply lft_sincl_refl|iFrame|iIntros "% _ _ [$ _]"|].
  Qed.
  Lemma pbor_tok_resolve {X α q x ξ Φx} :
    q.[α] -∗ pbor_tok (X:=X) α x ξ Φx -∗ modw M (pborrow_wsat M sm)
      (q.[α] ∗ ⟨π, π ξ = x⟩ ∗ nbor_tok α (Φx x)).
  Proof.
    iIntros "α b". iMod (pbor_tok_open with "α b") as "[o Φx]".
    by iMod (pobor_tok_resolve with "o Φx").
  Qed.

  (** Subdivide a prophetic borrower without changing the prophecy *)
  Lemma pobor_tok_nsubdiv {X α q ξ Φx} Ψx x β :
    β ⊑□ α -∗ pobor_tok (X:=X) α q ξ Φx -∗ sm (Ψx x) -∗
    (∀ x', [†β] -∗ sm (Ψx x') -∗ M (sm (Φx x'))) =[pborrow_wsat M sm]=∗
      q.[α] ∗ pbor_tok β x ξ Ψx.
  Proof.
    rewrite pobor_tok_unseal pbor_tok_unseal.
    iIntros "⊑ [%[[%[vo pc]] o]] Ψx →Φx".
    iMod (vo_pc_update with "vo pc") as "[vo pc]".
    iMod (obor_tok_subdiv (M:=M) (sm:=pbsem _) [xpbor _ _ _ Ψx]
      with "⊑ o [pc Ψx] [→Φx]") as "[$[_[? _]]]"=>/=.
    { iSplit; [|done]. iExists _. iFrame. }
    { iIntros "† [[%[pc Ψx]]_]". iMod ("→Φx" with "† Ψx") as "Φx". iModIntro.
      iExists _. iFrame. }
    iModIntro. iRight. iExists _. iFrame.
  Qed.
  (** Simply close a prophetic borrower *)
  Lemma pobor_tok_close {X α q ξ Φx} x :
    pobor_tok (X:=X) α q ξ Φx -∗ sm (Φx x) =[pborrow_wsat M sm]=∗
      q.[α] ∗ pbor_tok α x ξ Φx.
  Proof.
    iIntros "o Φx". iApply (pobor_tok_nsubdiv Φx with "[] o Φx"); [|by iIntros].
    iApply lft_sincl_refl.
  Qed.

  (** Reborrow a nested prophetic borrower *)
  Lemma pobor_pobor_tok_reborrow {X Y α q ξ Φx β r η Ψx} y f : β ⊑□ α -∗
    pobor_tok (X:=X) β q ξ Φx -∗ pobor_tok (X:=Y) α r η Ψx -∗ sm (Ψx y) -∗
    (∀ y', [†β] -∗ pbor_tok α y' η Ψx -∗ M (sm (Φx (f y')))) -∗
      modw M (pborrow_wsat M sm) (∃ η' : prvar _,
      q.[β] ∗ r.[α] ∗ ⟨π, π ξ = f (π η')⟩ ∗ pbor_tok β y η' Ψx).
  Proof.
    rewrite pobor_tok_unseal.
    iIntros "#⊑ [%γ[[%[vo pc]] o]] [%γ'[[%[vo' pc']] o']] Ψx →Φx".
    iMod (vo_pc_update with "vo pc") as "[vo pc]".
    iMod (vo_pc_update with "vo' pc'") as "[vo' pc']".
    iMod (obor_tok_reborrow (M:=M) (sm:=pbsem _) β with "⊑ o' [pc' Ψx]")
      as "($ & →b' & b)". { iExists _. iFrame. }
    iMod vo_vo_alloc as (γx) "[vox vox']".
    iMod (obor_tok_subdiv (M:=M) (sm:=pbsem _) [xpreborrow _ _ γ γ' γx ξ f]
      with "[] o [pc vo' vox'] [→Φx →b']") as "[[β β'][_[b' _]]]"=>/=.
    { iApply lft_sincl_refl. } { iSplit; [|done]. iExists _. iFrame. }
    { iIntros "#† [[%y'[pc[vo' _]]]_]". iExists (f y'). iFrame "pc".
      iApply ("→Φx" with "†"). rewrite pbor_tok_unseal. iRight. iExists _.
      iFrame "vo'". by iApply "→b'". }
    iMod (bor_tok_open (M:=M) (sm:=pbsem _) with "β b") as "[o[%[pc' Ψx]]]".
    iMod (bor_tok_open (M:=M) (sm:=pbsem _) with "β' b'")
      as "[o'[%[pc[vo' vox']]]]".
    iDestruct (vo_vo_agree with "vox vox'") as %<-.
    iDestruct (vo_pc_agree with "vo' pc'") as %<-.
    iMod (proph_alloc y) as (η') "η'". iApply modw_fold. iExists η'.
    iMod (vo_pc_preresolve (λ π, f (π η')) [Aprvar _ η'] with "[$η' //] vo pc")
      as "[[η' _][$ →pc]]".
    { apply proph_dep_constr, proph_dep_one. }
    iMod (vo_pc_alloc with "η'") as (γ'') "[vo'' pc'']".
    iMod (obor_tok_merge_subdiv (M:=M) (sm:=pbsem _) [(_,_,_)';(_,_,_)']
      [xpbor _ γ'' η' Ψx] with "[$o $o'] [pc'' Ψx] [→pc vo' pc' vox vox']")
      as "[([$ _] & [$ _] & _) [b _]]"=>/=.
    { iSplit; [|iSplit=>//]; iApply lft_sincl_refl. }
    { iSplit; [|done]. iExists _. iFrame. }
    { iIntros "_ [[%y'[pc'' Ψx]]_]". iMod (pc_resolve with "pc''") as "obs".
      iMod (vo_pc_update with "vo' pc'") as "[vo' pc']".
      iMod (vo_vo_update with "vox vox'") as "[vox _]". iModIntro.
      iSplitL "pc' Ψx"; [iExists _; by iFrame|]. iSplit; [|done]. iExists _.
      iFrame "vo' vox". iApply "→pc".
      by iApply (proph_obs_impl with "obs")=> ? ->. }
    iApply modw_fold. iModIntro. rewrite pbor_tok_unseal. iRight. iExists _.
    iFrame.
  Qed.
  Lemma pobor_pbor_tok_reborrow {X Y α q ξ Φx β r y η Ψx} f : β ⊑□ α -∗
    pobor_tok (X:=X) β q ξ Φx -∗ r.[α] -∗ pbor_tok (X:=Y) α y η Ψx -∗
    (∀ y', [†β] -∗ pbor_tok α y' η Ψx -∗ M (sm (Φx (f y')))) -∗
      modw M (pborrow_wsat M sm) (∃ η' : prvar _,
      q.[β] ∗ r.[α] ∗ ⟨π, π ξ = f (π η')⟩ ∗ pbor_tok β y η' Ψx).
  Proof.
    iIntros "⊑ Φx β b →Φx". iMod (pbor_tok_open with "β b") as "[o Ψx]".
    iApply (pobor_pobor_tok_reborrow with "⊑ Φx o Ψx →Φx").
  Qed.
End pborrow.

(** Allocate [pborrow_wsat] *)
Lemma pborrow_wsat_alloc `{!pborrowGpreS TY FML Σ} :
  ⊢ |==> ∃ _ : pborrowGS TY FML Σ, lft_wsat ∗ ∀ M sm, pborrow_wsat M sm.
Proof.
  iMod proph_init as (?) "_". iMod borrow_wsat_alloc as (?) "[W ?]".
  iModIntro. iExists (PborrowGS _ _ _ _ _ _). iFrame "W". by iIntros.
Qed.
