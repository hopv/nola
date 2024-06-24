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
Local Notation xjust P := (inl (inl (inl P))).
Local Notation xpbor X γ ξ Φ := (inl (inl (inr (existT X ((γ, ξ)', Φ))))).
Local Notation xplend X xπ Φ := (inl (inr (existT X (xπ, Φ)))).
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
  Context `{!pborrowGS TY FML Σ, !GenUpd (PROP:=iProp Σ) M, !GenUpdBupd M}.
  Implicit Type (sm : FML $oi Σ -d> iProp Σ) (X Y : TY) (Xl Yl : list TY)
    (P : FML $oi Σ) (Pb : pborrow_fml TY FML $oi Σ).

  (** ** Tokens *)

  (** Non-prophetic tokens *)
  Definition nborc_tok α P : iProp Σ := borc_tok α (xjust P).
  Definition nbor_tok α P : iProp Σ := bor_tok α (xjust P).
  Definition nobor_tok α q P : iProp Σ := obor_tok α q (xjust P).
  Definition nlend_tok α P : iProp Σ := lend_tok α (xjust P).

  (** Prophetic borrower token *)
  Local Definition pborc_tok_def {X} α (x : X) (ξ : prvar X)
    (Φ : X -d> FML $oi Σ) : iProp Σ :=
    [†α] ∨ ∃ γ, val_obs γ x ∗ borc_tok α (xpbor X γ ξ Φ).
  Local Lemma pborc_tok_aux : seal (@pborc_tok_def). Proof. by eexists. Qed.
  Definition pborc_tok {X} := pborc_tok_aux.(unseal) X.
  Local Lemma pborc_tok_unseal : @pborc_tok = @pborc_tok_def.
  Proof. exact: seal_eq. Qed.
  Local Definition pbor_tok_def {X} α (x : X) (ξ : prvar X)
    (Φ : X -d> FML $oi Σ) : iProp Σ :=
    [†α] ∨ ∃ γ, val_obs γ x ∗ bor_tok α (xpbor X γ ξ Φ).
  Local Lemma pbor_tok_aux : seal (@pbor_tok_def). Proof. by eexists. Qed.
  Definition pbor_tok {X} := pbor_tok_aux.(unseal) X.
  Local Lemma pbor_tok_unseal : @pbor_tok = @pbor_tok_def.
  Proof. exact: seal_eq. Qed.

  (** Open prophetic borrower token *)
  Local Definition pobor_tok_def {X} α q (ξ : prvar X) (Φ : X -d> FML $oi Σ)
    : iProp Σ :=
    ∃ γ, (∃ x, val_obs γ x ∗ proph_ctrl γ x ξ) ∗
      obor_tok α q (xpbor X γ ξ Φ).
  Local Lemma pobor_tok_aux : seal (@pobor_tok_def). Proof. by eexists. Qed.
  Definition pobor_tok {X} := pobor_tok_aux.(unseal) X.
  Local Lemma pobor_tok_unseal : @pobor_tok = @pobor_tok_def.
  Proof. exact: seal_eq. Qed.

  (** Prophetic lender token *)
  Definition plend_tok {X} α (xπ : clair TY X) (Φ : X -d> FML $oi Σ)
    : iProp Σ := lend_tok α (xplend X xπ Φ).

  (** Borrower and lender tokens are non-expansive *)
  #[export] Instance nborc_tok_ne {α} : NonExpansive (nborc_tok α).
  Proof. solve_proper. Qed.
  #[export] Instance nbor_tok_ne {α} : NonExpansive (nbor_tok α).
  Proof. solve_proper. Qed.
  #[export] Instance nobor_tok_ne {α q} : NonExpansive (nobor_tok α q).
  Proof. solve_proper. Qed.
  #[export] Instance nlend_tok_ne {α} : NonExpansive (nlend_tok α).
  Proof. solve_proper. Qed.
  #[export] Instance pborc_tok_ne {X α x ξ} :
    NonExpansive (pborc_tok (X:=X) α x ξ).
  Proof.
    rewrite pborc_tok_unseal /pborc_tok_def=> ????. do 7 f_equiv.
    apply inr_ne. by apply: existT_ne.
  Qed.
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
  Fact nborc_tok_timeless `{!Discrete P} {α} : Timeless (nborc_tok α P).
  Proof. exact _. Qed.
  Fact nbor_tok_timeless `{!Discrete P} {α} : Timeless (nbor_tok α P).
  Proof. exact _. Qed.
  Fact nobor_tok_timeless `{!Discrete P} {α q} : Timeless (nobor_tok α q P).
  Proof. exact _. Qed.
  Fact nlend_tok_timeless `{!Discrete P} {α} : Timeless (nlend_tok α P).
  Proof. exact _. Qed.
  #[export] Instance pborc_tok_timeless `{!Discrete (Φ : X -d> _)} {α x ξ} :
    Timeless (pborc_tok α x ξ Φ).
  Proof. rewrite pborc_tok_unseal. exact _. Qed.
  #[export] Instance pbor_tok_timeless `{!Discrete (Φ : X -d> _)} {α x ξ} :
    Timeless (pbor_tok α x ξ Φ).
  Proof. rewrite pbor_tok_unseal. exact _. Qed.
  #[export] Instance pobor_tok_timeless `{!Discrete (Φ : X -d> _)} {α q ξ} :
    Timeless (pobor_tok α q ξ Φ).
  Proof. rewrite pobor_tok_unseal. exact _. Qed.
  Fact plend_tok_timeless `{!Discrete (Φ : X -d> _)} {α xπ} :
    Timeless (plend_tok α xπ Φ).
  Proof. exact _. Qed.

  (** Turn [nborc_tok] to [nbor_tok] *)
  Lemma nborc_tok_nbor_tok {α P} : nborc_tok α P ⊢ nbor_tok α P.
  Proof. exact borc_tok_bor_tok. Qed.
  (** Turn [pborc_tok] to [pbor_tok] *)
  Lemma pborc_tok_pbor_tok {X α x ξ Φ} :
    pborc_tok (X:=X) α x ξ Φ ⊢ pbor_tok α x ξ Φ.
  Proof.
    rewrite pborc_tok_unseal pbor_tok_unseal /pborc_tok_def.
    by setoid_rewrite borc_tok_bor_tok.
  Qed.

  (** Fake a borrower token from the dead lifetime token *)
  Lemma nborc_tok_fake {α} P : [†α] ⊢ nborc_tok α P.
  Proof. exact: borc_tok_fake. Qed.
  Lemma nbor_tok_fake {α} P : [†α] ⊢ nbor_tok α P.
  Proof. exact: bor_tok_fake. Qed.
  Lemma pborc_tok_fake {X α} x ξ Φ : [†α] ⊢ pborc_tok (X:=X) α x ξ Φ.
  Proof. rewrite pborc_tok_unseal. iIntros. by iLeft. Qed.
  Lemma pbor_tok_fake {X α} x ξ Φ : [†α] ⊢ pbor_tok (X:=X) α x ξ Φ.
  Proof. rewrite pbor_tok_unseal. iIntros. by iLeft. Qed.

  (** Modify the lifetime of borrower and lender tokens *)
  Lemma nborc_tok_lft {α β P} : β ⊑□ α -∗ nborc_tok α P -∗ nborc_tok β P.
  Proof. exact borc_tok_lft. Qed.
  Lemma nbor_tok_lft {α β P} : β ⊑□ α -∗ nbor_tok α P -∗ nbor_tok β P.
  Proof. exact bor_tok_lft. Qed.
  Lemma nobor_tok_lft {α β q r P} :
    β ⊑□ α -∗ (q.[α] -∗ r.[β]) -∗ nobor_tok α q P -∗ nobor_tok β r P.
  Proof. exact obor_tok_lft. Qed.
  Lemma nlend_tok_lft {α β P} : α ⊑□ β -∗ nlend_tok α P -∗ nlend_tok β P.
  Proof. exact lend_tok_lft. Qed.
  Lemma pborc_tok_lft {X α β x ξ Φ} :
    β ⊑□ α -∗ pborc_tok (X:=X) α x ξ Φ -∗ pborc_tok β x ξ Φ.
  Proof.
    rewrite pborc_tok_unseal. iIntros "#? [?|[%[vo ?]]]".
    { iLeft. by iApply lft_sincl_dead. }
    iRight. iExists _. iFrame "vo". by iApply borc_tok_lft.
  Qed.
  Lemma pbor_tok_lft {X α β x ξ Φ} :
    β ⊑□ α -∗ pbor_tok (X:=X) α x ξ Φ -∗ pbor_tok β x ξ Φ.
  Proof.
    rewrite pbor_tok_unseal. iIntros "#? [?|[%[vo ?]]]".
    { iLeft. by iApply lft_sincl_dead. }
    iRight. iExists _. iFrame "vo". by iApply bor_tok_lft.
  Qed.
  Lemma pobor_tok_lft {X α β q r ξ Φ} :
    β ⊑□ α -∗ (q.[α] -∗ r.[β]) -∗ pobor_tok (X:=X) α q ξ Φ -∗ pobor_tok β r ξ Φ.
  Proof.
    rewrite pobor_tok_unseal. iIntros "⊑ →β [%[vopc o]]". iExists _.
    iFrame "vopc". iApply (obor_tok_lft with "⊑ →β o").
  Qed.
  Lemma plend_tok_lft {X α β xπ Φ} :
    α ⊑□ β -∗ plend_tok (X:=X) α xπ Φ -∗ plend_tok β xπ Φ.
  Proof. exact lend_tok_lft. Qed.

  (** Take out the full prophecy token from an open prophetic borrower *)
  Lemma pobor_proph_tok {X α q ξ Φ} :
    pobor_tok (X:=X) α q ξ Φ -∗ 1:[ξ] ∗ (1:[ξ] -∗ pobor_tok α q ξ Φ).
  Proof.
    rewrite pobor_tok_unseal. iIntros "[%[[%[vo pc]] o]]".
    iDestruct (vo_pc_vo_proph with "vo pc") as "[vo[vo' $]]". iIntros "ξ".
    iExists _. iFrame "o". iExists _. iFrame "vo".
    iApply (vo_proph_pc with "vo' ξ").
  Qed.

  (** ** World satisfaction *)

  (** Body of a prophetic lender *)
  Definition plend_body sm {X} (xπ : clair TY X) (Φ : X -d> FML $oi Σ)
    : iProp Σ := ∃ x', ⟨π, xπ π = x'⟩ ∗ sm (Φ x').
  Definition plend_body_var sm {X} (ξ : prvar X) (Φ : X -d> FML $oi Σ)
    : iProp Σ := plend_body sm (λ π, π ξ) Φ.

  (** [plend_body] is non-expansive *)
  #[export] Instance plend_body_ne `{!NonExpansive sm} {X xπ} :
    NonExpansive (@plend_body sm X xπ).
  Proof. solve_proper. Qed.
  Fact plend_body_var_ne `{!NonExpansive sm} {X ξ} :
    NonExpansive (@plend_body_var sm X ξ).
  Proof. exact _. Qed.

  (** Semantics of [pborrow_fml] *)
  Definition pbsem sm : _ -d> iProp Σ := λ Pb, match Pb with
    | xjust P => sm P
    | xpbor _ γ ξ Φ => ∃ x, proph_ctrl γ x ξ ∗ sm (Φ x)
    | xplend _ xπ Φ => plend_body sm xπ Φ
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
  Lemma nborc_nlend_tok_new_list α Pl Ql :
    ([∗ list] P ∈ Pl, sm P) -∗
    ([†α] -∗ ([∗ list] P ∈ Pl, sm P) -∗ M
      ([∗ list] Q ∈ Ql, sm Q)%I) =[pborrow_wsat M sm]=∗
      ([∗ list] P ∈ Pl, nborc_tok α P) ∗ [∗ list] Q ∈ Ql, nlend_tok α Q.
  Proof.
    iIntros "Pl →Ql".
    iMod (borc_lend_tok_new_list (M:=M) (sm:=pbsem _) α
      ((λ P, xjust P) <$> Pl) ((λ Q, xjust Q) <$> Ql) with "[Pl] [→Ql]");
      by rewrite !big_sepL_fmap.
  Qed.
  Lemma nborc_nlend_tok_new α P :
    sm P =[pborrow_wsat M sm]=∗ nborc_tok α P ∗ nlend_tok α P.
  Proof.
    iIntros "P". iMod (nborc_nlend_tok_new_list α [P] [P] with "[P] []")
      as "[[$_][$_]]"; by [iFrame|iIntros|].
  Qed.

  (** Split a lender *)
  Lemma nlend_tok_split {α P} Ql :
    nlend_tok α P -∗ (sm P -∗ M ([∗ list] Q ∈ Ql, sm Q))
      =[pborrow_wsat M sm]=∗ [∗ list] Q ∈ Ql, nlend_tok α Q.
  Proof.
    iIntros "l →Ql".
    iMod (lend_tok_split (M:=M) (sm:=pbsem _) ((λ Q, xjust Q) <$> Ql)
      with "l [→Ql]"); by rewrite !big_sepL_fmap.
  Qed.

  (** Retrieve from a lender *)
  Lemma nlend_tok_retrieve {α P} :
    [†α] -∗ nlend_tok α P -∗ modw M (pborrow_wsat M sm) (sm P).
  Proof. exact lend_tok_retrieve. Qed.

  (** Open a borrower *)
  Lemma nborc_tok_open {α q P} :
    q.[α] -∗ nborc_tok α P =[pborrow_wsat M sm]=∗ nobor_tok α q P ∗ sm P.
  Proof. exact borc_tok_open. Qed.
  Lemma nbor_tok_open {α q P} :
    q.[α] -∗ nbor_tok α P -∗ modw M (pborrow_wsat M sm)
      (nobor_tok α q P ∗ sm P).
  Proof. exact bor_tok_open. Qed.

  (** Merge and subdivide open borrowers *)
  Lemma nobor_tok_merge_subdiv αqPl Ql β :
    ([∗ list] '(α, q, P)' ∈ αqPl, β ⊑□ α ∗ nobor_tok α q P) -∗
    ([∗ list] Q ∈ Ql, sm Q) -∗ ([†β] -∗ ([∗ list] Q ∈ Ql, sm Q) -∗ M
      ([∗ list] '(_, _, P)' ∈ αqPl, sm P)%I) =[pborrow_wsat M sm]=∗
      ([∗ list] '(α, q, _)' ∈ αqPl, q.[α]) ∗ [∗ list] Q ∈ Ql, nborc_tok β Q.
  Proof.
    iIntros "ol Ql →Pl".
    iMod (obor_tok_merge_subdiv (M:=M) (sm:=pbsem _)
      ((λ '(α, q, P)', (α, q, xjust P)') <$> αqPl) ((λ Q, xjust Q) <$> Ql)
      with "[ol] [Ql] [→Pl]"); by rewrite !big_sepL_fmap /=.
  Qed.
  Lemma nobor_tok_subdiv {α q P} Ql β :
    β ⊑□ α -∗ nobor_tok α q P -∗ ([∗ list] Q ∈ Ql, sm Q) -∗
    ([†β] -∗ ([∗ list] Q ∈ Ql, sm Q) -∗ M (sm P))
      =[pborrow_wsat M sm]=∗ q.[α] ∗ [∗ list] Q ∈ Ql, nborc_tok β Q.
  Proof.
    iIntros "⊑ o Ql →P".
    iMod (nobor_tok_merge_subdiv [(_,_,_)'] with "[⊑ o] Ql [→P]")
      as "[[$ _]$]"=>/=; by [iFrame|rewrite bi.sep_emp|].
  Qed.
  Lemma nobor_tok_close {α q P} :
    nobor_tok α q P -∗ sm P =[pborrow_wsat M sm]=∗ q.[α] ∗ nborc_tok α P.
  Proof.
    iIntros "o P".
    iMod (nobor_tok_subdiv [P] with "[] o [P] []") as "[$[$_]]"=>/=;
      by [iApply lft_sincl_refl|iFrame|iIntros "_[$_]"|].
  Qed.

  (** Reborrow *)
  Lemma nobor_tok_reborrow {α q P} β :
    nobor_tok α q P -∗ sm P =[pborrow_wsat M sm]=∗
      q.[α] ∗ nborc_tok (α ⊓ β) P ∗ ([†β] -∗ nbor_tok α P).
  Proof. exact: obor_tok_reborrow. Qed.
  Lemma nborc_tok_reborrow {α q P} β :
    q.[α] -∗ nborc_tok α P =[pborrow_wsat M sm]=∗
      q.[α] ∗ nborc_tok (α ⊓ β) P ∗ ([†β] -∗ nbor_tok α P).
  Proof. exact: borc_tok_reborrow. Qed.
  Lemma nbor_tok_reborrow {α q P} β :
    q.[α] -∗ nbor_tok α P -∗ modw M (pborrow_wsat M sm)
      (q.[α] ∗ nborc_tok (α ⊓ β) P ∗ ([†β] -∗ nbor_tok α P)).
  Proof. exact: bor_tok_reborrow. Qed.

  (** ** On prophetic borrowing *)

  (** Utility *)
  Local Definition pbor_list {Xl}
    (γξxΦl : plist (λ X, _ *' _ *' X *' (X → _)) Xl)
    : list (pborrow_fml TY FML $oi Σ) :=
    of_plist (λ _ '(γ, ξ, _, Φ)', xpbor _ γ ξ Φ) γξxΦl.
  Local Definition plend_list {Xl} (xπΦl : plist (λ X, _ *' (X → _)) Xl)
    : list (pborrow_fml TY FML $oi Σ) :=
    of_plist (λ _ '(xπ, Φ)', xplend _ xπ Φ) xπΦl.
  Local Lemma vo_pbor_alloc_list {Xl ξl} {xΦl : plist _ Xl} :
    1:∗[of_plist_prvar ξl] -∗ ([∗ plist] '(x, Φ)' ∈ xΦl, sm (Φ x)) ==∗ ∃ γl,
      let γξxΦl := plist_zip γl (plist_zip ξl xΦl) in
      ([∗ plist] '(γ, _, x, _)' ∈ γξxΦl, val_obs γ x) ∗
      ([∗ list] Pb ∈ pbor_list γξxΦl, pbsem sm Pb).
  Proof.
    elim: Xl ξl xΦl=>/=; [iIntros; by iExists ()|]=> X Xl IH [ξ ξl] [[x Φ] xΦl].
    iIntros "[ξ ξl] [Φ Φl]". iMod (IH with "ξl Φl") as (γl) "[vol pborl]".
    iMod (vo_pc_alloc with "ξ") as (γ) "[vo pc]". iModIntro. iExists (γ, γl)'.
    iFrame "vo vol pborl". iExists _. iFrame.
  Qed.

  (** Lemma for [pborc_plend_tok_new_list] *)
  Local Lemma pbor_list_sem_to_plend {Xl γl} {ξxΦl : plist _ Xl} :
    ([∗ list] Pb ∈ pbor_list (plist_zip γl ξxΦl), pbsem sm Pb) ==∗
      [∗ plist] '(ξ, _, Φ)' ∈ ξxΦl, plend_body_var sm ξ Φ.
  Proof.
    elim: Xl γl ξxΦl=>/=; [by iIntros|]=> X Xl IH [γ γl] [[ξ[x Φ]] ξxΦl].
    iIntros "[[%[pc Φ]] pborl]". iMod (IH with "pborl") as "$".
    iMod (pc_resolve with "pc") as "?". iModIntro. iExists _. iFrame.
  Qed.
  (** Create new prophetic borrowers and lenders *)
  Lemma pborc_plend_tok_new_list Xl α (xΦl : plist _ Xl) :
    ⊢ |==> ∃ ξl, ∀ Yl (yπΨl : plist (λ Y, _ *' (Y → _)) Yl),
      let ξxΦl := plist_zip ξl xΦl in
      ([∗ plist] '(x, Φ)' ∈ xΦl, sm (Φ x)) -∗
      ([†α] -∗ ([∗ plist] '(ξ, _, Φ)' ∈ ξxΦl, plend_body_var sm ξ Φ) -∗
        M ([∗ plist] '(yπ, Ψ)' ∈ yπΨl, plend_body sm yπ Ψ))
        =[pborrow_wsat M sm]=∗
        ([∗ plist] '(ξ, x, Φ)' ∈ ξxΦl, pborc_tok α x ξ Φ) ∗
        ([∗ plist] '(yπ, Ψ)' ∈ yπΨl, plend_tok α yπ Ψ).
  Proof.
    iMod (proph_alloc_list (plist_map (λ _, fst') xΦl)) as (ξl) "ξl".
    iModIntro. iExists ξl. iIntros (??) "Φl →Ψl".
    set ξxΦl := plist_zip ξl xΦl.
    iMod (vo_pbor_alloc_list with "ξl Φl") as (γl) "[vol pborl]".
    iMod (borc_lend_tok_new_list (M:=M) α _ (plend_list yπΨl)
      with "pborl [→Ψl]") as "[bl ll]".
    { iStopProof. f_equiv. iIntros "→Ψl pborl".
      iMod (pbor_list_sem_to_plend with "pborl"). rewrite big_sepL_of_plist.
      by iApply "→Ψl". }
    iModIntro. rewrite !big_sepL_of_plist /=. iFrame "ll".
    iDestruct (big_sepPL_sep_2 with "vol bl") as "vobl".
    rewrite -(plist_zip_snd (xl:=γl) (yl:=ξxΦl)) big_sepPL_map.
    iApply (big_sepPL_impl with "vobl"). iIntros "!>" (?[?[?[??]]]) "/= [vo b]".
    rewrite pborc_tok_unseal. iRight. iExists _. iFrame.
  Qed.
  (** Simply create a prophetic borrower and a prophetic lender *)
  Lemma pborc_plend_tok_new X α x Φ :
    sm (Φ x) =[pborrow_wsat M sm]=∗ ∃ ξ,
      pborc_tok (X:=X) α x ξ Φ ∗ plend_tok α (λ π, π ξ) Φ.
  Proof.
    iIntros "Φ".
    iMod (pborc_plend_tok_new_list [X] α ((x, Φ)',())') as ([ξ[]]) "big".
    iExists ξ.
    iMod ("big" $! [X] ((_,_)',())' with "[Φ] []") as "[[$ _][$ _]]"=>/=;
      by [iFrame|iIntros|].
  Qed.

  (** Split a prophetic lender *)
  Lemma plend_tok_split {X α xπ Φ} Yl (yπΨl : plist (λ Y, _ *' (Y → _)) Yl) :
    plend_tok (X:=X) α xπ Φ -∗
    (plend_body sm xπ Φ -∗ M ([∗ plist] '(yπ, Ψ)' ∈ yπΨl, plend_body sm yπ Ψ))
      =[pborrow_wsat M sm]=∗ [∗ plist] '(yπ, Ψ)' ∈ yπΨl, plend_tok α yπ Ψ.
  Proof.
    iIntros "/=l →Ψl".
    iMod (lend_tok_split (M:=M) (sm:=pbsem _) (plend_list yπΨl)
      with "l [→Ψl]"); by rewrite big_sepL_of_plist.
  Qed.

  (** Retrieve from a prophetic lender *)
  Lemma plend_tok_retrieve {X α xπ Φ} :
    [†α] -∗ plend_tok (X:=X) α xπ Φ -∗ modw M (pborrow_wsat M sm)
      (plend_body sm xπ Φ).
  Proof. exact: lend_tok_retrieve. Qed.

  (** Open a prophetic borrower *)
  Lemma pborc_tok_open {X α q x ξ Φ} :
    q.[α] -∗ pborc_tok (X:=X) α x ξ Φ =[pborrow_wsat M sm]=∗
      pobor_tok α q ξ Φ ∗ sm (Φ x).
  Proof.
    rewrite pborc_tok_unseal pobor_tok_unseal. iIntros "α [†|[%[vo c]]]".
    { iDestruct (lft_live_dead with "α †") as "[]". }
    iMod (borc_tok_open (sm:=pbsem _) with "α c") as "[o[%[pc Φ]]]".
    iModIntro. iDestruct (vo_pc_agree with "vo pc") as %<-. iFrame "Φ".
    iExists _. iFrame "o". iExists _. iFrame.
  Qed.
  Lemma pbor_tok_open {X α q x ξ Φ} :
    q.[α] -∗ pbor_tok (X:=X) α x ξ Φ -∗ modw M (pborrow_wsat M sm)
      (pobor_tok α q ξ Φ ∗ sm (Φ x)).
  Proof.
    rewrite pbor_tok_unseal pobor_tok_unseal. iIntros "α [†|[%[vo b]]]".
    { iDestruct (lft_live_dead with "α †") as "[]". }
    iMod (bor_tok_open (M:=M) (sm:=pbsem _) with "α b") as "[o[%[pc Φ]]]".
    iModIntro. iDestruct (vo_pc_agree with "vo pc") as %<-. iFrame "Φ".
    iExists _. iFrame "o". iExists _. iFrame.
  Qed.

  (** Lemmas for [pobor_tok_merge_subdiv] *)
  Local Lemma pobor_preresolve {Xl Yl β r} {ηl : plist _ Yl}
    {αqξΦfl : plist (λ X, _ *' _ *' _ *' _ *' (_ → X)) Xl} :
    r:∗[of_plist_prvar ηl] -∗
    ([∗ plist] '(α, q, ξ, Φ, _)' ∈ αqξΦfl, β ⊑□ α ∗ pobor_tok α q ξ Φ) ==∗ ∃ γl,
      let γαqξΦfl := plist_zip γl αqξΦfl in
      r:∗[of_plist_prvar ηl] ∗
      ([∗ plist] '(_, _, ξ, _, f)' ∈ αqξΦfl,
        ⟨π, π (Aprvar _ ξ) = f (app_plist_prvar π ηl)⟩) ∗
      ([∗ list] '(α, q, Pb)' ∈
        of_plist (λ _ '(γ, α, q, ξ, Φ, _)', (α, q, xpbor _ γ ξ Φ)') γαqξΦfl,
        β ⊑□ α ∗ obor_tok α q Pb) ∗
      ∀ yl', ⟨π, app_plist_prvar π ηl = yl'⟩ -∗
        [∗ plist] '(γ, _, _, ξ, _, f)' ∈ γαqξΦfl, proph_ctrl γ (f yl') ξ.
  Proof.
    rewrite/= pobor_tok_unseal. elim: Xl αqξΦfl=>/=.
    { iIntros (_) "$ _ !>". iExists (). do 2 (iSplit; [done|]). by iIntros. }
    move=> X Xl IH [[α[q[ξ[Φ f]]]] αqξΦfl].
    iIntros "ηl [[$[%[[%[vo pc]]o]]] ol]".
    iMod (IH with "ηl ol") as (γl) "[ηl[$[ol →pcl]]]". iExists (γ, γl)'=>/=.
    iFrame "o ol".
    iMod (vo_pc_preresolve (λ π, f (app_plist_prvar π ηl)) with "ηl vo pc")
      as "[$[$ →pc]]"; [exact: proph_dep_plist|]. iModIntro.
    iIntros (yl') "#obs". iDestruct ("→pcl" with "obs") as "$". iApply "→pc".
    by iApply (proph_obs_impl with "obs")=> ? ->.
  Qed.
  Local Lemma pbor_list_sem_to_obs_sem {Yl γl' ηl} {yΨl : plist _ Yl} :
    ([∗ list] Qb ∈ pbor_list (plist_zip γl' (plist_zip ηl yΨl)), pbsem sm Qb)
      ==∗ ∃ yl', ⟨π, app_plist_prvar π ηl = yl'⟩ ∗
      [∗ plist] '(y', _, Ψ)' ∈ plist_zip yl' yΨl, sm (Ψ y').
  Proof.
    elim: Yl γl' ηl yΨl=>/=.
    { iIntros (_ [] _ _) "!>". iExists (). iSplit; [|done].
      by iApply proph_obs_true. }
    move=> Y Yl IH [γ' γl'] [η ηl] [[y Ψ] yΨl]. iIntros "[[%y'[pc Ψ]] pborl]".
    iMod (IH with "pborl") as (yl') "[obs Ψl]". iExists (y', yl')'.
    iFrame "Ψ Ψl". iMod (pc_resolve with "pc") as "obs'". iModIntro.
    by iApply (proph_obs_impl2 with "obs obs'")=>/= ? <- <-.
  Qed.
  (** Merge and subdivide prophetic borrowers *)
  Lemma pobor_tok_merge_subdiv Xl Yl
    (αqξΦfl : plist (λ X, _ *' _ *' _ *' _ *' (_ → X)) Xl) (yΨl : plist _ Yl) Rl
    β :
    ([∗ plist] '(α, q, ξ, Φ, _)' ∈ αqξΦfl, β ⊑□ α ∗ pobor_tok α q ξ Φ) -∗
    ([∗ plist] '(y, Ψ)' ∈ yΨl, sm (Ψ y)) -∗ ([∗ list] R ∈ Rl, sm R) -∗
    (∀ yl', [†β] -∗ ([∗ plist] '(y', _, Ψ)' ∈ plist_zip yl' yΨl, sm (Ψ y')) -∗
      ([∗ list] R ∈ Rl, sm R) -∗ M
        ([∗ plist] '(_, _, _, Φ, f)' ∈ αqξΦfl, sm (Φ (f yl'))))
      =[pborrow_wsat M sm]=∗ ∃ ηl,
      ([∗ plist] '(α, q, _)' ∈ αqξΦfl, q.[α]) ∗
      ([∗ plist] '(_, _, ξ, _, f)' ∈ αqξΦfl,
        ⟨π, π (Aprvar _ ξ) = f (app_plist_prvar π ηl)⟩) ∗
      ([∗ plist] '(η, y, Ψ)' ∈ plist_zip ηl yΨl, pborc_tok β y η Ψ) ∗
      [∗ list] R ∈ Rl, nborc_tok β R.
  Proof.
    iIntros "ol Ψl Rl →Φl".
    iMod (proph_alloc_list (plist_map (λ _, fst') yΨl)) as (ηl) "ηl".
    iExists ηl.
    iMod (pobor_preresolve with "ηl ol") as (γl) "[ηl[$[ol →pcl]]]".
    iMod (vo_pbor_alloc_list with "ηl Ψl") as (γl') "[vol pborl]".
    iMod (obor_tok_merge_subdiv (M:=M) (sm:=pbsem _) _
      (_ ++ ((λ R, xjust R) <$> Rl)) with "ol [pborl Rl] [→Φl →pcl]")
      as "[αl cl]"; rewrite big_sepL_app !big_sepL_fmap. { by iFrame. }
    { iIntros "† [pborl Rl]".
      iMod (pbor_list_sem_to_obs_sem with "pborl") as (yl') "[obs Ψl]".
      iMod ("→Φl" with "† Ψl Rl") as "Φl". iModIntro.
      iDestruct ("→pcl" with "obs") as "pcl".
      rewrite big_sepL_of_plist
        -{1}(plist_zip_snd (xl:=γl) (yl:=αqξΦfl)) big_sepPL_map.
      iDestruct (big_sepPL_sep_2 with "pcl Φl") as "pcΦl".
      iApply (big_sepPL_impl with "pcΦl").
      iIntros "!>" (?[?[?[?[??]]]]) "/=[??]". iExists _. iFrame. }
    iModIntro. rewrite !big_sepL_of_plist /=. iDestruct "cl" as "[cl $]".
    rewrite -(big_sepPL_map _ (λ _ big, (big.2'.1'.[big.1'])%I)) plist_zip_snd.
    iFrame "αl". iDestruct (big_sepPL_sep_2 with "vol cl") as "vocl".
    rewrite -{2}(plist_zip_snd (xl:=γl') (yl:=plist_zip ηl yΨl)) big_sepPL_map.
    iApply (big_sepPL_impl with "vocl"). iIntros "!>" (?[?[?[??]]]) "/= [vo c]".
    rewrite pborc_tok_unseal. iRight. iExists _. iFrame.
  Qed.
  (** Subdivide a prophetic borrower *)
  Lemma pobor_tok_subdiv {X α q ξ Φ} Yl (f : _ → X) (yΨl : plist _ Yl) Rl β :
    β ⊑□ α -∗ pobor_tok α q ξ Φ -∗ ([∗ plist] '(y, Ψ)' ∈ yΨl, sm (Ψ y)) -∗
    ([∗ list] R ∈ Rl, sm R) -∗
    (∀ yl', [†β] -∗ ([∗ plist] '(y', _, Ψ)' ∈ plist_zip yl' yΨl, sm (Ψ y')) -∗
      ([∗ list] R ∈ Rl, sm R) -∗ M (sm (Φ (f yl'))))
      =[pborrow_wsat M sm]=∗ ∃ ηl,
      q.[α] ∗ ⟨π, π (Aprvar _ ξ) = f (app_plist_prvar π ηl)⟩ ∗
      ([∗ plist] '(η, y, Ψ)' ∈ plist_zip ηl yΨl, pborc_tok β y η Ψ) ∗
      [∗ list] R ∈ Rl, nborc_tok β R.
  Proof.
    iIntros "⊑ o Ψl Rl →Φ".
    iMod (pobor_tok_merge_subdiv [_] _ ((_,_,_,_,_)',())'
      with "[$⊑ $o //] Ψl Rl [→Φ]") as (ηl) "big"=>/=.
    { iIntros (?). by rewrite bi.sep_emp. }
    iExists ηl. by iDestruct "big" as "/=[[$ _][[$ _]$]]".
  Qed.

  (** Resolve the prophecy of a prophetic borrower *)
  Lemma pobor_tok_resolve {X α q ξ Φ} x :
    pobor_tok (X:=X) α q ξ Φ -∗ sm (Φ x) =[pborrow_wsat M sm]=∗
      q.[α] ∗ ⟨π, π ξ = x⟩ ∗ nborc_tok α (Φ x).
  Proof.
    iIntros "o Φ".
    iMod (pobor_tok_subdiv [] (λ _, x) () [Φ x] with "[] o [//] [Φ] []")
      as (?) "[$[$[_[$ _]]]]"=>/=;
      by [iApply lft_sincl_refl|iFrame|iIntros "% _ _ [$ _]"|].
  Qed.
  Lemma pborc_tok_resolve {X α q x ξ Φ} :
    q.[α] -∗ pborc_tok (X:=X) α x ξ Φ =[pborrow_wsat M sm]=∗
      q.[α] ∗ ⟨π, π ξ = x⟩ ∗ nborc_tok α (Φ x).
  Proof.
    iIntros "α c". iMod (pborc_tok_open with "α c") as "[o Φ]".
    iApply (pobor_tok_resolve with "o Φ").
  Qed.
  Lemma pbor_tok_resolve {X α q x ξ Φ} :
    q.[α] -∗ pbor_tok (X:=X) α x ξ Φ -∗ modw M (pborrow_wsat M sm)
      (q.[α] ∗ ⟨π, π ξ = x⟩ ∗ nborc_tok α (Φ x)).
  Proof.
    iIntros "α b". iMod (pbor_tok_open with "α b") as "[o Φ]".
    by iMod (pobor_tok_resolve with "o Φ").
  Qed.

  (** Subdivide a prophetic borrower without changing the prophecy *)
  Lemma pobor_tok_nsubdiv {X α q ξ Φ} Ψ x β :
    β ⊑□ α -∗ pobor_tok (X:=X) α q ξ Φ -∗ sm (Ψ x) -∗
    (∀ x', [†β] -∗ sm (Ψ x') -∗ M (sm (Φ x'))) =[pborrow_wsat M sm]=∗
      q.[α] ∗ pborc_tok β x ξ Ψ.
  Proof.
    rewrite pobor_tok_unseal pborc_tok_unseal.
    iIntros "⊑ [%[[%[vo pc]] o]] Ψ →Φ".
    iMod (vo_pc_update with "vo pc") as "[vo pc]".
    iMod (obor_tok_subdiv (M:=M) (sm:=pbsem _) [xpbor _ _ _ Ψ]
      with "⊑ o [pc Ψ] [→Φ]") as "[$[c _]]"=>/=.
    { iSplit; [|done]. iExists _. iFrame. }
    { iIntros "† [[%[pc Ψ]]_]". iMod ("→Φ" with "† Ψ") as "Φ". iModIntro.
      iExists _. iFrame. }
    iModIntro. iRight. iExists _. iFrame.
  Qed.
  (** Simply close a prophetic borrower *)
  Lemma pobor_tok_close {X α q ξ Φ} x :
    pobor_tok (X:=X) α q ξ Φ -∗ sm (Φ x) =[pborrow_wsat M sm]=∗
      q.[α] ∗ pborc_tok α x ξ Φ.
  Proof.
    iIntros "o Φ". iApply (pobor_tok_nsubdiv Φ with "[] o Φ"); [|by iIntros].
    iApply lft_sincl_refl.
  Qed.

  (** Reborrow a nested prophetic borrower *)
  Lemma pobor_pobor_tok_reborrow {X Y α q ξ Φ β r η Ψ} y f :
    pobor_tok (X:=X) α q ξ Φ -∗ pobor_tok (X:=Y) β r η Ψ -∗ sm (Ψ y) -∗
    (∀ y', [†α] -∗ pbor_tok β y' η Ψ -∗ M (sm (Φ (f y'))))
      =[pborrow_wsat M sm]=∗ ∃ η' : prvar _,
      q.[α] ∗ r.[β] ∗ ⟨π, π ξ = f (π η')⟩ ∗ pborc_tok (α ⊓ β) y η' Ψ.
  Proof.
    rewrite pobor_tok_unseal.
    iIntros "[%γ[[%[vo pc]] o]] [%γ'[[%[vo' pc']] o']] Ψ →Φ".
    iMod (vo_pc_update with "vo pc") as "[vo pc]".
    iMod (vo_pc_update with "vo' pc'") as "[vo' pc']".
    iMod (obor_tok_reborrow (M:=M) (sm:=pbsem _) α with "o' [pc' Ψ]")
      as "[β[c →b']]". { iExists _. iFrame. }
    rewrite lft_meet_comm. iMod vo_vo_alloc as (γx) "[vox vox']".
    iMod (obor_tok_subdiv (M:=M) (sm:=pbsem _) [xpreborrow _ _ γ γ' γx ξ f]
      with "[] o [pc vo' vox'] [→Φ →b']") as "[[α α'][c' _]]"=>/=.
    { iApply lft_sincl_refl. } { iSplit; [|done]. iExists _. iFrame. }
    { iIntros "#† [[%y'[pc[vo' _]]]_]". iExists (f y'). iFrame "pc".
      iApply ("→Φ" with "†"). rewrite pbor_tok_unseal. iRight. iExists _.
      iFrame "vo'". by iApply "→b'". }
    iDestruct (lft_live_combine with "α' β") as (?) "[αβ →α'β]".
    iMod (borc_tok_open (sm:=pbsem _) with "αβ c") as "[o[%[pc' Ψ]]]".
    iMod (borc_tok_open (sm:=pbsem _) with "α c'")
      as "[o'[%[pc[vo' vox']]]]".
    iDestruct (vo_vo_agree with "vox vox'") as %<-.
    iDestruct (vo_pc_agree with "vo' pc'") as %<-.
    iMod (proph_alloc y) as (η') "η'". iExists η'.
    iMod (vo_pc_preresolve (λ π, f (π η')) [Aprvar _ η'] with "[$η' //] vo pc")
      as "[[η' _][$ →pc]]".
    { apply proph_dep_constr, proph_dep_one. }
    iMod (vo_pc_alloc with "η'") as (γ'') "[vo'' pc'']".
    iMod (obor_tok_merge_subdiv (M:=M) (sm:=pbsem _) [(_,_,_)';(_,_,_)']
      [xpbor _ γ'' η' Ψ] with "[$o $o'] [pc'' Ψ] [→pc vo' pc' vox vox']")
      as "[[αβ[$_]][c _]]"=>/=.
    { iSplit; [by iApply lft_sincl_refl|]. iSplit; [|done].
      iApply lft_sincl_meet_l. }
    { iSplit; [|done]. iExists _. iFrame. }
    { iIntros "_ [[%y'[pc'' Ψ]]_]". iMod (pc_resolve with "pc''") as "obs".
      iMod (vo_pc_update with "vo' pc'") as "[vo' pc']".
      iMod (vo_vo_update with "vox vox'") as "[vox _]". iModIntro.
      iSplitL "pc' Ψ"; [iExists _; by iFrame|]. iSplit; [|done]. iExists _.
      iFrame "vo' vox". iApply "→pc".
      by iApply (proph_obs_impl with "obs")=> ? ->. }
    iModIntro. iDestruct ("→α'β" with "αβ") as "[$$]". rewrite pborc_tok_unseal.
    iRight. iExists _. iFrame.
  Qed.
  Lemma pobor_pborc_tok_reborrow {X Y α q ξ Φ β r y η Ψ} f :
    pobor_tok (X:=X) α q ξ Φ -∗ r.[β] -∗ pborc_tok (X:=Y) β y η Ψ -∗
    (∀ y', [†α] -∗ pbor_tok β y' η Ψ -∗ M (sm (Φ (f y'))))
      =[pborrow_wsat M sm]=∗ ∃ η' : prvar _,
      q.[α] ∗ r.[β] ∗ ⟨π, π ξ = f (π η')⟩ ∗ pborc_tok (α ⊓ β) y η' Ψ.
  Proof.
    iIntros "Φ β c →Φ". iMod (pborc_tok_open with "β c") as "[o Ψ]".
    iApply (pobor_pobor_tok_reborrow with "Φ o Ψ →Φ").
  Qed.
  Lemma pobor_pbor_tok_reborrow {X Y α q ξ Φ β r y η Ψ} f :
    pobor_tok (X:=X) α q ξ Φ -∗ r.[β] -∗ pbor_tok (X:=Y) β y η Ψ -∗
    (∀ y', [†α] -∗ pbor_tok β y' η Ψ -∗ M (sm (Φ (f y')))) -∗
      modw M (pborrow_wsat M sm) (∃ η' : prvar _,
      q.[α] ∗ r.[β] ∗ ⟨π, π ξ = f (π η')⟩ ∗ pborc_tok (α ⊓ β) y η' Ψ).
  Proof.
    iIntros "Φ β c →Φ". iMod (pbor_tok_open with "β c") as "[o Ψ]".
    iMod (pobor_pobor_tok_reborrow with "Φ o Ψ →Φ") as "$". by iIntros.
  Qed.
End pborrow.

(** Allocate [pborrow_wsat] *)
Lemma pborrow_wsat_alloc `{!pborrowGpreS TY FML Σ} :
  ⊢ |==> ∃ _ : pborrowGS TY FML Σ, ∀ M sm, pborrow_wsat M sm.
Proof.
  iMod proph_init as (?) "_". iMod borrow_wsat_alloc as (?) "W".
  iModIntro. iExists (PborrowGS _ _ _ _ _ _). by iIntros.
Qed.
