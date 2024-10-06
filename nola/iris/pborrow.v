(** * Prophetic borrowing *)

From nola.bi Require Export plist.
From nola.bi Require Import order.
From nola.iris Require Export borrow proph_ag cif.
From iris.proofmode Require Import proofmode.
Import ProdNotation PlistNotation FunPNotation BUpd0Notation iPropAppNotation
  LftNotation ProphNotation ModwNotation DsemNotation.

Implicit Type (TY : synty) (FML : oFunctor) (α : lft) (q : Qp).

Section pborrow.
  Context `{!borrowGS (cifOF CON) Σ, !prophGS TY Σ, !proph_agG TY Σ}.
  Implicit Type (γ : positive) (X Y : TY) (Xl Yl : list TY) (Px : cif CON Σ).

  (** ** Tokens *)

  (** Formulas for a borrower and a lender *)
  Local Definition cif_xpbor {X} γ ξ (Φx : X -d> cif CON Σ) : cif CON Σ :=
    ∃ x, ▷ proph_ctrl γ x ξ ∗ Φx x.
  Local Definition cif_xplend {X} (xπ : clair TY X) (Φx : X -d> cif CON Σ)
    : cif CON Σ :=
    ∃ x, ▷ ⟨π, xπ π = x⟩ ∗ Φx x.

  (** Formulas are non-expansive *)
  Local Instance cif_pbor_ne {X γ ξ} : NonExpansive (@cif_xpbor X γ ξ).
  Proof. unfold cif_xpbor. solve_proper. Qed.
  Local Instance cif_plend_ne {X xπ} : NonExpansive (@cif_xplend X xπ).
  Proof. unfold cif_xplend. solve_proper. Qed.

  (** Prophetic borrower token *)
  Local Definition pbor_tok_def {X} α (x : X) (ξ : prvar X)
    (Φx : X -d> cif CON Σ) : iProp Σ :=
    [†α] ∨ ∃ γ, val_obs γ x ∗ bor_tok α (cif_xpbor γ ξ Φx).
  Local Lemma pbor_tok_aux : seal (@pbor_tok_def). Proof. by eexists. Qed.
  Definition pbor_tok {X} := pbor_tok_aux.(unseal) X.
  Local Lemma pbor_tok_unseal : @pbor_tok = @pbor_tok_def.
  Proof. exact: seal_eq. Qed.

  (** Open prophetic borrower token *)
  Local Definition pobor_tok_def {X} α q (ξ : prvar X) (Φx : X -d> cif CON Σ)
    : iProp Σ :=
    ∃ γ, (∃ x, val_obs γ x ∗ proph_ctrl γ x ξ) ∗
      obor_tok α q (cif_xpbor γ ξ Φx).
  Local Lemma pobor_tok_aux : seal (@pobor_tok_def). Proof. by eexists. Qed.
  Definition pobor_tok {X} := pobor_tok_aux.(unseal) X.
  Local Lemma pobor_tok_unseal : @pobor_tok = @pobor_tok_def.
  Proof. exact: seal_eq. Qed.

  (** Prophetic lender token *)
  Definition plend_tok {X} α (xπ : clair TY X) (Φx : X -d> cif CON Σ)
    : iProp Σ :=
    lend_tok α (cif_xplend xπ Φx).

  (** Borrower and lender tokens are non-expansive *)
  #[export] Instance pbor_tok_ne {X α x ξ} :
    NonExpansive (pbor_tok (X:=X) α x ξ).
  Proof. rewrite pbor_tok_unseal. solve_proper. Qed.
  #[export] Instance pbor_tok_proper {X α x ξ} :
    Proper ((≡) ==> (⊣⊢)) (pbor_tok (X:=X) α x ξ).
  Proof. apply ne_proper, _. Qed.
  #[export] Instance pobor_tok_ne {X α q ξ} :
    NonExpansive (pobor_tok (X:=X) α q ξ).
  Proof. rewrite pobor_tok_unseal. solve_proper. Qed.
  #[export] Instance pobor_tok_proper {X α q ξ} :
    Proper ((≡) ==> (⊣⊢)) (pobor_tok (X:=X) α q ξ).
  Proof. apply ne_proper, _. Qed.
  #[export] Instance plend_tok_ne {X α xπ} :
    NonExpansive (plend_tok (X:=X) α xπ).
  Proof. solve_proper. Qed.
  #[export] Instance plend_tok_proper {X α xπ} :
    Proper ((≡) ==> (⊣⊢)) (plend_tok (X:=X) α xπ).
  Proof. apply ne_proper, _. Qed.

  (** ** Basic lemmas *)

  (** Fake a borrower token from the dead lifetime token *)
  Lemma pbor_tok_fake {X α} x ξ Φx : [†α] ⊢ pbor_tok (X:=X) α x ξ Φx.
  Proof. rewrite pbor_tok_unseal. iIntros. by iLeft. Qed.

  (** Modify the lifetime of borrower and lender tokens *)
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

  (** ** Borrows *)

  Context `{!SemCifcon JUDG CON Σ, !@ModUpd (iProp Σ) M, !ModBUpd M,
    !ModExcept0 M}.
  Implicit Type δ : JUDG -n> iProp Σ.

  (** Utility *)
  Local Definition cif_xpbors {Xl}
    (γξxΦxl : plist (λ X, _ *' _ *' X *' (X → _)) Xl) : list (cif CON Σ) :=
    of_plist (λ _ '(γ, ξ, _, Φx)', cif_xpbor γ ξ Φx) γξxΦxl.
  Local Definition cif_xplends {Xl} (xπΦxl : plist (λ X, _ *' (X → _)) Xl)
    : list (cif CON Σ) :=
    of_plist (λ _ '(xπ, Φx)', cif_xplend xπ Φx) xπΦxl.
  Local Lemma vo_pbor_alloc_list {δ Xl ξl} {xΦxl : plist _ Xl} :
    1:∗[of_plist_prvar ξl] -∗ ([∗ plist] '(x, Φx)' ∈ xΦxl, ⟦ Φx x ⟧(δ)) ==∗
      ∃ γl, let γξxΦxl := plist_zip γl (plist_zip ξl xΦxl) in
      ([∗ plist] '(γ, _, x, _)' ∈ γξxΦxl, val_obs γ x) ∗
      ([∗ list] Px ∈ cif_xpbors γξxΦxl, ⟦ Px ⟧(δ)).
  Proof.
    elim: Xl ξl xΦxl=>/=; [iIntros; by iExists ()|].
    move=> X Xl IH [ξ ξl] [[x Φx] xΦxl]. iIntros "[ξ ξl] [Φx Φxl]".
    iMod (IH with "ξl Φxl") as (γl) "[vol pborl]".
    iMod (vo_pc_alloc with "ξ") as (γ) "[vo pc]". iModIntro. iExists (γ, γl)'.
    iFrame "vo vol pborl". iExists _. iFrame.
  Qed.

  (** Body of a lender *)
  Definition xplend {X} δ (xπ : clair TY X) (Φx : X -d> cif CON Σ) : iProp Σ :=
    ∃ x, ▷ ⟨π, xπ π = x⟩ ∗ ⟦ Φx x ⟧(δ).
  Definition xplend_var {X} δ (ξ : prvar X) (Φx : X -d> cif CON Σ) : iProp Σ :=
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
  Local Lemma cif_xpbors_sem_to_plend {δ Xl γl} {ξxΦxl : plist _ Xl} :
    ([∗ list] Px ∈ cif_xpbors (plist_zip γl ξxΦxl), ⟦ Px ⟧(δ)) ==∗◇
      [∗ plist] '(ξ, _, Φx)' ∈ ξxΦxl, xplend_var δ ξ Φx.
  Proof.
    elim: Xl γl ξxΦxl=>/=; [by iIntros|]=> X Xl IH [γ γl] [[ξ[x Φx]] ξxΦxl].
    iIntros "[[%[>pc Φx]] pborl]". iMod (IH with "pborl") as "$".
    iMod (pc_resolve with "pc"). iModIntro. iExists _. iFrame.
  Qed.
  (** Create new prophetic borrowers and lenders *)
  Lemma pbor_plend_tok_new_list {δ} Xl α (xΦxl : plist _ Xl) :
    ⊢ |==> ∃ ξl, ∀ Yl (yπΨxl : plist (λ Y, _ *' (Y → _)) Yl),
      let ξxΦxl := plist_zip ξl xΦxl in
      ([∗ plist] '(x, Φx)' ∈ xΦxl, ⟦ Φx x ⟧(δ)) -∗
      ([†α] -∗ ([∗ plist] '(ξ, _, Φx)' ∈ ξxΦxl, xplend_var δ ξ Φx) -∗
        M ([∗ plist] '(yπ, Ψx)' ∈ yπΨxl, xplend δ yπ Ψx))
        =[borrow_wsat M ⟦⟧(δ)]=∗◇
        ([∗ plist] '(ξ, x, Φx)' ∈ ξxΦxl, pbor_tok α x ξ Φx) ∗
        ([∗ plist] '(yπ, Ψx)' ∈ yπΨxl, plend_tok α yπ Ψx).
  Proof.
    iMod (proph_alloc_list (plist_map (λ _, fst') xΦxl)) as (ξl) "ξl".
    iModIntro. iExists ξl. iIntros (??) "Φxl →Ψxl".
    set ξxΦxl := plist_zip ξl xΦxl.
    iMod (vo_pbor_alloc_list with "ξl Φxl") as (γl) "[vol pborl]".
    iMod (bor_lend_tok_new_list (FML:=cifOF _) (M:=M) α _ (cif_xplends yπΨxl)
      with "pborl [→Ψxl]") as "[bl ll]".
    { iStopProof. f_equiv. iIntros "→Ψxl pborl".
      iMod (cif_xpbors_sem_to_plend with "pborl"). rewrite big_sepL_of_plist.
      by iApply "→Ψxl". }
    iModIntro. rewrite !big_sepL_of_plist /=. iFrame "ll".
    iDestruct (big_sepPL_sep_2 with "vol bl") as "vobl".
    rewrite -(plist_zip_snd (xl:=γl) (yl:=ξxΦxl)) big_sepPL_map.
    iApply (big_sepPL_impl with "vobl"). iIntros "!>" (?[?[?[??]]]) "/= [vo b]".
    rewrite pbor_tok_unseal. iRight. iExists _. iFrame.
  Qed.
  (** Simply create a prophetic borrower and a prophetic lender *)
  Lemma pbor_plend_tok_new {δ} X α x Φx :
    ⟦ Φx x ⟧(δ) =[borrow_wsat M ⟦⟧(δ)]=∗◇ ∃ ξ,
      pbor_tok (X:=X) α x ξ Φx ∗ plend_tok α (λ π, π ξ) Φx.
  Proof.
    iIntros "Φx".
    iMod (pbor_plend_tok_new_list [X] α ((x, Φx)',())') as ([ξ[]]) "big".
    iExists ξ.
    iMod ("big" $! [X] ((_,_)',())' with "[Φx] []") as "[[$ _][$ _]]"=>/=;
      by [iFrame|iIntros|].
  Qed.

  (** Split a prophetic lender *)
  Lemma plend_tok_split {δ X α xπ Φx} Yl
    (yπΨxl : plist (λ Y, _ *' (Y → _)) Yl) :
    plend_tok (X:=X) α xπ Φx -∗
    (xplend δ xπ Φx -∗ M ([∗ plist] '(yπ, Ψx)' ∈ yπΨxl, xplend δ yπ Ψx))
      =[borrow_wsat M ⟦⟧(δ)]=∗◇ [∗ plist] '(yπ, Ψx)' ∈ yπΨxl, plend_tok α yπ Ψx.
  Proof.
    iIntros "/=l →Ψxl".
    iMod (lend_tok_split (FML:=cifOF _) (M:=M) (cif_xplends yπΨxl)
      with "l [→Ψxl]"); by rewrite big_sepL_of_plist.
  Qed.

  (** Retrieve from a prophetic lender *)
  Lemma plend_tok_retrieve {δ X α xπ Φx} :
    [†α] -∗ plend_tok (X:=X) α xπ Φx -∗ modw M (borrow_wsat M ⟦⟧(δ))
      (xplend δ xπ Φx).
  Proof. exact: lend_tok_retrieve. Qed.

  (** Open a prophetic borrower *)
  Lemma pbor_tok_open {δ X α q x ξ Φx} :
    q.[α] -∗ pbor_tok (X:=X) α x ξ Φx -∗ modw M (borrow_wsat M ⟦⟧(δ))
      (pobor_tok α q ξ Φx ∗ ⟦ Φx x ⟧(δ)).
  Proof.
    rewrite pbor_tok_unseal pobor_tok_unseal. iIntros "α [†|[%[vo b]]]".
    { iDestruct (lft_live_dead with "α †") as %[]. }
    iMod (bor_tok_open (M:=M) with "α b") as "/=[o[%[>pc Φx]]]".
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
      ([∗ list] '(α, q, Px)' ∈ of_plist
        (λ _ '(γ, α, q, ξ, Φx, _)', (α, q, cif_xpbor γ ξ Φx)') γαqξΦxfl,
        β ⊑□ α ∗ obor_tok α q Px) ∗
      ∀ yl', ⟨π, app_plist_prvar π ηl = yl'⟩ -∗
        [∗ plist] '(γ, _, _, ξ, _, f)' ∈ γαqξΦxfl, proph_ctrl γ (f yl') ξ.
  Proof.
    rewrite /= pobor_tok_unseal. elim: Xl αqξΦxfl=>/=.
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
  Local Lemma cif_xpbors_sem_to_obs_sem {δ Yl γl' ηl} {yΨxl : plist _ Yl} :
    ([∗ list] Qx ∈ cif_xpbors (plist_zip γl' (plist_zip ηl yΨxl)), ⟦ Qx ⟧(δ))
      ==∗◇ ∃ yl', ⟨π, app_plist_prvar π ηl = yl'⟩ ∗
      [∗ plist] '(y', _, Ψx)' ∈ plist_zip yl' yΨxl, ⟦ Ψx y' ⟧(δ).
  Proof.
    elim: Yl γl' ηl yΨxl=>/=.
    { iIntros (_ [] _ _) "!>". iExists (). iSplit; [|done].
      by iApply proph_obs_true. }
    move=> Y Yl IH [γ' γl'] [η ηl] [[y Ψx] yΨxl].
    iIntros "[[%y'[>pc Ψx]] pborl]".
    iMod (IH with "pborl") as (yl') "[obs Ψxl]".
    iExists (y', yl')'. iFrame "Ψx Ψxl". iMod (pc_resolve with "pc") as "obs'".
    iModIntro. by iApply (proph_obs_impl2 with "obs obs'")=>/= ? <- <-.
  Qed.
  (** Merge and subdivide prophetic borrowers *)
  Lemma pobor_tok_merge_subdiv {δ} Xl Yl
    (αqξΦxfl : plist (λ X, _ *' _ *' _ *' _ *' (_ → X)) Xl) (yΨxl : plist _ Yl)
    Rxl β :
    ([∗ plist] '(α, q, ξ, Φx, _)' ∈ αqξΦxfl, β ⊑□ α ∗ pobor_tok α q ξ Φx) -∗
    ([∗ plist] '(y, Ψx)' ∈ yΨxl, ⟦ Ψx y ⟧(δ)) -∗
    ([∗ list] Rx ∈ Rxl, ⟦ Rx ⟧(δ)) -∗
    (∀ yl', [†β] -∗
      ([∗ plist] '(y', _, Ψx)' ∈ plist_zip yl' yΨxl, ⟦ Ψx y' ⟧(δ)) -∗
      ([∗ list] Rx ∈ Rxl, ⟦ Rx ⟧(δ)) -∗ M
        ([∗ plist] '(_, _, _, Φx, f)' ∈ αqξΦxfl, ⟦ Φx (f yl') ⟧(δ)))
      =[borrow_wsat M ⟦⟧(δ)]=∗◇ ∃ ηl,
      ([∗ plist] '(α, q, _)' ∈ αqξΦxfl, q.[α]) ∗
      ([∗ plist] '(_, _, ξ, _, f)' ∈ αqξΦxfl,
        ⟨π, π (Aprvar _ ξ) = f (app_plist_prvar π ηl)⟩) ∗
      ([∗ plist] '(η, y, Ψx)' ∈ plist_zip ηl yΨxl, pbor_tok β y η Ψx) ∗
      [∗ list] Rx ∈ Rxl, bor_tok β Rx.
  Proof.
    iIntros "ol Ψxl Rxl →Φxl".
    iMod (proph_alloc_list (plist_map (λ _, fst') yΨxl)) as (ηl) "ηl".
    iExists ηl. iMod (pobor_preresolve with "ηl ol") as (γl) "[ηl[$[ol →pcl]]]".
    iMod (vo_pbor_alloc_list with "ηl Ψxl") as (γl') "[vol pborl]".
    iMod (obor_tok_merge_subdiv (M:=M) _ (_ ++ _)
      with "ol [pborl Rxl] [→Φxl →pcl]") as "[αl bl]"; rewrite big_sepL_app.
    { by iStopProof. }
    { iIntros "† [pborl Rxl]".
      iMod (cif_xpbors_sem_to_obs_sem with "pborl") as (yl') "[obs Ψxl]".
      iMod ("→Φxl" with "† Ψxl Rxl") as "Φxl". iModIntro.
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
  Lemma pobor_tok_subdiv {δ X α q ξ Φx} Yl (f : _ → X) (yΨxl : plist _ Yl) Rxl
    β :
    β ⊑□ α -∗ pobor_tok α q ξ Φx -∗ ([∗ plist] '(y, Ψx)' ∈ yΨxl, ⟦ Ψx y ⟧(δ)) -∗
    ([∗ list] Rx ∈ Rxl, ⟦ Rx ⟧(δ)) -∗
    (∀ yl', [†β] -∗
      ([∗ plist] '(y', _, Ψx)' ∈ plist_zip yl' yΨxl, ⟦ Ψx y' ⟧(δ)) -∗
      ([∗ list] Rx ∈ Rxl, ⟦ Rx ⟧(δ)) -∗ M ⟦ Φx (f yl') ⟧(δ))
      =[borrow_wsat M ⟦⟧(δ)]=∗◇ ∃ ηl,
      q.[α] ∗ ⟨π, π (Aprvar _ ξ) = f (app_plist_prvar π ηl)⟩ ∗
      ([∗ plist] '(η, y, Ψx)' ∈ plist_zip ηl yΨxl, pbor_tok β y η Ψx) ∗
      [∗ list] Rx ∈ Rxl, bor_tok β Rx.
  Proof.
    iIntros "⊑ o Ψxl Rxl →Φx".
    iMod (pobor_tok_merge_subdiv [_] _ ((_,_,_,_,_)',())'
      with "[$⊑ $o //] Ψxl Rxl [→Φx]") as (ηl) "big"=>/=.
    { iIntros (?). by rewrite bi.sep_emp. }
    iExists ηl. by iDestruct "big" as "/=[[$ _][[$ _]$]]".
  Qed.

  (** Resolve the prophecy of a prophetic borrower *)
  Lemma pobor_tok_resolve {δ X α q ξ Φx} x :
    pobor_tok (X:=X) α q ξ Φx -∗ ⟦ Φx x ⟧(δ) =[borrow_wsat M ⟦⟧(δ)]=∗◇
      q.[α] ∗ ⟨π, π ξ = x⟩ ∗ bor_tok α (Φx x).
  Proof.
    iIntros "o Φx".
    iMod (pobor_tok_subdiv [] (λ _, x) () [Φx x] with "[] o [//] [Φx] []")
      as (?) "[$[$[_[$ _]]]]"=>/=;
      by [iApply lft_sincl_refl|iFrame|iIntros "% _ _ [$ _]"|].
  Qed.
  Lemma pbor_tok_resolve {δ X α q x ξ Φx} :
    q.[α] -∗ pbor_tok (X:=X) α x ξ Φx -∗ modw M (borrow_wsat M ⟦⟧(δ))
      (q.[α] ∗ ⟨π, π ξ = x⟩ ∗ bor_tok α (Φx x)).
  Proof.
    iIntros "α b". iMod (pbor_tok_open with "α b") as "[o Φx]".
    by iMod (pobor_tok_resolve with "o Φx").
  Qed.

  (** Subdivide a prophetic borrower without changing the prophecy *)
  Lemma pobor_tok_nsubdiv {δ X α q ξ Φx} Ψx x β :
    β ⊑□ α -∗ pobor_tok (X:=X) α q ξ Φx -∗ ⟦ Ψx x ⟧(δ) -∗
    (∀ x', [†β] -∗ ⟦ Ψx x' ⟧(δ) -∗ M ⟦ Φx x' ⟧(δ)) =[borrow_wsat M ⟦⟧(δ)]=∗
      q.[α] ∗ pbor_tok β x ξ Ψx.
  Proof.
    rewrite pobor_tok_unseal pbor_tok_unseal.
    iIntros "⊑ [%[[%[vo pc]] o]] Ψx →Φx".
    iMod (vo_pc_update with "vo pc") as "[vo pc]".
    iMod (obor_tok_subdiv (FML:=cifOF _) (M:=M) [cif_xpbor _ _ Ψx]
      with "⊑ o [pc Ψx] [→Φx]") as "[$[_[? _]]]"=>/=.
    { iSplit; [|done]. iExists _. iFrame. }
    { iIntros "† [[%[pc Ψx]]_]". iMod ("→Φx" with "† Ψx") as "Φx". iModIntro.
      iExists _. iFrame. }
    iModIntro. iRight. iExists _. iFrame.
  Qed.
  (** Simply close a prophetic borrower *)
  Lemma pobor_tok_close {δ X α q ξ Φx} x :
    pobor_tok (X:=X) α q ξ Φx -∗ ⟦ Φx x ⟧(δ) =[borrow_wsat M ⟦⟧(δ)]=∗
      q.[α] ∗ pbor_tok α x ξ Φx.
  Proof.
    iIntros "o Φx". iApply (pobor_tok_nsubdiv Φx with "[] o Φx"); [|by iIntros].
    iApply lft_sincl_refl.
  Qed.

  (** Reborrow a nested prophetic borrower *)
  Lemma pobor_pobor_tok_reborrow {δ X Y α q ξ Φx β r η Ψx} y f : β ⊑□ α -∗
    pobor_tok (X:=X) β q ξ Φx -∗ pobor_tok (X:=Y) α r η Ψx -∗ ⟦ Ψx y ⟧(δ) -∗
    (∀ y', [†β] -∗ pbor_tok α y' η Ψx -∗ M ⟦ Φx (f y') ⟧(δ)) -∗
      modw M (borrow_wsat M ⟦⟧(δ)) (∃ η' : prvar _,
      q.[β] ∗ r.[α] ∗ ⟨π, π ξ = f (π η')⟩ ∗ pbor_tok β y η' Ψx).
  Proof.
    rewrite pobor_tok_unseal.
    iIntros "#⊑ [%γ[[%[vo pc]] o]] [%γ'[[%[vo' pc']] o']] Ψx →Φx".
    iMod (vo_pc_update with "vo pc") as "[vo pc]".
    iMod (vo_pc_update with "vo' pc'") as "[vo' pc']".
    iMod (obor_tok_reborrow (M:=M) β with "⊑ o' [pc' Ψx]") as "($ & →b' & b)".
    { iExists _. iFrame. }
    iMod vo_vo_alloc as (γx) "[vox vox']".
    iMod (obor_tok_subdiv (FML:=cifOF _) (M:=M)
      [▷ ∃ y, proph_ctrl γ (f y) ξ ∗ val_obs γ' y ∗ val_obs γx y]%cif
      with "[] o [pc vo' vox'] [→Φx →b']") as "[[β β'][_[b' _]]]"=>/=.
    { iApply lft_sincl_refl. } { iSplit; [|done]. iExists _. iFrame. }
    { iIntros "#† [>[%y'[pc[vo' _]]]_]". iExists (f y'). iFrame "pc".
      iApply ("→Φx" with "†"). rewrite pbor_tok_unseal. iRight. iExists _.
      iFrame "vo'". by iApply "→b'". }
    iMod (bor_tok_open (M:=M) with "β b") as "/=[o [%[>pc' Ψx]]]".
    iMod (bor_tok_open (M:=M) with "β' b'") as "/=[o' >[%[pc[vo' vox']]]]".
    iDestruct (vo_vo_agree with "vox vox'") as %<-.
    iDestruct (vo_pc_agree with "vo' pc'") as %<-.
    iMod (proph_alloc y) as (η') "η'". iExists η'.
    iMod (vo_pc_preresolve (λ π, f (π η')) [Aprvar _ η'] with "[$η' //] vo pc")
      as "[[η' _][$ →pc]]".
    { apply proph_dep_constr, proph_dep_one. }
    iMod (vo_pc_alloc with "η'") as (γ'') "[vo'' pc'']".
    iMod (obor_tok_merge_subdiv (FML:=cifOF _) (M:=M) [(_,_,_)';(_,_,_)']
      [cif_xpbor γ'' η' Ψx] with "[$o $o'] [pc'' Ψx] [→pc vo' pc' vox vox']")
      as "[([$ _] & [$ _] & _) [b _]]"=>/=.
    { iSplit; [|iSplit=>//]; iApply lft_sincl_refl. }
    { iSplit; [|done]. iExists _. iFrame. }
    { iIntros "_ [[%y'[>pc'' Ψx]]_]". iMod (pc_resolve with "pc''") as "obs".
      iMod (vo_pc_update with "vo' pc'") as "[vo' pc']".
      iMod (vo_vo_update with "vox vox'") as "[vox _]". iModIntro.
      iSplitL "pc' Ψx"; [iExists _; by iFrame|]. iSplit; [|done]. iExists _.
      iFrame "vo' vox". iApply "→pc".
      by iApply (proph_obs_impl with "obs")=> ? ->. }
    iModIntro. rewrite pbor_tok_unseal. iRight. iExists _. iFrame.
  Qed.
  Lemma pobor_pbor_tok_reborrow {δ X Y α q ξ Φx β r y η Ψx} f : β ⊑□ α -∗
    pobor_tok (X:=X) β q ξ Φx -∗ r.[α] -∗ pbor_tok (X:=Y) α y η Ψx -∗
    (∀ y', [†β] -∗ pbor_tok α y' η Ψx -∗ M ⟦ Φx (f y') ⟧(δ)) -∗
      modw M (borrow_wsat M ⟦⟧(δ)) (∃ η' : prvar _,
      q.[β] ∗ r.[α] ∗ ⟨π, π ξ = f (π η')⟩ ∗ pbor_tok β y η' Ψx).
  Proof.
    iIntros "⊑ Φx β b →Φx". iMod (pbor_tok_open with "β b") as "[o Ψx]".
    iApply (pobor_pobor_tok_reborrow with "⊑ Φx o Ψx →Φx").
  Qed.
End pborrow.

(** ** Notation *)
Notation xplendd := (xplend der).
Notation xplendd_var := (xplend_var der).
