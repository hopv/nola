(** * Prophetic borrowing *)

From nola.iris Require Export plist borrow proph_ag.
From iris.proofmode Require Import proofmode.

Implicit Type (α : lft) (q : Qp).

(** Proposition for prophetic borrowing *)
Variant pbprop (TY : synty) (PROP : Type) : Type :=
| (* Just a proposition *) pbprop_just (P : PROP)
| (* For prophetic borrower *) #[local] pbprop_pbor
    {X : TY} (γ : gname) (ξ : prvar X) (Φ : X → PROP)
| (* For prophetic lender *) pbprop_plend
    {X : TY} (xπ : proph TY X) (Φ : X → PROP)
| (* For prophetic reborrowing *) #[local] pbprop_preborrow
    {X Y : TY} (γ γ' γx : gname) (ξ : prvar X) (f : Y → X).
Arguments pbprop_just {_ _} _.
Arguments pbprop_pbor {_ _ _} _ _ _.
Arguments pbprop_plend {_ _ _} _ _.
Arguments pbprop_preborrow {_ _ _ _} _ _ _ _ _.

(** Ghost state *)
Class pborrowGS TY PROP Σ := PborrowGS {
  pborrowGS_borrow :: borrowGS (pbprop TY PROP) Σ;
  pborrowGS_proph :: prophGS TY Σ;
  pborrowGS_proph_ag : proph_agG TY Σ;
}.
Local Existing Instance pborrowGS_proph_ag.
Class pborrowGpreS TY PROP Σ := PborrowGpreS {
  pborrowGpreS_borrow :: borrowGpreS (pbprop TY PROP) Σ;
  pborrowGpreS_proph :: prophGpreS TY Σ;
  pborrowGpreS_proph_ag : proph_agG TY Σ;
}.
Local Existing Instance pborrowGpreS_proph_ag.
Definition pborrowΣ TY PROP :=
  #[borrowΣ (pbprop TY PROP); prophΣ TY; proph_agΣ TY].
#[export] Instance subG_pborrow `{!subG (pborrowΣ TY PROP) Σ} :
  pborrowGpreS TY PROP Σ.
Proof. solve_inG. Qed.

Section pborrow.
  Context `{!pborrowGS TY PROP Σ}.
  Implicit Type (M : iProp Σ → iProp Σ) (intp : PROP → iProp Σ) (X : TY)
    (P : PROP) (Px : pbprop TY PROP).

  (** ** Tokens *)

  (** Prophetic borrower token *)
  Local Definition pbor_ctok_def {X} α (ξ : prvar X) (x : X) (Φ : X → PROP)
    : iProp Σ :=
    [†α] ∨ ∃ γ, val_obs γ x ∗ bor_ctok α (pbprop_pbor γ ξ Φ).
  Local Lemma pbor_ctok_aux : seal (@pbor_ctok_def). Proof. by eexists. Qed.
  Definition pbor_ctok {X} := pbor_ctok_aux.(unseal) X.
  Local Lemma pbor_ctok_unseal : @pbor_ctok = @pbor_ctok_def.
  Proof. exact: seal_eq. Qed.
  Local Definition pbor_tok_def {X} α (ξ : prvar X) (x : X) (Φ : X → PROP)
    : iProp Σ :=
    [†α] ∨ ∃ γ, val_obs γ x ∗ bor_tok α (pbprop_pbor γ ξ Φ).
  Local Lemma pbor_tok_aux : seal (@pbor_tok_def). Proof. by eexists. Qed.
  Definition pbor_tok {X} := pbor_tok_aux.(unseal) X.
  Local Lemma pbor_tok_unseal : @pbor_tok = @pbor_tok_def.
  Proof. exact: seal_eq. Qed.

  (** Open prophetic borrower token *)
  Local Definition opbor_tok_def {X} α q (ξ : prvar X) (Φ : X → PROP)
    : iProp Σ :=
    ∃ γ, (∃ x, val_obs γ x ∗ proph_ctrl γ x ξ) ∗
      obor_tok α q (pbprop_pbor γ ξ Φ).
  Local Lemma opbor_tok_aux : seal (@opbor_tok_def). Proof. by eexists. Qed.
  Definition opbor_tok {X} := opbor_tok_aux.(unseal) X.
  Local Lemma opbor_tok_unseal : @opbor_tok = @opbor_tok_def.
  Proof. exact: seal_eq. Qed.

  (** Prophetic lender token *)
  Definition plend_tok {X} α (xπ : proph TY X) (Φ : X → PROP) : iProp Σ :=
    lend_tok α (pbprop_plend xπ Φ).

  (** Non-prophetic token *)
  Definition nbor_ctok α P : iProp Σ := bor_ctok α (pbprop_just P).
  Definition nbor_tok α P : iProp Σ := bor_tok α (pbprop_just P).
  Definition onbor_tok α q P : iProp Σ := obor_tok α q (pbprop_just P).
  Local Definition nlend_tok α P : iProp Σ := lend_tok α (pbprop_just P).

  (** Prophetic borrower and lender tokens are timeless *)
  #[export] Instance pbor_ctok_timeless {α X ξ x Φ} :
    Timeless (pbor_ctok (X:=X) α ξ x Φ).
  Proof. rewrite pbor_ctok_unseal. exact _. Qed.
  #[export] Instance pbor_tok_timeless {α X ξ x Φ} :
    Timeless (pbor_tok (X:=X) α ξ x Φ).
  Proof. rewrite pbor_tok_unseal. exact _. Qed.
  #[export] Instance opbor_tok_timeless {α q X ξ Φ} :
    Timeless (opbor_tok (X:=X) α q ξ Φ).
  Proof. rewrite opbor_tok_unseal. exact _. Qed.
  Fact plend_tok_timeless {α X xπ Φ} :
    Timeless (plend_tok (X:=X) α xπ Φ).
  Proof. exact _. Qed.

  (** Turn [pbor_ctok] to [pbor_tok] *)
  Lemma pbor_ctok_tok {α X x ξ Φ} : pbor_ctok (X:=X) α ξ x Φ ⊢ pbor_tok α ξ x Φ.
  Proof.
    rewrite pbor_ctok_unseal pbor_tok_unseal /pbor_ctok_def.
    by setoid_rewrite bor_ctok_tok.
  Qed.

  (** Fake a prophetic borrower token from the dead lifetime token *)
  Lemma pbor_ctok_fake {α X ξ x Φ} : [†α] ⊢ pbor_ctok (X:=X) α ξ x Φ.
  Proof. rewrite pbor_ctok_unseal. iIntros. by iLeft. Qed.
  Lemma pbor_tok_fake {α X ξ x Φ} : [†α] ⊢ pbor_tok (X:=X) α ξ x Φ.
  Proof. rewrite pbor_tok_unseal. iIntros. by iLeft. Qed.
  (** Modify the lifetime of borrower and lender tokens *)
  Lemma pbor_ctok_lft {α β X ξ x Φ} :
    β ⊑□ α -∗ pbor_ctok (X:=X) α ξ x Φ -∗ pbor_ctok β ξ x Φ.
  Proof.
    rewrite pbor_ctok_unseal. iIntros "#? [?|[%[vo ?]]]".
    { iLeft. by iApply lft_sincl_dead. }
    iRight. iExists _. iFrame "vo". by iApply bor_ctok_lft.
  Qed.
  Lemma pbor_tok_lft {α β X ξ x Φ} :
    β ⊑□ α -∗ pbor_tok (X:=X) α ξ x Φ -∗ pbor_tok β ξ x Φ.
  Proof.
    rewrite pbor_tok_unseal. iIntros "#? [?|[%[vo ?]]]".
    { iLeft. by iApply lft_sincl_dead. }
    iRight. iExists _. iFrame "vo". by iApply bor_tok_lft.
  Qed.
  Lemma opbor_tok_lft {α β q r X ξ Φ} :
    β ⊑□ α -∗ (q.[α] -∗ r.[β]) -∗ opbor_tok (X:=X) α q ξ Φ -∗ opbor_tok β r ξ Φ.
  Proof.
    rewrite opbor_tok_unseal. iIntros "⊑ →β [%[vopc o]]". iExists _.
    iFrame "vopc". iApply (obor_tok_lft with "⊑ →β o").
  Qed.
  Lemma plend_tok_lft {α β X xπ Φ} :
    α ⊑□ β -∗ plend_tok (X:=X) α xπ Φ -∗ plend_tok β xπ Φ.
  Proof. exact lend_tok_lft. Qed.

  (** Take out a prophecy variable from an open prophetic borrower *)
  Lemma opbor_proph_tok {α q X ξ Φ} :
    opbor_tok (X:=X) α q ξ Φ -∗ 1:[ξ] ∗ (1:[ξ] -∗ opbor_tok α q ξ Φ).
  Proof.
    rewrite opbor_tok_unseal. iIntros "[%[[%[vo pc]] o]]".
    iDestruct (vo_pc_vo_proph with "vo pc") as "[vo[vo' $]]". iIntros "ξ".
    iExists _. iFrame "o". iExists _. iFrame "vo".
    iApply (vo_proph_pc with "vo' ξ").
  Qed.

  (** ** World satisfaction *)

  (** Body of a prophetic lender *)
  Definition plend_body intp {X} (xπ : proph TY X) (Φ : X → PROP) : iProp Σ :=
    ∃ y, ⟨π, xπ π = y⟩ ∗ intp (Φ y).
  Definition plend_body' intp {X} (ξ : prvar X) (Φ : X → PROP) : iProp Σ :=
    plend_body intp (λ π, π ξ) Φ.

  (** Interpretation of [pbprop] *)
  Definition pbintp intp Px : iProp Σ := match Px with
    | pbprop_just P => intp P
    | pbprop_pbor γ ξ Φ => ∃ x, proph_ctrl γ x ξ ∗ intp (Φ x)
    | pbprop_plend xπ Φ => plend_body intp xπ Φ
    | pbprop_preborrow γ γ' γx ξ f =>
        ∃ y, proph_ctrl γ (f y) ξ ∗ val_obs γ' y ∗ val_obs γx y
    end.

  (** World satisfaction *)
  Definition pborrow_wsat M intp : iProp Σ :=
    borrow_wsat (modw M proph_wsat) (pbintp intp).

  (** ** For non-prophetic borrowing *)

  (** Create new borrowers and lenders *)
  Lemma nbor_nlend_tok_new_list `{!GenUpd M} {intp} α Pl Ql :
    ([∗ list] P ∈ Pl, intp P) -∗
    ([†α] -∗ ([∗ list] P ∈ Pl, intp P) -∗
      modw M proph_wsat ([∗ list] Q ∈ Ql, intp Q)%I) =[pborrow_wsat M intp]=∗
      ([∗ list] P ∈ Pl, nbor_ctok α P) ∗ [∗ list] Q ∈ Ql, nlend_tok α Q.
  Proof.
    iIntros "Pl →Ql".
    iMod (bor_lend_tok_new_list (M:=modw M _)
      α (pbprop_just <$> Pl) (pbprop_just <$> Ql) with "[Pl] [→Ql]");
    by rewrite !big_sepL_fmap.
  Qed.
  Lemma nbor_nlend_tok_new `{!GenUpd M} {intp} α P :
    intp P =[pborrow_wsat M intp]=∗ nbor_ctok α P ∗ nlend_tok α P.
  Proof.
    iIntros "P". iMod (nbor_nlend_tok_new_list α [P] [P] with "[P] []")
      as "[[$_][$_]]"; by [iFrame|iIntros|].
  Qed.

  (** Extend a lender *)
  Lemma nlend_tok_extend `{!GenUpd M} {intp α P} Ql :
    nlend_tok α P -∗ (intp P -∗ modw M proph_wsat ([∗ list] Q ∈ Ql, intp Q))
      =[pborrow_wsat M intp]=∗ [∗ list] Q ∈ Ql, nlend_tok α Q.
  Proof.
    iIntros "l →Ql".
    iMod (lend_tok_extend (M:=modw M _) (pbprop_just <$> Ql) with "l [→Ql]");
      by rewrite !big_sepL_fmap.
  Qed.

  (** Retrieve from a lender *)
  Lemma nlend_tok_retrieve `{!GenUpd M} {intp α P} :
    [†α] -∗ nlend_tok α P -∗ modw M (proph_wsat ∗ pborrow_wsat M intp) (intp P).
  Proof. rewrite -modw_modw_sep. exact lend_tok_retrieve. Qed.

  (** Open a borrower *)
  Lemma nbor_ctok_open {M intp α q P} :
    q.[α] -∗ nbor_ctok α P =[pborrow_wsat M intp]=∗ onbor_tok α q P ∗ intp P.
  Proof. exact bor_ctok_open. Qed.
  Lemma nbor_tok_open `{!GenUpd M} {intp α q P} :
    q.[α] -∗ nbor_tok α P -∗
      modw M (proph_wsat ∗ pborrow_wsat M intp) (onbor_tok α q P ∗ intp P).
  Proof. rewrite -modw_modw_sep. exact bor_tok_open. Qed.

  (** Merge and subdivide open borrowers *)
  Lemma onbor_tok_merge_subdiv `{!GenUpd M} {intp α} qPl Ql :
    ([∗ list] '(q, P)' ∈ qPl, onbor_tok α q P) -∗ ([∗ list] Q ∈ Ql, intp Q) -∗
    ([†α] -∗ ([∗ list] Q ∈ Ql, intp Q) -∗
      modw M proph_wsat ([∗ list] P ∈ qPl.*2', intp P)%I)
      =[pborrow_wsat M intp]=∗
      ([∗ list] q ∈ qPl.*1', q.[α]) ∗ [∗ list] Q ∈ Ql, nbor_ctok α Q.
  Proof.
    iIntros "ol Ql →Pl".
    iMod (obor_tok_merge_subdiv (M:=modw M _)
      ((λ '(q, P)', (q, pbprop_just P)') <$> qPl) (pbprop_just <$> Ql)
      with "[ol] [Ql] [→Pl]"); by rewrite !big_sepL_fmap /=.
  Qed.
  Lemma onbor_tok_subdiv `{!GenUpd M} {intp α q P} Ql :
    onbor_tok α q P -∗ ([∗ list] Q ∈ Ql, intp Q) -∗
    ([†α] -∗ ([∗ list] Q ∈ Ql, intp Q) -∗ modw M proph_wsat (intp P))
      =[pborrow_wsat M intp]=∗ q.[α] ∗ [∗ list] Q ∈ Ql, nbor_ctok α Q.
  Proof.
    iIntros "o Ql →P".
    iMod (onbor_tok_merge_subdiv [(_,_)'] with "[o] Ql [→P]") as "[[$ _]$]"=>/=;
      by [iFrame|rewrite bi.sep_emp|].
  Qed.
  Lemma onbor_tok_close `{!GenUpd M} {intp α q P} :
    onbor_tok α q P -∗ intp P =[pborrow_wsat M intp]=∗ q.[α] ∗ nbor_ctok α P.
  Proof.
    iIntros "o P". iMod (onbor_tok_subdiv [P] with "o [P] []") as "[$[$_]]"=>/=;
      by [iFrame|iIntros "_[$_]$"|].
  Qed.

  (** Reborrow *)
  Lemma onbor_tok_reborrow `{!GenUpd M} {intp α q P} β :
    onbor_tok α q P -∗ intp P =[pborrow_wsat M intp]=∗
      q.[α] ∗ nbor_ctok (α ⊓ β) P ∗ ([†β] -∗ nbor_tok α P).
  Proof. exact: obor_tok_reborrow. Qed.
  Lemma nbor_ctok_reborrow `{!GenUpd M} {intp α q P} β :
    q.[α] -∗ nbor_ctok α P =[pborrow_wsat M intp]=∗
      q.[α] ∗ nbor_ctok (α ⊓ β) P ∗ ([†β] -∗ nbor_tok α P).
  Proof. exact: bor_ctok_reborrow. Qed.
  Lemma nbor_tok_reborrow `{!GenUpd M} {intp α q P} β :
    q.[α] -∗ nbor_tok α P -∗ modw M (proph_wsat ∗ pborrow_wsat M intp)
      (q.[α] ∗ nbor_ctok (α ⊓ β) P ∗ ([†β] -∗ nbor_tok α P)).
  Proof. rewrite -modw_modw_sep. exact: bor_tok_reborrow. Qed.

  (** ** On prophetic borrowing *)

  (** Utility *)
  Local Definition pbor_list {Xl}
    (γξxΦl : plist (λ X, _ *' _ *' X *' (X → PROP)) Xl) :=
    of_plist (λ _ '(γ, ξ, x, Φ)', pbprop_pbor γ ξ Φ) γξxΦl.
  Local Definition plend_list {Xl}
    (xπΦl : plist (λ X : TY, proph TY X *' (X → PROP)) Xl) :=
    of_plist (λ _ '(xπ, Φ)', pbprop_plend xπ Φ) xπΦl.
  Local Lemma vo_pbor_alloc_list {intp Xl ξl} {xΦl : plist _ Xl} :
    1:∗[of_plist_prvar ξl] -∗ ([∗ plist] '(x, Φ)' ∈ xΦl, intp (Φ x)) ==∗ ∃ γl,
      let γξxΦl := plist_zip γl (plist_zip ξl xΦl) in
      ([∗ plist] '(γ, _, x, _)' ∈ γξxΦl, val_obs γ x) ∗
      ([∗ list] Px ∈ pbor_list γξxΦl, pbintp intp Px).
  Proof.
    elim: Xl ξl xΦl=>/=; [iIntros; by iExists ()|]=> X Xl IH [ξ ξl] [[x Φ] xΦl].
    iIntros "[ξ ξl] [Φ Φl]". iMod (IH with "ξl Φl") as (γl) "[vol pborl]".
    iMod (vo_pc_alloc with "ξ") as (γ) "[vo pc]". iModIntro. iExists (γ, γl)'.
    iFrame "vo vol pborl". iExists _. iFrame.
  Qed.

  (** Lemma for [pbor_plend_tok_new_list] *)
  Local Lemma pbor_list_intp_to_plend {intp Xl γl} {ξxΦl : plist _ Xl} :
    ([∗ list] Px ∈ pbor_list (plist_zip γl ξxΦl), pbintp intp Px)
      =[proph_wsat]=∗ [∗ plist] '(ξ, x, Φ)' ∈ ξxΦl, plend_body' intp ξ Φ.
  Proof.
    elim: Xl γl ξxΦl=>/=; [by iIntros|]=> X Xl IH [γ γl] [[ξ[x Φ]] ξxΦl].
    iIntros "[[%[pc Φ]] pborl]". iMod (IH with "pborl") as "$".
    iMod (pc_resolve with "pc") as "?". iModIntro. iExists _. iFrame.
  Qed.
  (** Create new prophetic borrowers and lenders *)
  Lemma pbor_plend_tok_new_list `{!GenUpd M} {intp} α Xl
    (xΦl : plist (λ X : TY, X *' (X → PROP)) Xl) :
    ⊢ |=[proph_wsat]=> ∃ ξl,
      ∀ Yl (yπΨl : plist (λ Y : TY, proph TY Y *' (Y → PROP)) Yl),
      let ξxΦl := plist_zip ξl xΦl in
      ([∗ plist] '(x, Φ)' ∈ xΦl, intp (Φ x)) -∗
      ([†α] -∗ ([∗ plist] '(ξ, x, Φ)' ∈ ξxΦl, plend_body' intp ξ Φ) -∗
        modw M proph_wsat ([∗ plist] '(yπ, Ψ)' ∈ yπΨl, plend_body intp yπ Ψ))
        =[pborrow_wsat M intp]=∗
        ([∗ plist] '(ξ, x, Φ)' ∈ ξxΦl, pbor_ctok α ξ x Φ) ∗
        ([∗ plist] '(yπ, Ψ)' ∈ yπΨl, plend_tok α yπ Ψ).
  Proof.
    iMod (proph_alloc_list (plist_map (λ _, fst') xΦl)) as (ξl) "ξl".
    iModIntro. iExists ξl. iIntros (??) "Φl →Ψl".
    set ξxΦl := plist_zip ξl xΦl.
    iMod (vo_pbor_alloc_list with "ξl Φl") as (γl) "[vol pborl]".
    iMod (bor_lend_tok_new_list (M:=modw M _) α _ (plend_list yπΨl)
      with "pborl [→Ψl]") as "[bl ll]".
    { iStopProof. f_equiv. iIntros "→Ψl pborl".
      iMod (pbor_list_intp_to_plend with "pborl"). rewrite big_sepL_of_plist.
      by iApply "→Ψl". }
    iModIntro. rewrite !big_sepL_of_plist /=. iFrame "ll".
    iDestruct (big_sepPL_sep_2 with "vol bl") as "vobl".
    rewrite -(plist_zip_snd (xl:=γl) (yl:=ξxΦl)) big_sepPL_map.
    iApply (big_sepPL_impl with "vobl"). iIntros "!>" (?[?[?[??]]]) "/= [vo b]".
    rewrite pbor_ctok_unseal. iRight. iExists _. iFrame.
  Qed.
  (** Simply create a prophetic borrower and a prophetic lender *)
  Lemma pbor_plend_tok_new `{!GenUpd M} {intp} α X x Φ :
    intp (Φ x) =[proph_wsat ∗ pborrow_wsat M intp]=∗ ∃ ξ,
      pbor_ctok (X:=X) α ξ x Φ ∗ plend_tok α (λ π, π ξ) Φ.
  Proof.
    iIntros "Φ".
    iMod (pbor_plend_tok_new_list α [X] ((x, Φ)', ())') as ([ξ[]]) "big".
    iExists ξ.
    iMod ("big" $! [X] ((_,_)', ())' with "[Φ] []") as "[[$ _][$ _]]"=>/=;
      by [iFrame|iIntros|].
  Qed.

  (** Extend a prophetic lender *)
  Lemma plend_tok_extend `{!GenUpd M} {intp α X xπ Φ} Yl
    (yπΨl : plist (λ Y : TY, proph TY Y *' (Y → PROP)) Yl) :
    plend_tok (X:=X) α xπ Φ -∗
    (plend_body intp xπ Φ -∗ modw M proph_wsat
      ([∗ plist] '(yπ, Ψ)' ∈ yπΨl, plend_body intp yπ Ψ))
      =[pborrow_wsat M intp]=∗ [∗ plist] '(yπ, Ψ)' ∈ yπΨl, plend_tok α yπ Ψ.
  Proof.
    iIntros "/=l →Ψl".
    iMod (lend_tok_extend (M:=modw M _) (plend_list yπΨl) with "l [→Ψl]");
      by rewrite big_sepL_of_plist.
  Qed.

  (** Retrieve from a prophetic lender *)
  Lemma plend_tok_retrieve `{!GenUpd M} {intp α X xπ Φ} :
    [†α] -∗ plend_tok (X:=X) α xπ Φ -∗ modw M (proph_wsat ∗ pborrow_wsat M intp)
      (plend_body intp xπ Φ).
  Proof. rewrite -modw_modw_sep. exact: lend_tok_retrieve. Qed.

  (** Open a prophetic borrower *)
  Lemma pbor_ctok_open {M intp α q X ξ x Φ} :
    q.[α] -∗ pbor_ctok (X:=X) α ξ x Φ =[pborrow_wsat M intp]=∗
      opbor_tok α q ξ Φ ∗ intp (Φ x).
  Proof.
    rewrite pbor_ctok_unseal opbor_tok_unseal. iIntros "α [†|[%[vo c]]]".
    { iDestruct (lft_tok_dead with "α †") as "[]". }
    iMod (bor_ctok_open with "α c") as "[o[%[pc Φ]]]". iModIntro.
    iDestruct (vo_pc_agree with "vo pc") as %<-. iFrame "Φ". iExists _.
    iFrame "o". iExists _. iFrame.
  Qed.
  Lemma pbor_tok_open `{!GenUpd M} {intp α q X ξ x Φ} :
    q.[α] -∗ pbor_tok (X:=X) α ξ x Φ -∗
      modw M (proph_wsat ∗ pborrow_wsat M intp)
      (opbor_tok α q ξ Φ ∗ intp (Φ x)).
  Proof.
    rewrite pbor_tok_unseal opbor_tok_unseal -modw_modw_sep.
    iIntros "α [†|[%[vo b]]]". { iDestruct (lft_tok_dead with "α †") as "[]". }
    iMod (bor_tok_open (M:=modw M _) with "α b") as "[o[%[pc Φ]]]". iModIntro.
    iDestruct (vo_pc_agree with "vo pc") as %<-. iFrame "Φ". iExists _.
    iFrame "o". iExists _. iFrame.
  Qed.

  (** Lemmas for [opbor_tok_merge_subdiv] *)
  Local Lemma opbor_preresolve `{!GenUpd M} {α Xl Yl r} {ηl : plist _ Yl}
    {qξΦfl :
      plist (λ X, Qp *' prvar X *' (X → PROP) *' (plist_synty Yl → X)) Xl} :
    r:∗[of_plist_prvar ηl] -∗
    ([∗ plist] '(q, ξ, Φ, _)' ∈ qξΦfl, opbor_tok α q ξ Φ) =[proph_wsat]=∗ ∃ γl,
      let γqξΦfl := plist_zip γl qξΦfl in
      r:∗[of_plist_prvar ηl] ∗
      ([∗ plist] '(_, ξ, _, f)' ∈ qξΦfl,
        ⟨π, π (Aprvar _ ξ) = f (app_plist_prvar π ηl)⟩) ∗
      ([∗ list] '(q, Px)' ∈
        of_plist (λ _ '(γ, q, ξ, Φ, _)', (q, pbprop_pbor γ ξ Φ)') γqξΦfl,
        obor_tok α q Px) ∗
      ∀ yl', ⟨π, app_plist_prvar π ηl = yl'⟩ -∗
        [∗ plist] '(γ, _, ξ, _, f)' ∈ γqξΦfl, proph_ctrl γ (f yl') ξ.
  Proof.
    rewrite/= opbor_tok_unseal. elim: Xl qξΦfl=>/=.
    { iIntros (_) "$ _ !>". iExists (). do 2 (iSplit; [done|]). by iIntros. }
    move=> X Xl IH [[q[ξ[Φ f]]] qξΦfl]. iIntros "ηl [[%[[%[vo pc]]o]] ol]".
    iMod (IH with "ηl ol") as (γl) "[ηl[$[ol →pcl]]]". iExists (γ, γl)'=>/=.
    iFrame "o ol".
    iMod (vo_pc_preresolve (λ π, f (app_plist_prvar π ηl)) with "ηl vo pc")
      as "[$[$ →pc]]"; [exact: proph_dep_plist|]. iModIntro.
    iIntros (yl') "#obs". iDestruct ("→pcl" with "obs") as "$". iApply "→pc".
    by iApply (proph_obs_impl with "obs")=> ? ->.
  Qed.
  Local Lemma pbor_list_intp_to_obs_intp {intp Yl γl' ηl} {yΨl : plist _ Yl} :
    ([∗ list] Qx ∈ pbor_list (plist_zip γl' (plist_zip ηl yΨl)), pbintp intp Qx)
      =[proph_wsat]=∗ ∃ yl', ⟨π, app_plist_prvar π ηl = yl'⟩ ∗
      [∗ plist] '(y', _, Ψ)' ∈ plist_zip yl' yΨl, intp (Ψ y').
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
  Lemma opbor_tok_merge_subdiv `{!GenUpd M} {intp α} Xl Yl
    (qξΦfl :
      plist (λ X, Qp *' prvar X *' (X → PROP) *' (plist_synty Yl → X)) Xl)
    (yΨl : plist (λ Y : TY, Y *' (Y → PROP)) Yl) :
    ([∗ plist] '(q, ξ, Φ, _)' ∈ qξΦfl, opbor_tok α q ξ Φ) -∗
    ([∗ plist] '(y, Ψ)' ∈ yΨl, intp (Ψ y)) -∗
    (∀ yl', [†α] -∗ ([∗ plist] '(y', _, Ψ)' ∈ plist_zip yl' yΨl, intp (Ψ y')) -∗
      modw M proph_wsat ([∗ plist] '(_, ξ, Φ, f)' ∈ qξΦfl, intp (Φ (f yl'))))
      =[proph_wsat ∗ pborrow_wsat M intp]=∗ ∃ ηl,
      ([∗ plist] '(q, _)' ∈ qξΦfl, q.[α]) ∗
      ([∗ plist] '(_, ξ, _, f)' ∈ qξΦfl,
        ⟨π, π (Aprvar _ ξ) = f (app_plist_prvar π ηl)⟩) ∗
      [∗ plist] '(η, y, Ψ)' ∈ plist_zip ηl yΨl, pbor_ctok α η y Ψ.
  Proof.
    iIntros "ol Ψl →Φl".
    iMod (proph_alloc_list (plist_map (λ _, fst') yΨl)) as (ηl) "ηl".
    iExists ηl.
    iMod (opbor_preresolve with "ηl ol") as (γl) "[ηl[$[ol →pcl]]]".
    iMod (vo_pbor_alloc_list with "ηl Ψl") as (γl') "[vol pborl]".
    iMod (obor_tok_merge_subdiv (M:=modw M _) with "ol pborl [→Φl →pcl]")
      as "[αl cl]".
    { iIntros "† pborl".
      iMod (pbor_list_intp_to_obs_intp with "pborl") as (yl') "[obs Ψl]".
      iMod ("→Φl" with "† Ψl") as "Φl". iModIntro.
      iDestruct ("→pcl" with "obs") as "pcl".
      rewrite of_plist_fmap big_sepL_of_plist
        -{1}(plist_zip_snd (xl:=γl) (yl:=qξΦfl)) big_sepPL_map.
      iDestruct (big_sepPL_sep_2 with "pcl Φl") as "pcΦl".
      iApply (big_sepPL_impl with "pcΦl").
      iIntros "!>" (?[?[?[?[??]]]]) "/=[??]". iExists _. iFrame. }
    iModIntro. rewrite of_plist_fmap !big_sepL_of_plist /=.
    rewrite -(big_sepPL_map _ (λ _ big, (big.1'.[α])%I)) plist_zip_snd.
    iFrame "αl". iDestruct (big_sepPL_sep_2 with "vol cl") as "vocl".
    rewrite -{2}(plist_zip_snd (xl:=γl') (yl:=plist_zip ηl yΨl)) big_sepPL_map.
    iApply (big_sepPL_impl with "vocl"). iIntros "!>" (?[?[?[??]]]) "/= [vo c]".
    rewrite pbor_ctok_unseal. iRight. iExists _. iFrame.
  Qed.
  (** Subdivide a prophetic borrower *)
  Lemma opbor_tok_subdiv `{!GenUpd M} {intp X α q ξ Φ} Yl
    (f : plist_synty Yl → X) (yΨl : plist (λ Y : TY, Y *' (Y → PROP)) Yl) :
    opbor_tok α q ξ Φ -∗ ([∗ plist] '(y, Ψ)' ∈ yΨl, intp (Ψ y)) -∗
    (∀ yl', [†α] -∗ ([∗ plist] '(y', _, Ψ)' ∈ plist_zip yl' yΨl, intp (Ψ y')) -∗
      modw M proph_wsat (intp (Φ (f yl'))))
      =[proph_wsat ∗ pborrow_wsat M intp]=∗ ∃ ηl,
      q.[α] ∗ ⟨π, π (Aprvar _ ξ) = f (app_plist_prvar π ηl)⟩ ∗
      [∗ plist] '(η, y, Ψ)' ∈ plist_zip ηl yΨl, pbor_ctok α η y Ψ.
  Proof.
    iIntros "o Ψl →Φ".
    iMod (opbor_tok_merge_subdiv [_] _ ((_,_,_,_)', ())'
      with "[$o //] Ψl [→Φ]") as (ηl) "big"=>/=.
    { iIntros (?). by rewrite bi.sep_emp. }
    iExists ηl. by iDestruct "big" as "/=[[$ _][[$ _]$]]".
  Qed.

  (** Subdivide a prophetic borrower without changing the prophecy *)
  Lemma opbor_tok_nsubdiv `{!GenUpd M} {intp X α q ξ Φ} Ψ x :
    opbor_tok (X:=X) α q ξ Φ -∗ intp (Ψ x) -∗
    (∀ y, [†α] -∗ intp (Ψ y) -∗ modw M proph_wsat (intp (Φ y)))
      =[pborrow_wsat M intp]=∗ q.[α] ∗ pbor_ctok α ξ x Ψ.
  Proof.
    rewrite opbor_tok_unseal pbor_ctok_unseal. iIntros "[%[[%[vo pc]] o]] Ψ →Φ".
    iMod (vo_pc_update with "vo pc") as "[vo pc]".
    iMod (obor_tok_subdiv (M:=modw M _) [pbprop_pbor _ _ Ψ]
      with "o [pc Ψ] [→Φ]") as "[$[c _]]"=>/=.
    { iSplit; [|done]. iExists _. iFrame. }
    { iIntros "† [[%[pc Ψ]]_]". iMod ("→Φ" with "† Ψ") as "Φ". iModIntro.
      iExists _. iFrame. }
    iModIntro. iRight. iExists _. iFrame.
  Qed.
  (** Simply close a prophetic borrower *)
  Lemma opbor_tok_close `{!GenUpd M} {intp X α q ξ Φ} x :
    opbor_tok (X:=X) α q ξ Φ -∗ intp (Φ x) =[pborrow_wsat M intp]=∗
      q.[α] ∗ pbor_ctok α ξ x Φ.
  Proof.
    iIntros "o Φ". iApply (opbor_tok_nsubdiv Φ with "o Φ"). by iIntros.
  Qed.

  (** Resolve the prophecy of a prophetic borrower *)
  Lemma opbor_tok_resolve `{!GenUpd M} {intp X α q ξ Φ} x :
    opbor_tok (X:=X) α q ξ Φ -∗ intp (Φ x) =[proph_wsat ∗ pborrow_wsat M intp]=∗
      q.[α] ∗ ⟨π, π ξ = x⟩ ∗ nbor_ctok α (Φ x).
  Proof.
    rewrite opbor_tok_unseal. iIntros "[%[[%[vo pc]] o]] Φ".
    iMod (vo_pc_resolve with "vo pc") as "[$ pc]".
    iMod (obor_tok_subdiv (M:=modw M _) [pbprop_just (Φ x)] with "o [Φ] [pc]")
      as "[$[$ _]]"=>/=; [by iFrame| |done].
    iIntros "† [Φ _] !>". iExists _. iFrame.
  Qed.
  Lemma pbor_ctok_resolve `{!GenUpd M} {intp X α q ξ x Φ} :
    q.[α] -∗ pbor_ctok (X:=X) α ξ x Φ =[proph_wsat ∗ pborrow_wsat M intp]=∗
      q.[α] ∗ ⟨π, π ξ = x⟩ ∗ nbor_ctok α (Φ x).
  Proof.
    iIntros "α c". iMod (pbor_ctok_open with "α c") as "[o Φ]".
    iApply (opbor_tok_resolve with "o Φ").
  Qed.
  Lemma pbor_tok_resolve `{!GenUpd M} {intp X α q ξ x Φ} :
    q.[α] -∗ pbor_tok (X:=X) α ξ x Φ -∗
      modw M (proph_wsat ∗ pborrow_wsat M intp)
      (q.[α] ∗ ⟨π, π ξ = x⟩ ∗ nbor_ctok α (Φ x)).
  Proof.
    iIntros "α b". iMod (pbor_tok_open with "α b") as "[o Φ]".
    by iMod (opbor_tok_resolve with "o Φ").
  Qed.

  (** Reborrow a nested prophetic borrower *)
  Lemma opbor_opbor_tok_reborrow `{!GenUpd M} {intp} {X Y : TY}
    {α q ξ Φ β r η Ψ} y (f : Y → X) :
    opbor_tok (X:=X) α q ξ Φ -∗ opbor_tok (X:=Y) β r η Ψ -∗ intp (Ψ y) -∗
    (∀ y', [†α] -∗ pbor_tok β η y' Ψ -∗ modw M proph_wsat (intp (Φ (f y'))))
      =[proph_wsat ∗ pborrow_wsat M intp]=∗ ∃ ζ : prvar _,
      q.[α] ∗ r.[β] ∗ ⟨π, π ξ = f (π ζ)⟩ ∗ pbor_ctok (α ⊓ β) ζ y Ψ.
  Proof.
    rewrite opbor_tok_unseal.
    iIntros "[%γ[[%[vo pc]] o]] [%γ'[[%[vo' pc']] o']] Ψ →Φ".
    iMod (vo_pc_update with "vo pc") as "[vo pc]".
    iMod (vo_pc_update with "vo' pc'") as "[vo' pc']".
    iMod (obor_tok_reborrow (M:=modw M _) α with "o' [pc' Ψ]")
      as "[β[c →b']]". { iExists _. iFrame. } rewrite lft_meet_comm.
    iMod vo_vo_alloc as (γx) "[vox vox']".
    iMod (obor_tok_subdiv (M:=modw M _) [pbprop_preborrow γ γ' γx ξ f]
      with "o [pc vo' vox'] [→Φ →b']") as "[α[c' _]]"=>/=.
    { iSplit; [|done]. iExists _. iFrame. }
    { iIntros "#† [[%y'[pc[vo' _]]]_]". iExists (f y'). iFrame "pc".
      iApply ("→Φ" with "†"). rewrite pbor_tok_unseal. iRight. iExists _.
      iFrame "vo'". by iApply "→b'". }
    iDestruct (bor_ctok_lft with "[] c'") as "c'"; [iApply lft_sincl_meet_l|].
    iDestruct (lft_tok_combine with "α β") as (?) "[αβ →αβ]".
    rewrite (lock meet). iDestruct "αβ" as "[αβ αβ']". unlock.
    iMod (bor_ctok_open with "αβ c") as "[o[%[pc' Ψ]]]".
    iMod (bor_ctok_open with "αβ' c'") as "[o'[%[pc[vo' vox']]]]".
    iDestruct (vo_vo_agree with "vox vox'") as %<-.
    iDestruct (vo_pc_agree with "vo' pc'") as %<-.
    iMod (proph_alloc y) as (ζ) "ζ". iExists ζ.
    iMod (vo_pc_preresolve (λ π, f (π ζ)) [Aprvar _ ζ] with "[$ζ //] vo pc")
      as "[[ζ _][$ →pc]]".
    { apply proph_dep_constr, proph_dep_one. }
    iMod (vo_pc_alloc with "ζ") as (γ'') "[vo'' pc'']".
    iMod (obor_tok_merge_subdiv (M:=modw M _) [(_,_)';(_,_)']
      [pbprop_pbor γ'' ζ Ψ] with "[$o $o' //] [pc'' Ψ] [→pc vo' pc' vox vox']")
      as "[[αβ[αβ' _]][c _]]"=>/=.
    { iSplit; [|done]. iExists _. iFrame. }
    { iIntros "_ [[%y'[pc'' Ψ]]_]". iMod (pc_resolve with "pc''") as "obs".
      iMod (vo_pc_update with "vo' pc'") as "[vo' pc']".
      iMod (vo_vo_update with "vox vox'") as "[vox _]". iApply modw_fold.
      iModIntro. iSplitL "pc' Ψ"; [iExists _; by iFrame|]. iSplit; [|done].
      iExists _. iFrame "vo' vox". iApply "→pc".
      by iApply (proph_obs_impl with "obs")=> ? ->. }
    iModIntro. iDestruct ("→αβ" with "[$αβ $αβ' //]") as "[$$]".
    rewrite pbor_ctok_unseal. iRight. iExists _. iFrame.
  Qed.
  Lemma opbor_pbor_ctok_reborrow `{!GenUpd M} {intp} {X Y : TY}
    {α q ξ Φ β r η y Ψ} (f : Y → X) :
    opbor_tok (X:=X) α q ξ Φ -∗ r.[β] -∗ pbor_ctok (X:=Y) β η y Ψ -∗
    (∀ y', [†α] -∗ pbor_tok β η y' Ψ -∗ modw M proph_wsat (intp (Φ (f y'))))
      =[proph_wsat ∗ pborrow_wsat M intp]=∗ ∃ ζ : prvar _,
      q.[α] ∗ r.[β] ∗ ⟨π, π ξ = f (π ζ)⟩ ∗ pbor_ctok (α ⊓ β) ζ y Ψ.
  Proof.
    iIntros "Φ β c →Φ". iMod (pbor_ctok_open with "β c") as "[o Ψ]".
    iApply (opbor_opbor_tok_reborrow with "Φ o Ψ →Φ").
  Qed.
  Lemma opbor_pbor_tok_reborrow `{!GenUpd M} {intp} {X Y : TY}
    {α q ξ Φ β r η y Ψ} (f : Y → X) :
    opbor_tok (X:=X) α q ξ Φ -∗ r.[β] -∗ pbor_tok (X:=Y) β η y Ψ -∗
    (∀ y', [†α] -∗ pbor_tok β η y' Ψ -∗ modw M proph_wsat (intp (Φ (f y')))) -∗
      modw M (proph_wsat ∗ pborrow_wsat M intp) (∃ ζ : prvar _,
      q.[α] ∗ r.[β] ∗ ⟨π, π ξ = f (π ζ)⟩ ∗ pbor_ctok (α ⊓ β) ζ y Ψ).
  Proof.
    iIntros "Φ β c →Φ". iMod (pbor_tok_open with "β c") as "[o Ψ]".
    iMod (opbor_opbor_tok_reborrow with "Φ o Ψ →Φ") as "$". by iIntros.
  Qed.
End pborrow.

(** Allocate [proph_wsat] and [pborrow_wsat] *)
Lemma proph_pborrow_wsat_alloc `{!pborrowGpreS TY PROP Σ} :
  ⊢ |==> ∃ _ : pborrowGS TY PROP Σ,
    proph_wsat ∗ ∀ M intp, pborrow_wsat M intp.
Proof.
  iMod proph_wsat_alloc as (?) "W". iMod borrow_wsat_alloc as (?) "W'".
  iModIntro. iExists (PborrowGS _ _ _ _ _ _). iFrame "W". by iIntros.
Qed.
