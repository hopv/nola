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
    {X : TY} (xπ : clair TY X) (Φ : X → PROP)
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
  Implicit Type (M : iProp Σ → iProp Σ) (intp : PROP -d> iProp Σ) (X Y : TY)
    (Xl Yl : list TY) (P : PROP) (Px : pbprop TY PROP).

  (** ** Tokens *)

  (** Prophetic borrower token *)
  Local Definition pbor_ctok_def {X} α (x : X) (ξ : prvar X) (Φ : X → PROP)
    : iProp Σ :=
    [†α] ∨ ∃ γ, val_obs γ x ∗ bor_ctok α (pbprop_pbor γ ξ Φ).
  Local Lemma pbor_ctok_aux : seal (@pbor_ctok_def). Proof. by eexists. Qed.
  Definition pbor_ctok {X} := pbor_ctok_aux.(unseal) X.
  Local Lemma pbor_ctok_unseal : @pbor_ctok = @pbor_ctok_def.
  Proof. exact: seal_eq. Qed.
  Local Definition pbor_tok_def {X} α (x : X) (ξ : prvar X) (Φ : X → PROP)
    : iProp Σ :=
    [†α] ∨ ∃ γ, val_obs γ x ∗ bor_tok α (pbprop_pbor γ ξ Φ).
  Local Lemma pbor_tok_aux : seal (@pbor_tok_def). Proof. by eexists. Qed.
  Definition pbor_tok {X} := pbor_tok_aux.(unseal) X.
  Local Lemma pbor_tok_unseal : @pbor_tok = @pbor_tok_def.
  Proof. exact: seal_eq. Qed.

  (** Open prophetic borrower token *)
  Local Definition pobor_tok_def {X} α q (ξ : prvar X) (Φ : X → PROP)
    : iProp Σ :=
    ∃ γ, (∃ x, val_obs γ x ∗ proph_ctrl γ x ξ) ∗
      obor_tok α q (pbprop_pbor γ ξ Φ).
  Local Lemma pobor_tok_aux : seal (@pobor_tok_def). Proof. by eexists. Qed.
  Definition pobor_tok {X} := pobor_tok_aux.(unseal) X.
  Local Lemma pobor_tok_unseal : @pobor_tok = @pobor_tok_def.
  Proof. exact: seal_eq. Qed.

  (** Prophetic lender token *)
  Definition plend_tok {X} α (xπ : clair TY X) (Φ : X → PROP) : iProp Σ :=
    lend_tok α (pbprop_plend xπ Φ).

  (** Non-prophetic token *)
  Definition nbor_ctok α P : iProp Σ := bor_ctok α (pbprop_just P).
  Definition nbor_tok α P : iProp Σ := bor_tok α (pbprop_just P).
  Definition nobor_tok α q P : iProp Σ := obor_tok α q (pbprop_just P).
  Definition nlend_tok α P : iProp Σ := lend_tok α (pbprop_just P).

  (** Prophetic borrower and lender tokens are timeless *)
  #[export] Instance pbor_ctok_timeless {α X x ξ Φ} :
    Timeless (pbor_ctok (X:=X) α x ξ Φ).
  Proof. rewrite pbor_ctok_unseal. exact _. Qed.
  #[export] Instance pbor_tok_timeless {α X x ξ Φ} :
    Timeless (pbor_tok (X:=X) α x ξ Φ).
  Proof. rewrite pbor_tok_unseal. exact _. Qed.
  #[export] Instance pobor_tok_timeless {α q X ξ Φ} :
    Timeless (pobor_tok (X:=X) α q ξ Φ).
  Proof. rewrite pobor_tok_unseal. exact _. Qed.
  Fact plend_tok_timeless {α X xπ Φ} :
    Timeless (plend_tok (X:=X) α xπ Φ).
  Proof. exact _. Qed.

  (** Turn [pbor_ctok] to [pbor_tok] *)
  Lemma pbor_ctok_tok {α X x ξ Φ} : pbor_ctok (X:=X) α x ξ Φ ⊢ pbor_tok α x ξ Φ.
  Proof.
    rewrite pbor_ctok_unseal pbor_tok_unseal /pbor_ctok_def.
    by setoid_rewrite bor_ctok_tok.
  Qed.

  (** Fake a prophetic borrower token from the dead lifetime token *)
  Lemma pbor_ctok_fake {α X x ξ Φ} : [†α] ⊢ pbor_ctok (X:=X) α x ξ Φ.
  Proof. rewrite pbor_ctok_unseal. iIntros. by iLeft. Qed.
  Lemma pbor_tok_fake {α X x ξ Φ} : [†α] ⊢ pbor_tok (X:=X) α x ξ Φ.
  Proof. rewrite pbor_tok_unseal. iIntros. by iLeft. Qed.
  (** Modify the lifetime of borrower and lender tokens *)
  Lemma pbor_ctok_lft {α β X x ξ Φ} :
    β ⊑□ α -∗ pbor_ctok (X:=X) α x ξ Φ -∗ pbor_ctok β x ξ Φ.
  Proof.
    rewrite pbor_ctok_unseal. iIntros "#? [?|[%[vo ?]]]".
    { iLeft. by iApply lft_sincl_dead. }
    iRight. iExists _. iFrame "vo". by iApply bor_ctok_lft.
  Qed.
  Lemma pbor_tok_lft {α β X x ξ Φ} :
    β ⊑□ α -∗ pbor_tok (X:=X) α x ξ Φ -∗ pbor_tok β x ξ Φ.
  Proof.
    rewrite pbor_tok_unseal. iIntros "#? [?|[%[vo ?]]]".
    { iLeft. by iApply lft_sincl_dead. }
    iRight. iExists _. iFrame "vo". by iApply bor_tok_lft.
  Qed.
  Lemma pobor_tok_lft {α β q r X ξ Φ} :
    β ⊑□ α -∗ (q.[α] -∗ r.[β]) -∗ pobor_tok (X:=X) α q ξ Φ -∗ pobor_tok β r ξ Φ.
  Proof.
    rewrite pobor_tok_unseal. iIntros "⊑ →β [%[vopc o]]". iExists _.
    iFrame "vopc". iApply (obor_tok_lft with "⊑ →β o").
  Qed.
  Lemma plend_tok_lft {α β X xπ Φ} :
    α ⊑□ β -∗ plend_tok (X:=X) α xπ Φ -∗ plend_tok β xπ Φ.
  Proof. exact lend_tok_lft. Qed.

  (** Take out a prophecy variable from an open prophetic borrower *)
  Lemma pobor_proph_tok {α q X ξ Φ} :
    pobor_tok (X:=X) α q ξ Φ -∗ 1:[ξ] ∗ (1:[ξ] -∗ pobor_tok α q ξ Φ).
  Proof.
    rewrite pobor_tok_unseal. iIntros "[%[[%[vo pc]] o]]".
    iDestruct (vo_pc_vo_proph with "vo pc") as "[vo[vo' $]]". iIntros "ξ".
    iExists _. iFrame "o". iExists _. iFrame "vo".
    iApply (vo_proph_pc with "vo' ξ").
  Qed.

  (** ** World satisfaction *)

  (** Body of a prophetic lender *)
  Definition plend_body intp {X}
    (xπ : clair TY X) (Φ : X → PROP) : iProp Σ :=
    ∃ x', ⟨π, xπ π = x'⟩ ∗ intp (Φ x').
  Definition plend_body_var intp {X} (ξ : prvar X) (Φ : X → PROP) : iProp Σ :=
    plend_body intp (λ π, π ξ) Φ.

  (** Interpretation of [pbprop] *)
  Definition pbintp intp : _ -d> iProp Σ := λ Px, match Px with
    | pbprop_just P => intp P
    | pbprop_pbor γ ξ Φ => ∃ x, proph_ctrl γ x ξ ∗ intp (Φ x)
    | pbprop_plend xπ Φ => plend_body intp xπ Φ
    | pbprop_preborrow γ γ' γx ξ f =>
        ∃ y, proph_ctrl γ (f y) ξ ∗ val_obs γ' y ∗ val_obs γx y
    end%I.

  (** World satisfaction *)
  Definition pborrow_wsat M intp : iProp Σ := borrow_wsat M (pbintp intp).

  (** [pbintp] is non-expansive *)
  #[export] Instance pbintp_ne : NonExpansive pbintp.
  Proof. move=> ????[]/=; solve_proper. Qed.
  (** [pbintp] is proper *)
  #[export] Instance pbintp_proper : Proper ((≡) ==> (≡)) pbintp.
  Proof. apply ne_proper, _. Qed.
  (** [pborrow_wsat] is non-expansive *)
  #[export] Instance pborrow_wsat_ne `{!NonExpansive M} :
    NonExpansive (pborrow_wsat M).
  Proof. solve_proper. Qed.
  (** [pborrow_wsat] is proper *)
  #[export] Instance pborrow_wsat_proper `{!NonExpansive M} :
    Proper ((≡) ==> (≡)) (pborrow_wsat M).
  Proof. solve_proper. Qed.
  Lemma pborrow_wsat_ne_mod {n M M' intp} :
    (∀ P : iProp Σ, M P ≡{n}≡ M' P) →
    pborrow_wsat M intp ≡{n}≡ pborrow_wsat M' intp.
  Proof. move=> ?. by apply borrow_wsat_ne_mod. Qed.
  Lemma pborrow_wsat_proper_mod {M M' intp} :
    (∀ P : iProp Σ, M P ≡ M' P) → pborrow_wsat M intp ≡ pborrow_wsat M' intp.
  Proof.
    move=> ?. apply equiv_dist=> ?. apply pborrow_wsat_ne_mod=> ?.
    by apply equiv_dist.
  Qed.

  (** ** For non-prophetic borrowing *)

  (** Create new borrowers and lenders *)
  Lemma nbor_nlend_tok_new_list `{!GenUpd M} {intp} α Pl Ql :
    ([∗ list] P ∈ Pl, intp P) -∗
    ([†α] -∗ ([∗ list] P ∈ Pl, intp P) -∗ M
      ([∗ list] Q ∈ Ql, intp Q)%I) =[pborrow_wsat M intp]=∗
      ([∗ list] P ∈ Pl, nbor_ctok α P) ∗ [∗ list] Q ∈ Ql, nlend_tok α Q.
  Proof.
    iIntros "Pl →Ql".
    iMod (bor_lend_tok_new_list α (pbprop_just <$> Pl) (pbprop_just <$> Ql)
      with "[Pl] [→Ql]"); by rewrite !big_sepL_fmap.
  Qed.
  Lemma nbor_nlend_tok_new `{!GenUpd M} {intp} α P :
    intp P =[pborrow_wsat M intp]=∗ nbor_ctok α P ∗ nlend_tok α P.
  Proof.
    iIntros "P". iMod (nbor_nlend_tok_new_list α [P] [P] with "[P] []")
      as "[[$_][$_]]"; by [iFrame|iIntros|].
  Qed.

  (** Split a lender *)
  Lemma nlend_tok_split `{!GenUpd M} {intp α P} Ql :
    nlend_tok α P -∗ (intp P -∗ M ([∗ list] Q ∈ Ql, intp Q))
      =[pborrow_wsat M intp]=∗ [∗ list] Q ∈ Ql, nlend_tok α Q.
  Proof.
    iIntros "l →Ql".
    iMod (lend_tok_split (pbprop_just <$> Ql) with "l [→Ql]");
      by rewrite !big_sepL_fmap.
  Qed.

  (** Retrieve from a lender *)
  Lemma nlend_tok_retrieve `{!GenUpd M} {intp α P} :
    [†α] -∗ nlend_tok α P -∗ modw M (pborrow_wsat M intp) (intp P).
  Proof. exact lend_tok_retrieve. Qed.

  (** Open a borrower *)
  Lemma nbor_ctok_open {M intp α q P} :
    q.[α] -∗ nbor_ctok α P =[pborrow_wsat M intp]=∗ nobor_tok α q P ∗ intp P.
  Proof. exact bor_ctok_open. Qed.
  Lemma nbor_tok_open `{!GenUpd M} {intp α q P} :
    q.[α] -∗ nbor_tok α P -∗ modw M (pborrow_wsat M intp)
      (nobor_tok α q P ∗ intp P).
  Proof. exact bor_tok_open. Qed.

  (** Merge and subdivide open borrowers *)
  Lemma nobor_tok_merge_subdiv `{!GenUpd M} {intp} αqPl Ql β :
    ([∗ list] '(α, q, P)' ∈ αqPl, β ⊑□ α ∗ nobor_tok α q P) -∗
    ([∗ list] Q ∈ Ql, intp Q) -∗
    ([†β] -∗ ([∗ list] Q ∈ Ql, intp Q) -∗ M
      ([∗ list] '(_, _, P)' ∈ αqPl, intp P)%I) =[pborrow_wsat M intp]=∗
      ([∗ list] '(α, q, _)' ∈ αqPl, q.[α]) ∗ [∗ list] Q ∈ Ql, nbor_ctok β Q.
  Proof.
    iIntros "ol Ql →Pl".
    iMod (obor_tok_merge_subdiv
      ((λ '(α, q, P)', (α, q, pbprop_just P)') <$> αqPl) (pbprop_just <$> Ql)
      with "[ol] [Ql] [→Pl]"); by rewrite !big_sepL_fmap /=.
  Qed.
  Lemma nobor_tok_subdiv `{!GenUpd M} {intp α q P} Ql β :
    β ⊑□ α -∗ nobor_tok α q P -∗ ([∗ list] Q ∈ Ql, intp Q) -∗
    ([†β] -∗ ([∗ list] Q ∈ Ql, intp Q) -∗ M (intp P))
      =[pborrow_wsat M intp]=∗ q.[α] ∗ [∗ list] Q ∈ Ql, nbor_ctok β Q.
  Proof.
    iIntros "⊑ o Ql →P".
    iMod (nobor_tok_merge_subdiv [(_,_,_)'] with "[⊑ o] Ql [→P]")
      as "[[$ _]$]"=>/=; by [iFrame|rewrite bi.sep_emp|].
  Qed.
  Lemma nobor_tok_close `{!GenUpd M} {intp α q P} :
    nobor_tok α q P -∗ intp P =[pborrow_wsat M intp]=∗ q.[α] ∗ nbor_ctok α P.
  Proof.
    iIntros "o P".
    iMod (nobor_tok_subdiv [P] with "[] o [P] []") as "[$[$_]]"=>/=;
      by [iApply lft_sincl_refl|iFrame|iIntros "_[$_]"|].
  Qed.

  (** Reborrow *)
  Lemma nobor_tok_reborrow `{!GenUpd M} {intp α q P} β :
    nobor_tok α q P -∗ intp P =[pborrow_wsat M intp]=∗
      q.[α] ∗ nbor_ctok (α ⊓ β) P ∗ ([†β] -∗ nbor_tok α P).
  Proof. exact: obor_tok_reborrow. Qed.
  Lemma nbor_ctok_reborrow `{!GenUpd M} {intp α q P} β :
    q.[α] -∗ nbor_ctok α P =[pborrow_wsat M intp]=∗
      q.[α] ∗ nbor_ctok (α ⊓ β) P ∗ ([†β] -∗ nbor_tok α P).
  Proof. exact: bor_ctok_reborrow. Qed.
  Lemma nbor_tok_reborrow `{!GenUpd M} {intp α q P} β :
    q.[α] -∗ nbor_tok α P -∗ modw M (pborrow_wsat M intp)
      (q.[α] ∗ nbor_ctok (α ⊓ β) P ∗ ([†β] -∗ nbor_tok α P)).
  Proof. exact: bor_tok_reborrow. Qed.

  (** ** On prophetic borrowing *)

  (** Utility *)
  Local Definition pbor_list {Xl}
    (γξxΦl : plist (λ X, _ *' _ *' X *' (X → PROP)) Xl) :=
    of_plist (λ _ '(γ, ξ, _, Φ)', pbprop_pbor γ ξ Φ) γξxΦl.
  Local Definition plend_list {Xl}
    (xπΦl : plist (λ X, _ *' (X → PROP)) Xl) :=
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
    ([∗ list] Px ∈ pbor_list (plist_zip γl ξxΦl), pbintp intp Px) ==∗
      [∗ plist] '(ξ, x, Φ)' ∈ ξxΦl, plend_body_var intp ξ Φ.
  Proof.
    elim: Xl γl ξxΦl=>/=; [by iIntros|]=> X Xl IH [γ γl] [[ξ[x Φ]] ξxΦl].
    iIntros "[[%[pc Φ]] pborl]". iMod (IH with "pborl") as "$".
    iMod (pc_resolve with "pc") as "?". iModIntro. iExists _. iFrame.
  Qed.
  (** Create new prophetic borrowers and lenders *)
  Lemma pbor_plend_tok_new_list `{!GenUpd M} {intp} α Xl (xΦl : plist _ Xl) :
    ⊢ |==> ∃ ξl, ∀ Yl (yπΨl : plist (λ Y, _ *' (Y → PROP)) Yl),
      let ξxΦl := plist_zip ξl xΦl in
      ([∗ plist] '(x, Φ)' ∈ xΦl, intp (Φ x)) -∗
      ([†α] -∗ ([∗ plist] '(ξ, x, Φ)' ∈ ξxΦl, plend_body_var intp ξ Φ) -∗
        M ([∗ plist] '(yπ, Ψ)' ∈ yπΨl, plend_body intp yπ Ψ))
        =[pborrow_wsat M intp]=∗
        ([∗ plist] '(ξ, x, Φ)' ∈ ξxΦl, pbor_ctok α x ξ Φ) ∗
        ([∗ plist] '(yπ, Ψ)' ∈ yπΨl, plend_tok α yπ Ψ).
  Proof.
    iMod (proph_alloc_list (plist_map (λ _, fst') xΦl)) as (ξl) "ξl".
    iModIntro. iExists ξl. iIntros (??) "Φl →Ψl".
    set ξxΦl := plist_zip ξl xΦl.
    iMod (vo_pbor_alloc_list with "ξl Φl") as (γl) "[vol pborl]".
    iMod (bor_lend_tok_new_list α _ (plend_list yπΨl) with "pborl [→Ψl]")
      as "[bl ll]".
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
    intp (Φ x) =[pborrow_wsat M intp]=∗ ∃ ξ,
      pbor_ctok (X:=X) α x ξ Φ ∗ plend_tok α (λ π, π ξ) Φ.
  Proof.
    iIntros "Φ".
    iMod (pbor_plend_tok_new_list α [X] ((x, Φ)',())') as ([ξ[]]) "big".
    iExists ξ.
    iMod ("big" $! [X] ((_,_)',())' with "[Φ] []") as "[[$ _][$ _]]"=>/=;
      by [iFrame|iIntros|].
  Qed.

  (** Split a prophetic lender *)
  Lemma plend_tok_split `{!GenUpd M} {intp α X xπ Φ} Yl
    (yπΨl : plist (λ Y, _ *' (Y → PROP)) Yl) :
    plend_tok (X:=X) α xπ Φ -∗
    (plend_body intp xπ Φ -∗ M
      ([∗ plist] '(yπ, Ψ)' ∈ yπΨl, plend_body intp yπ Ψ))
      =[pborrow_wsat M intp]=∗ [∗ plist] '(yπ, Ψ)' ∈ yπΨl, plend_tok α yπ Ψ.
  Proof.
    iIntros "/=l →Ψl".
    iMod (lend_tok_split (plend_list yπΨl) with "l [→Ψl]");
      by rewrite big_sepL_of_plist.
  Qed.

  (** Retrieve from a prophetic lender *)
  Lemma plend_tok_retrieve `{!GenUpd M} {intp α X xπ Φ} :
    [†α] -∗ plend_tok (X:=X) α xπ Φ -∗ modw M (pborrow_wsat M intp)
      (plend_body intp xπ Φ).
  Proof. exact: lend_tok_retrieve. Qed.

  (** Open a prophetic borrower *)
  Lemma pbor_ctok_open {M intp α q X x ξ Φ} :
    q.[α] -∗ pbor_ctok (X:=X) α x ξ Φ =[pborrow_wsat M intp]=∗
      pobor_tok α q ξ Φ ∗ intp (Φ x).
  Proof.
    rewrite pbor_ctok_unseal pobor_tok_unseal. iIntros "α [†|[%[vo c]]]".
    { iDestruct (lft_alive_dead with "α †") as "[]". }
    iMod (bor_ctok_open with "α c") as "[o[%[pc Φ]]]". iModIntro.
    iDestruct (vo_pc_agree with "vo pc") as %<-. iFrame "Φ". iExists _.
    iFrame "o". iExists _. iFrame.
  Qed.
  Lemma pbor_tok_open `{!GenUpd M} {intp α q X x ξ Φ} :
    q.[α] -∗ pbor_tok (X:=X) α x ξ Φ -∗ modw M (pborrow_wsat M intp)
      (pobor_tok α q ξ Φ ∗ intp (Φ x)).
  Proof.
    rewrite pbor_tok_unseal pobor_tok_unseal. iIntros "α [†|[%[vo b]]]".
    { iDestruct (lft_alive_dead with "α †") as "[]". }
    iMod (bor_tok_open with "α b") as "[o[%[pc Φ]]]". iModIntro.
    iDestruct (vo_pc_agree with "vo pc") as %<-. iFrame "Φ". iExists _.
    iFrame "o". iExists _. iFrame.
  Qed.

  (** Lemmas for [pobor_tok_merge_subdiv] *)
  Local Lemma pobor_preresolve `{!GenUpd M} {β Xl Yl r} {ηl : plist _ Yl}
    {αqξΦfl : plist (λ X, _ *' _ *' _ *' _ *' (_ → X)) Xl} :
    r:∗[of_plist_prvar ηl] -∗
    ([∗ plist] '(α, q, ξ, Φ, _)' ∈ αqξΦfl, β ⊑□ α ∗ pobor_tok α q ξ Φ) ==∗ ∃ γl,
      let γαqξΦfl := plist_zip γl αqξΦfl in
      r:∗[of_plist_prvar ηl] ∗
      ([∗ plist] '(_, _, ξ, _, f)' ∈ αqξΦfl,
        ⟨π, π (Aprvar _ ξ) = f (app_plist_prvar π ηl)⟩) ∗
      ([∗ list] '(α, q, Px)' ∈
        of_plist (λ _ '(γ, α, q, ξ, Φ, _)', (α, q, pbprop_pbor γ ξ Φ)') γαqξΦfl,
        β ⊑□ α ∗ obor_tok α q Px) ∗
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
  Local Lemma pbor_list_intp_to_obs_intp {intp Yl γl' ηl} {yΨl : plist _ Yl} :
    ([∗ list] Qx ∈ pbor_list (plist_zip γl' (plist_zip ηl yΨl)), pbintp intp Qx)
      ==∗ ∃ yl', ⟨π, app_plist_prvar π ηl = yl'⟩ ∗
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
  Lemma pobor_tok_merge_subdiv `{!GenUpd M} {intp} Xl Yl
    (αqξΦfl : plist (λ X, _ *' _ *' _ *' _ *' (_ → X)) Xl) (yΨl : plist _ Yl) Rl
    β :
    ([∗ plist] '(α, q, ξ, Φ, _)' ∈ αqξΦfl, β ⊑□ α ∗ pobor_tok α q ξ Φ) -∗
    ([∗ plist] '(y, Ψ)' ∈ yΨl, intp (Ψ y)) -∗ ([∗ list] R ∈ Rl, intp R) -∗
    (∀ yl', [†β] -∗ ([∗ plist] '(y', _, Ψ)' ∈ plist_zip yl' yΨl, intp (Ψ y')) -∗
      ([∗ list] R ∈ Rl, intp R) -∗ M
        ([∗ plist] '(_, _, _, Φ, f)' ∈ αqξΦfl, intp (Φ (f yl'))))
      =[pborrow_wsat M intp]=∗ ∃ ηl,
      ([∗ plist] '(α, q, _)' ∈ αqξΦfl, q.[α]) ∗
      ([∗ plist] '(_, _, ξ, _, f)' ∈ αqξΦfl,
        ⟨π, π (Aprvar _ ξ) = f (app_plist_prvar π ηl)⟩) ∗
      ([∗ plist] '(η, y, Ψ)' ∈ plist_zip ηl yΨl, pbor_ctok β y η Ψ) ∗
      [∗ list] R ∈ Rl, nbor_ctok β R.
  Proof.
    iIntros "ol Ψl Rl →Φl".
    iMod (proph_alloc_list (plist_map (λ _, fst') yΨl)) as (ηl) "ηl".
    iExists ηl.
    iMod (pobor_preresolve with "ηl ol") as (γl) "[ηl[$[ol →pcl]]]".
    iMod (vo_pbor_alloc_list with "ηl Ψl") as (γl') "[vol pborl]".
    iMod (obor_tok_merge_subdiv _ (_ ++ (pbprop_just <$> Rl))
      with "ol [pborl Rl] [→Φl →pcl]") as "[αl cl]";
      rewrite big_sepL_app !big_sepL_fmap. { by iFrame. }
    { iIntros "† [pborl Rl]".
      iMod (pbor_list_intp_to_obs_intp with "pborl") as (yl') "[obs Ψl]".
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
    rewrite pbor_ctok_unseal. iRight. iExists _. iFrame.
  Qed.
  (** Subdivide a prophetic borrower *)
  Lemma pobor_tok_subdiv `{!GenUpd M} {intp X α q ξ Φ} Yl (f : _ → X)
    (yΨl : plist _ Yl) Rl β :
    β ⊑□ α -∗ pobor_tok α q ξ Φ -∗ ([∗ plist] '(y, Ψ)' ∈ yΨl, intp (Ψ y)) -∗
    ([∗ list] R ∈ Rl, intp R) -∗
    (∀ yl', [†β] -∗ ([∗ plist] '(y', _, Ψ)' ∈ plist_zip yl' yΨl, intp (Ψ y')) -∗
      ([∗ list] R ∈ Rl, intp R) -∗ M (intp (Φ (f yl'))))
      =[pborrow_wsat M intp]=∗ ∃ ηl,
      q.[α] ∗ ⟨π, π (Aprvar _ ξ) = f (app_plist_prvar π ηl)⟩ ∗
      ([∗ plist] '(η, y, Ψ)' ∈ plist_zip ηl yΨl, pbor_ctok β y η Ψ) ∗
      [∗ list] R ∈ Rl, nbor_ctok β R.
  Proof.
    iIntros "⊑ o Ψl Rl →Φ".
    iMod (pobor_tok_merge_subdiv [_] _ ((_,_,_,_,_)',())'
      with "[$⊑ $o //] Ψl Rl [→Φ]") as (ηl) "big"=>/=.
    { iIntros (?). by rewrite bi.sep_emp. }
    iExists ηl. by iDestruct "big" as "/=[[$ _][[$ _]$]]".
  Qed.

  (** Resolve the prophecy of a prophetic borrower *)
  Lemma pobor_tok_resolve `{!GenUpd M} {intp X α q ξ Φ} x :
    pobor_tok (X:=X) α q ξ Φ -∗ intp (Φ x) =[pborrow_wsat M intp]=∗
      q.[α] ∗ ⟨π, π ξ = x⟩ ∗ nbor_ctok α (Φ x).
  Proof.
    iIntros "o Φ".
    iMod (pobor_tok_subdiv [] (λ _, x) () [Φ x] with "[] o [//] [Φ] []")
      as (?) "[$[$[_[$ _]]]]"=>/=;
      by [iApply lft_sincl_refl|iFrame|iIntros "% _ _ [$ _]"|].
  Qed.
  Lemma pbor_ctok_resolve `{!GenUpd M} {intp X α q x ξ Φ} :
    q.[α] -∗ pbor_ctok (X:=X) α x ξ Φ =[pborrow_wsat M intp]=∗
      q.[α] ∗ ⟨π, π ξ = x⟩ ∗ nbor_ctok α (Φ x).
  Proof.
    iIntros "α c". iMod (pbor_ctok_open with "α c") as "[o Φ]".
    iApply (pobor_tok_resolve with "o Φ").
  Qed.
  Lemma pbor_tok_resolve `{!GenUpd M} {intp X α q x ξ Φ} :
    q.[α] -∗ pbor_tok (X:=X) α x ξ Φ -∗ modw M (pborrow_wsat M intp)
      (q.[α] ∗ ⟨π, π ξ = x⟩ ∗ nbor_ctok α (Φ x)).
  Proof.
    iIntros "α b". iMod (pbor_tok_open with "α b") as "[o Φ]".
    by iMod (pobor_tok_resolve with "o Φ").
  Qed.

  (** Subdivide a prophetic borrower without changing the prophecy *)
  Lemma pobor_tok_nsubdiv `{!GenUpd M} {intp X α q ξ Φ} Ψ x β :
    β ⊑□ α -∗ pobor_tok (X:=X) α q ξ Φ -∗ intp (Ψ x) -∗
    (∀ x', [†β] -∗ intp (Ψ x') -∗ M (intp (Φ x'))) =[pborrow_wsat M intp]=∗
      q.[α] ∗ pbor_ctok β x ξ Ψ.
  Proof.
    rewrite pobor_tok_unseal pbor_ctok_unseal.
    iIntros "⊑ [%[[%[vo pc]] o]] Ψ →Φ".
    iMod (vo_pc_update with "vo pc") as "[vo pc]".
    iMod (obor_tok_subdiv [pbprop_pbor _ _ Ψ] with "⊑ o [pc Ψ] [→Φ]")
      as "[$[c _]]"=>/=.
    { iSplit; [|done]. iExists _. iFrame. }
    { iIntros "† [[%[pc Ψ]]_]". iMod ("→Φ" with "† Ψ") as "Φ". iModIntro.
      iExists _. iFrame. }
    iModIntro. iRight. iExists _. iFrame.
  Qed.
  (** Simply close a prophetic borrower *)
  Lemma pobor_tok_close `{!GenUpd M} {intp X α q ξ Φ} x :
    pobor_tok (X:=X) α q ξ Φ -∗ intp (Φ x) =[pborrow_wsat M intp]=∗
      q.[α] ∗ pbor_ctok α x ξ Φ.
  Proof.
    iIntros "o Φ". iApply (pobor_tok_nsubdiv Φ with "[] o Φ"); [|by iIntros].
    iApply lft_sincl_refl.
  Qed.

  (** Reborrow a nested prophetic borrower *)
  Lemma pobor_pobor_tok_reborrow `{!GenUpd M} {intp X Y α q ξ Φ β r η Ψ} y f :
    pobor_tok (X:=X) α q ξ Φ -∗ pobor_tok (X:=Y) β r η Ψ -∗ intp (Ψ y) -∗
    (∀ y', [†α] -∗ pbor_tok β y' η Ψ -∗ M (intp (Φ (f y'))))
      =[pborrow_wsat M intp]=∗ ∃ η' : prvar _,
      q.[α] ∗ r.[β] ∗ ⟨π, π ξ = f (π η')⟩ ∗ pbor_ctok (α ⊓ β) y η' Ψ.
  Proof.
    rewrite pobor_tok_unseal.
    iIntros "[%γ[[%[vo pc]] o]] [%γ'[[%[vo' pc']] o']] Ψ →Φ".
    iMod (vo_pc_update with "vo pc") as "[vo pc]".
    iMod (vo_pc_update with "vo' pc'") as "[vo' pc']".
    iMod (obor_tok_reborrow α with "o' [pc' Ψ]") as "[β[c →b']]".
    { iExists _. iFrame. }
    rewrite lft_meet_comm. iMod vo_vo_alloc as (γx) "[vox vox']".
    iMod (obor_tok_subdiv [pbprop_preborrow γ γ' γx ξ f]
      with "[] o [pc vo' vox'] [→Φ →b']") as "[[α α'][c' _]]"=>/=.
    { iApply lft_sincl_refl. } { iSplit; [|done]. iExists _. iFrame. }
    { iIntros "#† [[%y'[pc[vo' _]]]_]". iExists (f y'). iFrame "pc".
      iApply ("→Φ" with "†"). rewrite pbor_tok_unseal. iRight. iExists _.
      iFrame "vo'". by iApply "→b'". }
    iDestruct (lft_alive_combine with "α' β") as (?) "[αβ →α'β]".
    iMod (bor_ctok_open with "αβ c") as "[o[%[pc' Ψ]]]".
    iMod (bor_ctok_open with "α c'") as "[o'[%[pc[vo' vox']]]]".
    iDestruct (vo_vo_agree with "vox vox'") as %<-.
    iDestruct (vo_pc_agree with "vo' pc'") as %<-.
    iMod (proph_alloc y) as (η') "η'". iExists η'.
    iMod (vo_pc_preresolve (λ π, f (π η')) [Aprvar _ η'] with "[$η' //] vo pc")
      as "[[η' _][$ →pc]]".
    { apply proph_dep_constr, proph_dep_one. }
    iMod (vo_pc_alloc with "η'") as (γ'') "[vo'' pc'']".
    iMod (obor_tok_merge_subdiv [(_,_,_)';(_,_,_)'] [pbprop_pbor γ'' η' Ψ]
      with "[$o $o'] [pc'' Ψ] [→pc vo' pc' vox vox']") as "[[αβ[$_]][c _]]"=>/=.
    { iSplit; [by iApply lft_sincl_refl|]. iSplit; [|done].
      iApply lft_sincl_meet_l. }
    { iSplit; [|done]. iExists _. iFrame. }
    { iIntros "_ [[%y'[pc'' Ψ]]_]". iMod (pc_resolve with "pc''") as "obs".
      iMod (vo_pc_update with "vo' pc'") as "[vo' pc']".
      iMod (vo_vo_update with "vox vox'") as "[vox _]". iModIntro.
      iSplitL "pc' Ψ"; [iExists _; by iFrame|]. iSplit; [|done]. iExists _.
      iFrame "vo' vox". iApply "→pc".
      by iApply (proph_obs_impl with "obs")=> ? ->. }
    iModIntro. iDestruct ("→α'β" with "αβ") as "[$$]". rewrite pbor_ctok_unseal.
    iRight. iExists _. iFrame.
  Qed.
  Lemma pobor_pbor_ctok_reborrow `{!GenUpd M} {intp X Y α q ξ Φ β r y η Ψ} f :
    pobor_tok (X:=X) α q ξ Φ -∗ r.[β] -∗ pbor_ctok (X:=Y) β y η Ψ -∗
    (∀ y', [†α] -∗ pbor_tok β y' η Ψ -∗ M (intp (Φ (f y'))))
      =[pborrow_wsat M intp]=∗ ∃ η' : prvar _,
      q.[α] ∗ r.[β] ∗ ⟨π, π ξ = f (π η')⟩ ∗ pbor_ctok (α ⊓ β) y η' Ψ.
  Proof.
    iIntros "Φ β c →Φ". iMod (pbor_ctok_open with "β c") as "[o Ψ]".
    iApply (pobor_pobor_tok_reborrow with "Φ o Ψ →Φ").
  Qed.
  Lemma pobor_pbor_tok_reborrow `{!GenUpd M} {intp X Y α q ξ Φ β r y η Ψ} f :
    pobor_tok (X:=X) α q ξ Φ -∗ r.[β] -∗ pbor_tok (X:=Y) β y η Ψ -∗
    (∀ y', [†α] -∗ pbor_tok β y' η Ψ -∗ M (intp (Φ (f y')))) -∗
      modw M (pborrow_wsat M intp) (∃ η' : prvar _,
      q.[α] ∗ r.[β] ∗ ⟨π, π ξ = f (π η')⟩ ∗ pbor_ctok (α ⊓ β) y η' Ψ).
  Proof.
    iIntros "Φ β c →Φ". iMod (pbor_tok_open with "β c") as "[o Ψ]".
    iMod (pobor_pobor_tok_reborrow with "Φ o Ψ →Φ") as "$". by iIntros.
  Qed.
End pborrow.

(** Allocate [pborrow_wsat] *)
Lemma pborrow_wsat_alloc `{!pborrowGpreS TY PROP Σ} :
  ⊢ |==> ∃ _ : pborrowGS TY PROP Σ, ∀ M intp, pborrow_wsat M intp.
Proof.
  iMod proph_init as (?) "_". iMod borrow_wsat_alloc as (?) "W".
  iModIntro. iExists (PborrowGS _ _ _ _ _ _). by iIntros.
Qed.
