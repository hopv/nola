(** * More on basic pointer types *)

From nola.examples.rust_halt Require Export box shrref mutref prod.

Section ptrs_more.
  Context `{!rust_haltGS CON Σ, rust_haltJ CON JUDG Σ, !Csem CON JUDG Σ,
    !Jsem JUDG (iProp Σ), !rust_haltC CON, !rust_haltCS CON JUDG Σ,
    !rust_haltJS CON JUDG Σ}.

  (** Turn a mutable reference into a shared reference, resolving the prophecy
    to the actual value *)
  Lemma sub_share p
    `(!EtcxExtract (Yl:=Yl) (Zl:=Zl) (p ◁ ty_mutref (X:=X) α T) Γ Γr get getr,
      !Ty T, !TyOp T κ, !LftIncl κ α) :
    ⊢ sub κ Γ (p ◁ ty_shrref α T ᵖ:: Γr) (λ post yl,
        let '(x, x')' := get yl in x' = x → post (x, getr yl)')%type.
  Proof.
    rewrite sub_unseal. iIntros (????) "!> [κ κ'] $ pre".
    rewrite etcx_extract ty_mutref_unseal ty_shrref_unseal /=.
    iIntros "[(% & % & $ & big) Γr]". iDestruct "big" as (??? pπ [=->]? eq) "b".
    rewrite sem_cif_in /=.
    iDestruct (lft_incl'_live_acc α with "κ") as (?) "[α →κ]".
    iMod (pbord_open (M:=borrowM) with "α b") as "/=[o (% & ↦ & T)]".
    iMod (ty_own_proph with "κ' T") as (ηl ??) "[ηl →T]".
    iMod (pobord_resolve (M:=borrowM) with "o ηl") as "/=(ηl & obs & →b)";
      [done|].
    iMod ("→T" with "ηl") as "[$ T]".
    iMod ("→b" with "[$↦ $T //]") as "[α b]". rewrite bor_tok_bor.
    iDestruct ("→κ" with "α") as "κ".
    iDestruct (lft_incl'_live_acc (κ ⊓ α) with "κ") as (?) "[κα →κ]".
    iMod (ty_share with "κα b") as "[κα T]". iDestruct ("→κ" with "κα") as "$".
    iMod (store_alloc_pers with "T") as "T". iModIntro. iExists (λ _, (_, _)').
    iFrame "Γr". iSplit.
    { iApply (proph_obs_impl2 with "pre obs")=> ?. by rewrite eq=> ?. }
    iExists _, _, _, _. rewrite sem_cif_in /=. by iFrame.
  Qed.
  Lemma type_share p
    `(!EtcxExtract (Yl:=Yl) (Zl:=Yl') (p ◁ ty_mutref (X:=X) α T) Γi Γr get getr,
      !Ty T, !TyOp T κ, !LftIncl κ α) {Zl Γo e pre} :
    type (Yl:=Zl) κ (p ◁ ty_shrref α T ᵖ:: Γr) e Γo pre ⊢
      type κ Γi e Γo (λ post yl,
        let '(x, x')' := get yl in x' = x → pre post (x, getr yl)')%type.
  Proof.
    iIntros "type".
    iApply (type_in (prei:=λ post _, _ → post _) with "[] type").
    iApply sub_share.
  Qed.

  (** Mutably borrow a box pointer taking a fresh prophecy *)
  Lemma sub_borrow_box p α
    `(!EtcxExtract (X:=X) (Yl:=Yl) (Zl:=Zl) (p ◁ ty_box T) Γ Γr get getr,
      !Ty T) {κ} :
    ⊢ sub κ Γ (p ◁ ty_mutref α T ᵖ:: p ◁[†α] ty_box T ᵖ:: Γr) (λ post yl,
        ∀ x' : X, post ((get yl, x')', x', getr yl)')%type.
  Proof.
    rewrite sub_unseal. iIntros (??? xlπ) "!> $$ pre".
    rewrite etcx_extract ty_box_unseal ty_mutref_unseal /=.
    iIntros "[p Γr]". iDestruct "p" as (??<-????[=->]? eq) "(↦ & †l & T)".
    rewrite sem_cif_in /=. iMod (stored_acc with "T") as "T".
    iDestruct (ty_own_size with "T") as %->.
    iMod (pbor_plend_new (M:=borrowM) _ α _ _ (cif_pointsto_ty T _ _)
      with "[↦ T]") as (ξ) "[b l]"=>/=; [by iFrame|].
    iModIntro. iExists (λ π : prasn, ((_, π ξ)', _, _)'). iSplit.
    { iApply (proph_obs_impl with "pre")=> ?. by rewrite -eq=> ?. }
    iFrame "Γr". iSplitL "b".
    { iExists _, _. iSplit; [done|]. iExists _, _, _, _. rewrite sem_cif_in /=.
      by iFrame. }
    iExists _. iSplit; [done|]. iIntros "†".
    iMod (plendd_retrieve (M:=borrowM) with "† l") as
      (?) "/=[$ (%d' & % & $ & T)]".
    iDestruct (ty_own_size with "T") as %eql. rewrite -eql. iFrame "†l".
    iExists (S d'), _, _. rewrite sem_cif_in /=.
    iMod (store_alloc with "T") as "$". iPureIntro. do 2 split=>//. lia.
  Qed.
  Lemma type_borrow_box p
    `(!EtcxExtract (X:=X) (Yl:=Yl) (Zl:=Yl') (p ◁ ty_box T) Γi Γr get getr,
      !Ty T, !LftIncl κ α) {Zl Γo e pre} :
    type (Yl:=Zl) κ (p ◁ ty_mutref α T ᵖ:: p ◁[†α] ty_box T ᵖ:: Γr) e Γo pre ⊢
      type κ Γi e Γo (λ post yl,
        ∀ x' : X, pre post ((get yl, x')', x', getr yl)')%type.
  Proof.
    iIntros "type".
    iApply (type_in (prei:=λ post _, ∀ x', post _) with "[] type").
    iApply sub_borrow_box.
  Qed.

  (** Mutably reborrow a mutable reference, taking a fresh prophecy *)
  Lemma sub_reborrow p β
    `(!EtcxExtract (Yl:=Yl) (Zl:=Zl) (p ◁ ty_mutref (X:=X) α T) Γ Γr get getr,
      !LftIncl κ β, !LftIncl β α) :
    ⊢ sub κ Γ (p ◁ ty_mutref β T ᵖ:: p ◁[†β] ty_mutref α T ᵖ:: Γr) (λ post yl,
        let '(x, x')' := get yl in
        ∀ x'' : X, post ((x, x'')', (x'', x')', getr yl)')%type.
  Proof.
    rewrite sub_unseal. iIntros (? t ? xlπ) "!> [κ κ'] $ pre".
    rewrite etcx_extract ty_mutref_unseal /=. iIntros "[p Γr]".
    iDestruct "p" as (?? <- l ? ξ xπ [=->]? eq) "b". rewrite sem_cif_in /=.
    iMod (pbor_plend_new (M:=borrowM) _ β _ _
      (λ d xπ, cif_pbor α d xπ ξ (cif_pointsto_ty T l t)) with "[b]")
      as (η) "[b' l]"=>/=; [by rewrite sem_cif_in /=|].
    iDestruct (lft_incl'_live_acc β with "κ") as (?) "[β →κ]".
    iMod (pbord_open (M:=borrowM) with "β b'") as "/=[o b]".
    rewrite sem_cif_in /=.
    iDestruct (lft_incl'_live_acc α with "κ'") as (?) "[α →κ']"; [by etrans|].
    iMod (pobord_pbord_reborrow (M:=borrowM) (λ _, id) with "[] α o b []")
      as "(ξ & ↦T & big)"=>/=. { done. } { iApply lft_incl'_sincl. }
    { iIntros (??) "_ b". by rewrite sem_cif_in /=. }
    iMod ("big" $! [] 1%Qp with "[//] [//]") as (ζ) "(obs & _ & big)".
    iMod ("big" with "ξ ↦T") as "(β & α & b)". iDestruct ("→κ" with "β") as "$".
    iDestruct ("→κ'" with "α") as "$". iModIntro.
    iExists (λ π, ((xπ π, π ζ)', (π η, π ξ)', _)'). iFrame "Γr". iSplit.
    { iApply (proph_obs_impl2 with "pre obs")=> π. by rewrite (eq π)=> to ->. }
    iSplitL "b".
    { iExists _, _. iSplit; [done|]. iExists _, _, _, _. rewrite sem_cif_in /=.
      by iFrame "b". }
    iExists _. iSplit; [done|]. iIntros "†".
    iMod (plendd_retrieve (M:=borrowM) with "† l") as (xπ') "/=[eqz [%d' b]]".
    rewrite sem_cif_in /=. iModIntro. iExists (S d'), _. iSplitL "eqz".
    { iApply (proph_eqz_fpi (λ π x, (x, π ξ)') with "eqz")=> > []//. }
    iExists _, _, _, _. rewrite sem_cif_in /=. iFrame "b". iPureIntro.
    do 2 split=>//. lia.
  Qed.
  Lemma type_reborrow p β
    `(!EtcxExtract (Yl:=Yl) (Zl:=Yl') (p ◁ ty_mutref (X:=X) α T) Γi Γr get getr,
      !LftIncl κ β, !LftIncl β α) {Zl Γo e pre} :
    type (Yl:=Zl) κ
      (p ◁ ty_mutref β T ᵖ:: p ◁[†β] ty_mutref α T ᵖ:: Γr) e Γo pre ⊢
      type κ Γi e Γo (λ post yl, let '(x, x')' := get yl in
        ∀ x'' : X, pre post ((x, x'')', (x'', x')', getr yl)')%type.
  Proof.
    iIntros "type".
    iApply (type_in (prei:=λ post _, ∀ x', post _) with "[] type").
    iApply sub_reborrow.
  Qed.

  (** Dereference a shared reference to a box pointer *)
  Lemma type_deref_shrref_box p
    `(!EtcxExtract (Yl:=Yl) (Zl:=Zl) (p ◁ ty_shrref α (ty_box (X:=X) T)) Γ Γr
        get getr,
      !Ty T, !LftIncl κ α) :
    ⊢ type κ Γ (!p) (λ r, r ◁ ty_shrref α T ᵖ:: Γr)
        (λ post yl, post (get yl, getr yl)').
  Proof.
    rewrite type_unseal. iIntros (??? xlπ) "!> κ $ pre".
    rewrite etcx_extract ty_shrref_unseal ty_box_unseal /=. iIntros "[p Γr]".
    iDestruct "p" as (??????[=->]? eq) "big". wp_path p. rewrite sem_cif_in /=.
    iMod (stored_acc with "big") as "/=big".
    iDestruct "big" as (????? eq') "(>#⊑ & >↦ & #?)".
    iDestruct (lft_incl'_live_acc α with "κ") as (?) "[α →κ]".
    iMod (spointsto_acc with "α ↦") as (?) "[↦ →α]". wp_read.
    iMod ("→α" with "↦") as "α". iDestruct ("→κ" with "α") as "$". iModIntro.
    iFrame "pre Γr"=>/=. iExists _, _. iSplit=>//. iExists _, _, _.
    do 2 iSplit=>//. iSplit. { iPureIntro=> ?. etrans; [exact: eq'|exact: eq]. }
    iModIntro. rewrite !sem_cif_in /=. iApply store_wand; [|done].
    iIntros (????) "T !>". by iApply (ty_shr_lft with "⊑ T").
  Qed.

  (** Dereference a shared reference to a mutable reference *)
  Lemma type_deref_shrref_mutref p
    `(!EtcxExtract (Yl:=Yl) (Zl:=Zl)
        (p ◁ ty_shrref α (ty_mutref β (X:=X) T)) Γ Γr get getr,
      !Ty T, !LftIncl κ α, !LftIncl κ β) :
    ⊢ type κ Γ (!p) (λ r, r ◁ ty_shrref (α ⊓ β) T ᵖ:: Γr)
        (λ post yl, post ((get yl).1', getr yl)').
  Proof.
    rewrite type_unseal. iIntros (??? xlπ) "!> κ $ pre".
    rewrite etcx_extract ty_shrref_unseal ty_mutref_unseal /=. iIntros "[p Γr]".
    iDestruct "p" as (??????[=->]? eq) "big". wp_path p. rewrite sem_cif_in /=.
    iMod (stored_acc with "big") as "/=big".
    iDestruct "big" as (?????? eq') "(>#⊑ & >↦ & _ & #?)".
    iDestruct (lft_incl'_live_acc (β ⊓ α) with "κ") as (?) "[βα →κ]".
    iMod (spointsto_acc with "βα ↦") as (?) "[↦ →βα]". wp_read=>/=.
    iMod ("→βα" with "↦") as "βα". iDestruct ("→κ" with "βα") as "$". iModIntro.
    rewrite [_ ⊓ _]comm. iFrame "pre Γr". iExists _, _. iSplit=>//.
    iExists _, _, _. do 2 iSplit=>//. iSplit; last first.
    { iModIntro. rewrite !sem_cif_in /=. iApply store_wand; [|done].
      iIntros (????) "T !>". iApply (ty_shr_lft with "[] T").
      by iApply lft_sincl_meet_mono_l. }
    iPureIntro=> ?. by rewrite -eq eq'.
  Qed.

  (** Dereference a mutable reference to a box pointer *)
  Lemma type_deref_mutref_box p
    `(!EtcxExtract (Yl:=Yl) (Zl:=Zl) (p ◁ ty_mutref α (ty_box (X:=X) T)) Γ Γr
        get getr,
      !Ty T, !TyOp T κ, !LftIncl κ α) :
    ⊢ type κ Γ (!p) (λ r, r ◁ ty_mutref α T ᵖ:: Γr)
        (λ post yl, post (get yl, getr yl)').
  Proof.
    rewrite type_unseal. iIntros (??? xlπ) "!> [κ κ'] $ pre".
    rewrite etcx_extract ty_mutref_unseal ty_box_unseal /=. iIntros "[p Γr]".
    iDestruct "p" as (???????[=->]? eq) "b". wp_path p. rewrite sem_cif_in /=.
    iDestruct (lft_incl'_live_acc α with "κ") as (?) "[α →κ]".
    iMod (pbord_open (M:=borrowM) with "α b") as "/=[o (% & >↦ & big)]".
    iDestruct "big" as (????->? eq') "(↦' & † & T)". rewrite sem_cif_in /=.
    iMod (stored_acc with "T") as "T". rewrite heap_pointsto_vec_singleton.
    wp_read. iDestruct (ty_own_size with "T") as %->.
    iMod (ty_own_proph with "κ' T") as (ηl ??) "[ηl →T]".
    iMod (pobord_subdiv (M:=borrowM) ᵖ[(_,_,cif_pointsto_ty T _ _)']
      (λ _ '(p,_)', p) [] with "o ηl") as ([ζ[]]) "(ηl & obs & big)".
    { by move=> ??[?[]][?[]]<-. } { done. }
    iMod ("→T" with "ηl") as "[$ T]".
    iMod ("big" with "[] [↦' T] [//] [↦ †]") as "(α & [b _] & _)"=>/=.
    { iApply lft_sincl_refl. } { iFrame. }
    { iIntros (?) "_ [(%d' & % & ↦' & T) _] _".
      rewrite -heap_pointsto_vec_singleton. iFrame "↦".
      iDestruct (ty_own_size with "T") as %eql. rewrite -eql. iFrame "† ↦'".
      iExists (S d'), _, _. rewrite sem_cif_in /=.
      iMod (store_alloc with "T") as "$". iPureIntro. do 2 split=>//. lia. }
    iDestruct ("→κ" with "α") as "$". iModIntro.
    iExists (λ π : prasn, ((_, π ζ)', _)'). iFrame "Γr". iSplit.
    { iApply (proph_obs_impl2 with "pre obs")=> ? + <-. by rewrite eq. }
    iExists _, _. iSplit; [done|]. iExists _, _, _, _. rewrite sem_cif_in /=.
    rewrite pbor_tok_pbor. iFrame. iPureIntro. do 2 split=>//. move=> ?.
    by rewrite eq'.
  Qed.

  (** Dereference a mutable reference to a mutable reference, partially
    resolving the outer prophecy *)
  Lemma type_deref_mutref_mutref p
    `(!EtcxExtract (Yl:=Yl) (Zl:=Zl)
        (p ◁ ty_mutref α (ty_mutref β (X:=X) T)) Γ Γr get getr,
      !TyOp T κ, !LftIncl κ α, !LftIncl κ β) :
    ⊢ type κ Γ (!p) (λ r, r ◁ ty_mutref (α ⊓ β) T ᵖ:: Γr)
        (λ post yl, let '((x, x')', (xa, xa')')' := get yl in
          xa' = x' → post ((x, xa)', getr yl)')%type.
  Proof.
    rewrite type_unseal. iIntros (??? xlπ) "!> (κ & κ' & κ'') $ pre".
    rewrite etcx_extract ty_mutref_unseal /=. iIntros "[p Γr]".
    iDestruct "p" as (????? ξ ?[=->]? eq) "b". wp_path p. rewrite sem_cif_in /=.
    iDestruct (lft_incl'_live_acc (α ⊓ β) with "κ'") as (?) "[αβ →κ']".
    iDestruct (pbor_lft with "[] b") as "b"; [by iApply lft_sincl_meet_l|].
    iMod (pbord_open (M:=borrowM) with "αβ b") as "/=[o (% & >↦ & big)]".
    iDestruct "big" as (? d' η ?->? eq') "b'". rewrite sem_cif_in /=.
    rewrite heap_pointsto_vec_singleton. wp_read.
    iDestruct (lft_incl'_live_acc β with "κ''") as (?) "[β →κ'']".
    iMod (pobord_pbord_reborrow (TY:=xty) (M:=borrowM) (X:=_ *'ₓ _)
      (λ π x', (x', π η)') S with "[] β o b' [↦]")
      as "/=(η & (% & ↦' & T) & big)"=>/=.
    { by move=> > [??]. } { iApply lft_sincl_meet_r. }
    { iIntros (??) "_ b !>". rewrite -heap_pointsto_vec_singleton. iFrame "↦".
      iExists _, _, _, _. rewrite sem_cif_in /=. iFrame "b". iPureIntro.
      do 2 split=>//. lia. }
    iMod (ty_own_proph with "κ T") as (ζl ??) "[ζl →T]".
    iDestruct (proph_toks_tok_fuse with "ζl η") as (?) "[ζlη →ζlη]".
    iMod ("big" with "[%] ζlη") as (?) "(obs & ζlη & big)".
    { move=> ?. apply proph_dep_f2; [done|]. exact: proph_dep_prvar. }
    iDestruct ("→ζlη" with "ζlη") as "[ζl η]". iMod ("→T" with "ζl") as "[$ T]".
    iMod ("big" with "η [$↦' $T //]") as "(αβ & β & b)". iModIntro.
    iDestruct ("→κ'" with "αβ") as "$". iDestruct ("→κ''" with "β") as "$".
    iExists (λ _, (_, _)'). iFrame "Γr". iSplit.
    { iApply (proph_obs_impl2 with "obs pre")=> ?. rewrite eq eq'=> -> to.
      exact: to. }
    iExists _, (S d'). iSplit; [done|]. iExists _, _, _, _.
    rewrite sem_cif_in /=. iFrame "b". iPureIntro. do 2 split=>//. lia.
  Qed.

  (** Split a shared reference over a product *)
  Lemma sub_shrref_prod_split p
    `(!EtcxExtract (X:=X *'ₓ Y) (Yl:=Zl) (Zl:=Zl')
        (p ◁ ty_shrref α (ty_prod T U)) Γ Γr get getr, !Ty T, !Ty U) {κ} :
    ⊢ sub κ Γ
        (p +ₗ #0 ◁ ty_shrref α T ᵖ:: p +ₗ #(ty_size T) ◁ ty_shrref α U ᵖ:: Γr)
        (λ post zl, let '(x, y)' := get zl in post (x, y, getr zl)').
  Proof.
    rewrite sub_unseal. iIntros (????) "!> $$ pre". rewrite etcx_extract.
    rewrite ty_shrref_unseal ty_prod_unseal /=. iIntros "[p Γr]".
    iDestruct "p" as (?? <- ???[=->]? eq) "big". rewrite sem_cif_in /=.
    iMod (stored_acc with "big") as "/=[T U]".
    iMod (store_alloc_pers with "T") as "T".
    iMod (store_alloc_pers with "U") as "U". iModIntro. iFrame "pre Γr".
    iSplitL "T"; iExists _, _; (iSplit; [done|]); iExists _, _, _;
      rewrite sem_cif_in /=; iFrame; [rewrite shift_loc_0|];
      unfold compose; by setoid_rewrite eq.
  Qed.
  Lemma type_shrref_prod_split p
    `(!EtcxExtract (X:=X *'ₓ Y) (Yl:=Zl) (Zl:=Zl')
        (p ◁ ty_shrref α (ty_prod T U)) Γi Γr get getr, !Ty T, !Ty U)
    {κ Zl'' Γo e pre} :
    type (Yl:=Zl'') κ
      (p +ₗ #0 ◁ ty_shrref α T ᵖ:: p +ₗ #(ty_size T) ◁ ty_shrref α U ᵖ:: Γr)
      e Γo pre ⊢
      type κ Γi e Γo
        (λ post zl, let '(x, y)' := get zl in pre post (x, y, getr zl)').
  Proof.
    iIntros "type". iApply (type_in (prei:=λ post _, post _) with "[] type").
    iApply sub_shrref_prod_split.
  Qed.

  (** Split a mutable reference over a product, splitting the prophecy *)
  Lemma sub_mutref_prod_split p
    `(!EtcxExtract (Yl:=Zl) (Zl:=Zl')
        (p ◁ ty_mutref (X:=X *'ₓ Y) α (ty_prod T U)) Γ Γr get getr,
      !Ty T, !Ty U, !TyOp T κ, !TyOp U κ, !LftIncl κ α) :
    ⊢ sub κ Γ
        (p +ₗ #0 ◁ ty_mutref α T ᵖ:: p +ₗ #(ty_size T) ◁ ty_mutref α U ᵖ:: Γr)
        (λ post zl, let '((x, y)', (x', y')')' := get zl in
          post ((x, x')', (y, y')', getr zl)').
  Proof.
    rewrite sub_unseal. iIntros (????) "!> (κ & κ' & κ'') $ pre".
    rewrite etcx_extract ty_mutref_unseal ty_prod_unseal /=. iIntros "[p Γr]".
    iDestruct "p" as (?? <- ??? pπ [=->]? eq) "b". rewrite sem_cif_in /=.
    iDestruct (lft_incl'_live_acc α with "κ") as (?) "[α →κ]".
    iMod (pbord_open (M:=borrowM) with "α b")
      as "/=[o (% & ↦ & % & % & -> & T & U)]".
    rewrite heap_pointsto_vec_app. iDestruct "↦" as "[↦ ↦']".
    iDestruct (ty_own_size with "T") as %->.
    iMod (ty_own_proph with "κ' T") as (ηl ??) "[ηl →T]".
    iMod (ty_own_proph with "κ'' U") as (ηl' ??) "[ηl' →U]".
    iDestruct (proph_toks_fuse with "ηl ηl'") as (?) "[ηll' →ηll']".
    iMod (pobord_subdiv (TY:=xty) (M:=borrowM) (X:=X *'ₓ Y)
      ᵖ[(_,_,cif_pointsto_ty T _ _)'; (_,_,cif_pointsto_ty U _ _)']
      (λ _ '(x,y,_)', (x,y)') [] with "o ηll'")
      as ([ζ[ζ'[]]]) "(ηll' & obs & big)"=>/=.
    { by move=> ??[?[?[]]][?[?[]]][<-<-]. } { done. }
    iDestruct ("→ηll'" with "ηll'") as "[ηl ηl']".
    iMod ("→T" with "ηl") as "[κ' T]". iMod ("→U" with "ηl'") as "[κ'' U]".
    iMod ("big" with "[] [$↦ $T $↦' $U //] [//] []")
      as "(α & (b & b' & _) & _)". { iApply lft_sincl_refl. }
    { iIntros (?) "_ ((%dt & % & ↦ & T) & (%du & % & ↦' & U) & _) _ !>".
      iExists (dt `max` du), (_ ++ _). rewrite heap_pointsto_vec_app.
      iFrame "↦". iDestruct (ty_own_size with "T") as %->. iFrame "↦'".
      iExists _, _. iSplit; [done|]. unfold compose=>/=.
      iSplitL "T"; iStopProof; apply: ty_own_depth; lia. }
    iModIntro. iDestruct ("→κ" with "α") as "$". iFrame "κ' κ''".
    iExists (λ π, (((pπ π).1', π ζ)', ((pπ π).2', π ζ')', _)'). iFrame "Γr".
    iSplit.
    { iApply (proph_obs_impl2 with "pre obs")=>/= π.
      rewrite (eq π)=> + eq'. by rewrite eq'. }
    setoid_rewrite sem_cif_in=>/=. rewrite !pbor_tok_pbor. iFrame "b b'".
    rewrite shift_loc_0. iPureIntro. split; by eexists _, _.
  Qed.
  Lemma type_mutref_prod_split p
    `(!EtcxExtract (Yl:=Zl) (Zl:=Zl')
        (p ◁ ty_mutref (X:=X *'ₓ Y) α (ty_prod T U)) Γi Γr get getr,
      !Ty T, !Ty U, !TyOp T κ, !TyOp U κ, !LftIncl κ α)
    {Zl'' Γo e pre} :
    type (Yl:=Zl'') κ
      (p +ₗ #0 ◁ ty_mutref α T ᵖ:: p +ₗ #(ty_size T) ◁ ty_mutref α U ᵖ:: Γr)
      e Γo pre ⊢
      type κ Γi e Γo
        (λ post zl, let '((x, y)', (x', y')')' := get zl in
          pre post ((x, x')', (y, y')', getr zl)').
  Proof.
    iIntros "type". iApply (type_in (prei:=λ post _, post _) with "[] type").
    iApply sub_mutref_prod_split.
  Qed.

  (** Update the body type of a mutable reference by mutual subtyping *)
  Lemma sub_mutref_subty p {X} T {Y} U f g
    `(!EtcxExtract (Yl:=Zl) (Zl:=Zl') (p ◁ ty_mutref α T) Γ Γr get getr,
      !TyOp T κ, !LftIncl κ α) :
    (∀ x, f (g x) = x) →
    subtyd' X Y T U f -∗ subtyd U T g -∗
      sub κ Γ (p ◁ ty_mutref α U ᵖ:: Γr) (λ post zl,
        let '(x, x')' := get zl in post ((f x, f x')', getr zl)').
  Proof.
    rewrite subty_unseal sub_unseal=> fg. iIntros "[_[#TU _]] [_[#UT _]] !>".
    iIntros (????) "[κ κ'] $ pre". rewrite etcx_extract ty_mutref_unseal /=.
    iIntros "[p Γr]". iDestruct "p" as (?? <- ??? pπ [=->]? eq) "b".
    rewrite sem_cif_in /=.
    iDestruct (lft_incl'_live_acc α with "κ") as (?) "[α →κ]".
    iMod (pbord_open (M:=borrowM) with "α b") as "/=[o (% & ↦ & T)]".
    iMod (ty_own_proph with "κ' T") as (ηl ??) "[ηl →T]".
    iMod (pobord_subdiv (TY:=xty) (M:=borrowM)
      ᵖ[(_,_,cif_pointsto_ty U _ _)'] (λ _ '(y,_)', g y) [] with "o ηl")
      as ([ζ[]]) "(ηl & obs & big)"=>/=.
    { move=> ??[?[]][?[]] /(f_equal f). by rewrite !fg=> <-. } { done. }
    iMod ("→T" with "ηl") as "[$ T]". iDestruct ("TU" with "T") as "U".
    iMod ("big" with "[] [$↦ $U //] [//] []") as "(α & (b & _) & _)".
    { iApply lft_sincl_refl. }
    { iIntros (?) "_ [(% & % & ↦ & U) _] _ !>". iFrame "↦".
      iDestruct ("UT" with "U") as "$". }
    iModIntro. iDestruct ("→κ" with "α") as "$". iExists (λ _, (_, _)').
    iFrame "Γr". iSplit.
    { iApply (proph_obs_impl2 with "pre obs")=>/= π.
      rewrite (eq π)=> + eq'. by rewrite eq'. }
    iExists _, _. iSplit; [done|]. iExists _, _, _, _. rewrite sem_cif_in /=.
    rewrite pbor_tok_pbor. iFrame "b". iPureIntro. do 2 split=>//.
    move=> ?. by rewrite fg.
  Qed.
  Lemma type_mutref_subty p {X} T {Y} U f g
    `(!EtcxExtract (Yl:=Zl) (Zl:=Zl') (p ◁ ty_mutref α T) Γi Γr get getr,
      !TyOp T κ, !LftIncl κ α) {Zl'' Γo e pre} :
    (∀ x, f (g x) = x) →
    subtyd' X Y T U f -∗ subtyd U T g -∗
      type (Yl:=Zl'') κ (p ◁ ty_mutref α U ᵖ:: Γr) e Γo pre -∗
      type κ Γi e Γo (λ post zl,
        let '(x, x')' := get zl in pre post ((f x, f x')', getr zl)').
  Proof.
    iIntros (fg) "#sub #sub' type".
    iApply (type_in (prei:=λ post _, post _) with "[] type").
    by iApply sub_mutref_subty.
  Qed.
End ptrs_more.
