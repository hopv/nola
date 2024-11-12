(** * More on basic pointer types *)

From nola.examples.rust_halt Require Export box shrref mutref prod sum.

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
    iDestruct (lft_incl'_live_acc (α:=α) with "κ") as (?) "[α →κ]".
    iMod (pbord_open (M:=borrowM) with "α b") as "/=[o (% & ↦ & T)]".
    iMod (ty_own_proph with "κ' T") as (ηl ??) "[ηl →T]".
    iMod (pobord_resolve (M:=borrowM) with "o ηl") as "/=(ηl & obs & →b)";
      [done|].
    iMod ("→T" with "ηl") as "[$ T]".
    iMod ("→b" with "[$↦ $T //]") as "[α b]". rewrite bor_tok_bor.
    iDestruct ("→κ" with "α") as "κ".
    iDestruct (lft_incl'_live_acc (α:=κ ⊓ α) with "κ") as (?) "[κα →κ]".
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

  (** Split a shared reference over a product *)
  Lemma sub_shrref_prod_split p
    `(!EtcxExtract (X:=X *'ₓ Y) (Yl:=Zl) (Zl:=Zl')
        (p ◁ ty_shrref α (ty_prod T U)) Γ Γr get getr, !Ty T, !Ty U) {κ} :
    ⊢ sub κ Γ
        (p +ₗ #0 ◁ ty_shrref α T ᵖ:: p +ₗ #(ty_size T) ◁ ty_shrref α U ᵖ:: Γr)
        (λ post zl, let '(x, y)' := get zl in post (x, y, getr zl)').
  Proof.
    rewrite sub_unseal. iIntros (????) "!> $ $ pre". rewrite etcx_extract.
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
    iDestruct (lft_incl'_live_acc (α:=α) with "κ") as (?) "[α →κ]".
    iMod (pbord_open (M:=borrowM) with "α b")
      as "/=[o (% & ↦ & % & % & -> & T & U)]".
    rewrite heap_pointsto_vec_app. iDestruct "↦" as "[↦ ↦']".
    iDestruct (ty_own_size with "T") as %->.
    iMod (ty_own_proph with "κ' T") as (ηl ??) "[ηl →T]".
    iMod (ty_own_proph with "κ'' U") as (ηl' ??) "[ηl' →U]".
    iDestruct (proph_toks_fuse with "ηl ηl'") as (?) "[ηll' →ηll']".
    iMod (pobord_subdiv (TY:=xty) (M:=borrowM) (X:=X *'ₓ Y) [X; Y]
      (λ _ '(x,y,_)', (x,y)') _
      ᵖ[(_,_,cif_pointsto_ty T _ _)'; (_,_,cif_pointsto_ty U _ _)'] []
      with "o ηll'") as ([ζ[ζ'[]]]) "(ηll' & obs & big)"=>/=.
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
End ptrs_more.
