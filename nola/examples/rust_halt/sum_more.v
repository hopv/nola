(** * More on the sum type *)

From nola.examples.rust_halt Require Export sum box shrref mutref.

Section sum_more.
  Context `{!rust_haltGS CON Σ, rust_haltJ CON JUDG Σ, !Csem CON JUDG Σ,
    !Jsem JUDG (iProp Σ), !rust_haltC CON, !rust_haltCS CON JUDG Σ,
    !rust_haltJS CON JUDG Σ}.

  (** Case analysis over a shared reference to a sum *)
  Lemma type_case_sum_shrref p
    `(!EtcxExtract (Yl:=Zl) (Zl:=Zl')
        (p ◁ ty_shrref α (ty_sum (X:=X) (Y:=Y) T U)) Γi Γr get getr,
      !Ty T, !Ty U, !LftIncl κ α)
    {Zl'' Γo e e' pre pre'} :
    type (Yl:=Zl'') κ (p +ₗ #1 ◁ ty_shrref α T ᵖ:: Γr) e Γo pre -∗
    type κ (p +ₗ #1 ◁ ty_shrref α U ᵖ:: Γr) e' Γo pre' -∗
      type κ Γi (case! !p of [e; e']) Γo (λ post zl, let zl' := getr zl in
        match get zl with
          inl x => pre post (x, zl')' | inr y => pre' post (y, zl')' end).
  Proof.
    rewrite type_unseal. iIntros "#type #type' !>" (????) "κ t #pre".
    rewrite etcx_extract ty_shrref_unseal ty_sum_unseal /=. iIntros "[p Γr]".
    iDestruct "p" as (?? peq ???[=->]? eq) "sum". wp_path p.
    rewrite sem_cif_in /=. iMod (stored_acc with "sum") as "sum"=>/=.
    iDestruct "sum" as (b) "[>↦ big]".
    iDestruct (lft_incl'_live_acc α with "κ") as (?) "[α →κ]".
    iMod (spointsto_acc with "α ↦") as (?) "[↦ →α]". wp_read.
    iMod ("→α" with "↦") as "α". iDestruct ("→κ" with "α") as "κ". wp_case.
    case: b=>/=; iDestruct "big" as (? eq') "[S _]";
      iMod (store_alloc_pers with "S") as "S";
      ((iApply ("type'" with "κ t") || iApply ("type" with "κ t"));
        [iApply (proph_obs_impl with "pre")=> ?; rewrite -eq eq'=> pr;
          exact: pr|]);
      iFrame "Γr"; rewrite -peq; iExists _, _; (iSplit; [done|]);
      iExists _, _, _; rewrite sem_cif_in /=; by iFrame "S".
  Qed.

  (** Case analysis over a mutable reference to a sum *)
  Lemma type_case_sum_mutref p
    `(!EtcxExtract (Yl:=Zl) (Zl:=Zl')
        (p ◁ ty_mutref α (ty_sum (X:=X) (Y:=Y) T U)) Γi Γr get getr,
      !Ty T, !TyOp T κ, !Ty U, !TyOp U κ, !LftIncl κ α)
    {Zl'' Γo e e' pre pre'} :
    type (Yl:=Zl'') κ (p +ₗ #1 ◁ ty_mutref α T ᵖ:: Γr) e Γo pre -∗
    type κ (p +ₗ #1 ◁ ty_mutref α U ᵖ:: Γr) e' Γo pre' -∗
      type κ Γi (case! !p of [e; e']) Γo (λ post zl, let zl' := getr zl in
        let '(s, s')' := get zl in
        match s with
        | inl x => ∀ x' : X, s' = inl x' → pre post ((x, x')', zl')'
        | inr y => ∀ y' : Y, s' = inr y' → pre' post ((y, y')', zl')' end)%type.
  Proof.
    rewrite type_unseal. iIntros "#type #type' !>" (????) "[κ κ'] t #pre".
    rewrite etcx_extract ty_mutref_unseal ty_sum_unseal /=. iIntros "[p Γr]".
    iDestruct "p" as (?? peq ? d' ??[=->]? eq) "b". wp_path p.
    rewrite sem_cif_in /=.
    iDestruct (lft_incl'_live_acc α with "κ") as (?) "[α →κ]".
    iMod (pbord_open (M:=borrowM) with "α b") as "/=[o (% & ↦ & big)]".
    iDestruct "big" as (b ??->) "big".
    rewrite heap_pointsto_vec_cons heap_pointsto_vec_app.
    iDestruct "↦" as "(>↦ & ↦S & ↦r)". wp_read. wp_case.
    case: b=>/=; iDestruct "big" as (? eq' ?) "S";
      [iDestruct (ty_own_size with "S") as %->|
        iDestruct (ty_own_size with "S") as %->];
      [iMod (ty_own_proph with "κ' S") as (ηl ??) "[ηl →S]"|
        iMod (ty_own_proph with "κ' S") as (ηl ??) "[ηl →S]"];
      [iMod (pobord_subdiv (TY:=xty) (M:=borrowM) (X:=X +ₓ Y)
        ᵖ[(_,_,cif_pointsto_ty U _ _)'] (λ _ '(y,_)', inr y) [] with "o ηl")
        as ([ζ[]]) "/=(ηl & #obs & big)"=>/=;
        [by move=> ??[?[]][?[]]/=[<-]|by move=> [??]|]|
       iMod (pobord_subdiv (TY:=xty) (M:=borrowM) (X:=X +ₓ Y)
        ᵖ[(_,_,cif_pointsto_ty T _ _)'] (λ _ '(x,_)', inl x) [] with "o ηl")
        as ([ζ[]]) "/=(ηl & #obs & big)"=>/=;
        [by move=> ??[?[]][?[]]/=[<-]|by move=> [??]|]];
      iMod ("→S" with "ηl") as "[$ S]";
      [iMod ("big" with "[] [$S $↦S] [//] [↦ ↦r]") as "(α & [b _] & _)";
        [by iApply lft_sincl_refl|..];
        [iIntros ([?[]]) "_ [(% & % & ↦S & S) _] _ !>";
          iExists _, (_ :: _ ++ _);
          rewrite heap_pointsto_vec_cons heap_pointsto_vec_app; iFrame "↦ ↦S";
          iDestruct (ty_own_size with "S") as %->; iFrame "↦r"; iExists _, _, _;
          iSplit; [done|]=>/=; by iFrame "S"|]|
       iMod ("big" with "[] [$S $↦S] [//] [↦ ↦r]") as "(α & [b _] & _)";
        [by iApply lft_sincl_refl|..];
        [iIntros ([?[]]) "_ [(% & % & ↦S & S) _] _ !>";
          iExists _, (_ :: _ ++ _);
          rewrite heap_pointsto_vec_cons heap_pointsto_vec_app; iFrame "↦ ↦S";
          iDestruct (ty_own_size with "S") as %->; iFrame "↦r"; iExists _, _, _;
          iSplit; [done|]=>/=; by iFrame "S"|]];
      iDestruct ("→κ" with "α") as "κ";
      ((iApply ("type'" with "κ t []") || iApply ("type" with "κ t []"));
        [iApply (proph_obs_impl2 with "obs pre")=> ?; rewrite eq eq'=> -> to;
          by apply to|]);
      iFrame "Γr"; iExists _, (S d'); rewrite -peq; (iSplit; [done|]);
      iExists _, _, _, _; rewrite sem_cif_in /= pbor_tok_pbor; iFrame "b";
      iPureIntro; do 2 split=>//; lia.
  Qed.
End sum_more.
