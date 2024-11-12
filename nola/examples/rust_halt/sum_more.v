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
    iDestruct (lft_incl'_live_acc (α:=α) with "κ") as (?) "[α →κ]".
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
End sum_more.
