(** * Mutable reference type *)

From nola.examples.rust_halt Require Export ptr.

Implicit Type l : loc.

Section ty_mutref.
  Context `{!rust_haltGS CON Σ, !rust_haltC CON, !rust_haltJ CON JUDG Σ,
    !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ), !rust_haltCS CON JUDG Σ,
    !rust_haltJS CON JUDG Σ}.

  (** [ty_mutref]: Mutable reference type *)
  Definition ty'_mutref_def {X} (α : lft) (T : ty CON Σ X)
    : ty' CON Σ (X *'ₓ X) :=
    (λ t d (pπ : clair (X *' X)) vl, ∃ l d' (ξ : prvar X) xπ, ⌜vl = [ #l]⌝ ∧
      ⌜d' < d⌝ ∧ ⌜∀ π, pπ π = (xπ π, π ξ)'⌝ ∧
      cif_pbor α d' xπ ξ (cif_pointsto_ty T l t),
      λ t d l β (pπ : clair (X *' X)), ∃ l' d' (ξ : prvar X) β' xπ, ⌜d' < d⌝ ∧
        ⌜∀ π, pπ π = (xπ π, π ξ)'⌝ ∧
        ▷ (β ⊑□ β') ∗ ▷ l ↦ˢ[α ⊓ β] #l' ∗ ▷ [ξ]:ˢ[α ⊓ β] ∗
        □ cif_store (ty_shr T t d' l' (α ⊓ β') xπ))%cif.
  Lemma ty'_mutref_aux : seal (@ty'_mutref_def). Proof. by eexists. Qed.
  Definition ty'_mutref {X} := ty'_mutref_aux.(unseal) X.
  Lemma ty'_mutref_unseal : @ty'_mutref = @ty'_mutref_def.
  Proof. exact: seal_eq. Qed.
  Definition ty_mutref {X} (α : lft) (T : ty CON Σ X) : ty CON Σ (X *'ₓ X) :=
    (1, ty'_mutref α T).
  Lemma ty_mutref_unseal :
    @ty_mutref = λ _ α T, (1, ty'_mutref_def α T).
  Proof. by rewrite /ty_mutref ty'_mutref_unseal. Qed.

  (** [ty_mutref] is productive *)
  #[export] Instance ty_mutref_productive {X α} :
    Productive (@ty_mutref X α).
  Proof.
    rewrite ty_mutref_unseal=> k ?? /ty_proeqv_later[eqvO eqvS].
    apply ty_proeqv=>/=. split; [done|]. split=> >.
    - do 4 f_equiv=> ?. do 4 f_equiv. destruct k=>//= >. unfold cif_pointsto_ty.
      f_equiv=> ?. f_equiv. exact: eqvO.
    - do 5 f_equiv=> ?. do 7 f_equiv. exact: eqvS.
  Qed.
  #[export] Instance ty_mutref_proper {X α} :
    Proper ((≡) ==> (≡)) (@ty_mutref X α).
  Proof. apply productive_proper, _. Qed.
  #[export] Instance ty_mutref_map_productive `(!Preserv' PR (ty _ _ X) F) {α} :
    Productive (λ T, ty_mutref α (F T)).
  Proof. move=> k ???. f_equiv. destruct k=>//=. by f_equiv. Qed.
  #[export] Instance ty_mutref_map_preserv `(!Preserv' PR (ty _ _ X) F) {α} :
    Preserv (λ T, ty_mutref α (F T)).
  Proof. apply productive_preserv, _. Qed.

  (** [ty_mutref] satisfies [Ty] *)
  #[export] Instance ty_mutref_ty {X α T} : Ty (@ty_mutref X α T).
  Proof.
    rewrite ty_mutref_unseal. split=>/= *. { exact _. }
    { by iDestruct 1 as (???? ->) "?". }
    { (do 11 f_equiv)=> ?. lia. } { (do 12 f_equiv)=> ?. lia. }
    {(do 12 f_equiv)=> eq ?. by rewrite -eq. }
    { (do 13 f_equiv)=> eq ?. by rewrite -eq. }
    iIntros "#⊑". iDestruct 1 as (???????) "(#? & #? & #? & $)".
    iExists _. do 2 iSplit=>//. iSplit. { iNext. by iApply lft_sincl_trans. }
    iSplit; iNext; iApply fbor_tok_lft; by [iApply lft_sincl_meet_mono_r|].
  Qed.

  (** [ty_mutref] satisfies [TyOp] *)
  #[export] Instance ty_mutref_ty_op `{!Ty (X:=X) T}
    `(!TyOpLe T κ 1 d, !LftIncl κ α) :
    TyOpAt (ty_mutref α T) κ d.
  Proof.
    rewrite ty_mutref_unseal. split=>/=.
    - move=> >. iIntros "[κ κ']". iDestruct 1 as (? ξ ???? eq) "big".
      rewrite sem_cif_in /=.
      iDestruct (lft_incl'_live_acc α with "κ") as (?) "[α →κ]".
      iMod (pbord_open (M:=borrowM) with "α big") as "/=[o (% & ↦ & T)]".
      iDestruct (pobor_proph with "o") as "[ξ →o]". unfold cif_pointsto_ty.
      iMod (ty_own_proph_le with "κ' T") as (ηl ??) "[ηl →T]"=>//. iModIntro.
      iDestruct (proph_tok_toks_fuse with "ξ ηl") as (?) "[$ →ξηl]"=>/=. iSplit.
      { iPureIntro. eapply proph_dep_proper; [exact: eq|done|].
        apply: (proph_dep_f2 (λ x x', (x', x)') _ _ [_]); [|done].
        exact: proph_dep_prvar. }
      iIntros "ξηl". iDestruct ("→ξηl" with "ξηl") as "[ξ ηl]".
      iDestruct ("→o" with "ξ") as "o". iMod ("→T" with "ηl") as "[$ T]".
      iMod (pobord_close (M:=borrowM) with "o [↦ T]") as "[α b]"=>/=;
        [by iFrame|].
      iDestruct ("→κ" with "α") as "$". iModIntro. iExists _, _, _, _.
      do 3 (iSplit; [done|]). by rewrite pbor_tok_pbor sem_cif_in /=.
    - move=> ?? β ??. iIntros "[[κ κ'] [β β']]".
      iDestruct 1 as (?????? eq) "(>#⊑ & _ & >ξ & T)".
      iDestruct (lft_incl'_live_acc (κ:=κ ⊓ β) (α ⊓ β) with "[$κ $β]")
        as (?) "[αβ →κβ]".
      iMod (sproph_tok_acc with "αβ ξ") as (?) "[ξ →αβ]". rewrite sem_cif_in /=.
      iMod (stored_acc with "T") as "T".
      iDestruct (lft_incl'_live_acc (κ:=κ ⊓ β) (κ ⊓ (α ⊓ β)) with "[$κ' $β']")
        as (?) "[καβ →κβ']".
      iMod (lft_sincl_live_acc with "[] καβ") as (?) "[καβ' →καβ]";
        [iApply lft_sincl_meet_mono_r; by iApply lft_sincl_meet_mono_r|].
      iMod (ty_shr_proph_le (T:=T) with "καβ' T") as (ηl ??) "[ηl →καβ']"=>//.
      iModIntro. iDestruct (proph_tok_toks_fuse with "ξ ηl") as (?) "[$ →ξηl]".
      iSplit.
      { iPureIntro. eapply proph_dep_proper; [exact: eq|done|].
        apply: (proph_dep_f2 (λ x x', (x', x)') _ _ [_]); [|done].
        exact: proph_dep_prvar. }
      iIntros "ξηl". iDestruct ("→ξηl" with "ξηl") as "[ξ ηl]".
      iMod ("→αβ" with "ξ") as "αβ". iDestruct ("→κβ" with "αβ") as "$".
      iMod ("→καβ'" with "ηl") as "καβ'". iModIntro.
      iDestruct ("→καβ" with "καβ'") as "?". by iApply "→κβ'".
    - move=> ?? β ??. iIntros "[[κ κ'] [β β']] b".
      iMod (bord_open (M:=borrowM) with "β b") as "/=[o (% & ↦ & big)]".
      iDestruct "big" as (??? xπ  -> ? eq) "pb".
      rewrite heap_pointsto_vec_singleton sem_cif_in /=.
      iDestruct (lft_incl'_live_acc α with "κ") as (?) "[α →κ]".
      iMod (pbord_soft_reborrow (M:=borrowM) (α ⊓ β) with "[] α pb")
        as "(α & →pb & bξ & bT)"; [iApply lft_sincl_meet_l|].
      iDestruct ("→κ" with "α") as "$".
      iDestruct (lft_incl'_live_acc (κ:=κ ⊓ β) (α ⊓ β) with "[$κ' $β']")
        as (?) "[αβ →κβ]".
      iMod (sproph_tok_alloc with "αβ bξ") as "[αβ $]".
      iDestruct ("→κβ" with "αβ") as "κβ".
      iDestruct (lft_incl'_live_acc (κ ⊓ (α ⊓ β)) with "κβ") as (?) "[καβ →κβ]".
      iMod (ty_share_le (T:=T) with "καβ bT") as "[καβ #T]"=>//.
      iDestruct ("→κβ" with "καβ") as "[κ $]".
      iMod (obord_subdiv (FML:=cifOF _) (M:=borrowM) [▷ _ ↦ _]%cif (α ⊓ β)
        with "[] o [↦] [→pb]") as "(β & _ & ↦ & _)"=>/=.
      { iApply lft_sincl_meet_r. } { by iSplitL. }
      { iIntros "† [↦ _] !>". iExists [_]. rewrite heap_pointsto_vec_singleton.
        iFrame "↦". iExists _, _, _, _. rewrite sem_cif_in /=.
        by iDestruct ("→pb" with "†") as "$". }
      iDestruct (lft_incl'_live_acc (κ:=κ ⊓ β) (α ⊓ β) with "[$κ $β]")
        as (?) "[αβ →κβ]".
      iMod (spointsto_alloc with "αβ ↦") as "[αβ $]".
      iDestruct ("→κβ" with "αβ") as "[$$]". iExists _, _, _.
      rewrite sem_cif_in /=. iMod (store_alloc_pers with "T") as "$".
      iModIntro. do 2 iSplit=>//. iNext. iApply lft_sincl_refl.
  Qed.

  (** [ty_mutref] preserves [Send] *)
  #[export] Instance ty_mutref_send `{!Send (X:=X) T} {α} :
    Send (ty_mutref α T).
  Proof.
    rewrite ty_mutref_unseal /ty'_mutref_def=> > /=. do 4 f_equiv=> ?.
    unfold cif_pointsto_ty. (do 4 f_equiv)=> >. f_equiv=> ?. f_equiv.
    exact: send.
  Qed.
  (** [ty_mutref] preserves [Sync] *)
  #[export] Instance ty_mutref_sync `{!Sync (X:=X) T} {α} :
    Sync (ty_mutref α T).
  Proof.
    rewrite ty_mutref_unseal /ty'_mutref_def=> > /=. do 5 f_equiv=> ?.
    do 7 f_equiv. exact: sync.
  Qed.

  (** Resolution over [ty_mutref], setting the prophecy to the actual final
    value *)
  #[export] Instance resol_mutref {X} `(!LftIncl κ α, !TyOp T κ) :
    Resol (ty_mutref (X:=X) α T) κ (λ '(x, x')', x' = x).
  Proof.
    rewrite /= ty_mutref_unseal. split=>/= >. iIntros "[κ κ'] $".
    iDestruct 1 as (?????? eq) "b". rewrite sem_cif_in /=.
    iDestruct (lft_incl'_live_acc α with "κ") as (?) "[α →κ]".
    iMod (pbord_open (M:=borrowM) with "α b") as "/=[o (% & ↦ & T)]".
    iMod (ty_own_proph with "κ' T") as (ηl ??) "[ηl →T]".
    iMod (pobord_resolve (M:=borrowM) with "o ηl") as "/=(ηl & obs & →α)"=>//.
    iMod ("→T" with "ηl") as "[$ T]". iMod ("→α" with "[$↦ $T //]") as "[α _]".
    iDestruct ("→κ" with "α") as "$". iModIntro.
    iApply (proph_obs_impl with "obs")=> ?. by rewrite eq.
  Qed.

  (** Real part of [ty_mutref], discarding  *)
  #[export] Instance real_mutref
    `(!RealLe (X:=X) (A:=A) T κ get 1 d, !LftIncl κ α) :
    RealAt (ty_mutref α T) κ (get ∘ fst') d.
  Proof.
    rewrite ty_mutref_unseal. split=>/= >.
    - iIntros "[κ κ'] t". iDestruct 1 as (????) "($ & % & %eq & b)".
      rewrite sem_cif_in /=.
      iDestruct (lft_incl'_live_acc α with "κ") as (?) "[α →κ]".
      iMod (pbord_open (M:=borrowM) with "α b") as "/=[o (% & ↦ & T)]".
      iMod (real_own_le with "κ' t T") as ([? eq']) "($ & $ & T)"=>//.
      iMod (pobord_close (M:=borrowM) with "o [↦ T]") as "[α b]"=>/=;
        [by iFrame|].
      iModIntro. iSplit. { iPureIntro. eexists _=> ?. by rewrite eq /=. }
      iDestruct ("→κ" with "α") as "$". iExists _, _, _. rewrite sem_cif_in /=.
      rewrite pbor_tok_pbor. by iFrame.
    - iIntros "κ t". iDestruct 1 as (?????? eq) "(_ & _ & _ & T)".
      rewrite sem_cif_in /=. iMod (stored_acc with "T") as "T".
      iMod (real_shr_le with "κ t T") as ([? eq']) "[$$]"=>//. iPureIntro.
      eexists _=> ?. by rewrite eq /=.
  Qed.

  (** Modify the lifetime of [ty_mutref] *)
  Lemma subty_mutref_lft `{!Deriv ih δ, !Ty (X:=X) T} {β α} :
    β ⊑□ α ⊢ subty δ (ty_mutref α T) (ty_mutref β T) id.
  Proof.
    rewrite subty_unseal ty_mutref_unseal. iIntros "#⊑". iSplit; [done|].
    iSplit; iModIntro=>/=.
    - iIntros (????). iDestruct 1 as (????) "($ & $ & $ & ?)".
      rewrite !sem_cif_in /= /cif_pointsto_ty. by iApply pbor_lft.
    - iIntros (?????). iDestruct 1 as (???????) "($ & #↦ & #ξ & #T)".
      iExists _, _, _, _. do 2 iSplit=>//.
      iSplit; [|iSplit];
        [iNext; iApply fbor_tok_lft; by [iApply lft_sincl_meet_mono_l|]..|].
      iModIntro. rewrite !sem_cif_in /=. iApply (store_wand with "[] T").
      iIntros (????) "{T}T !>". iApply (ty_shr_lft with "[] T").
      by iApply lft_sincl_meet_mono_l.
  Qed.

  (** Subtyping over [ty_mutref] *)
  Lemma subty_mutref `{!Deriv ih δ} {X T U α} :
    □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ →
      subty (X:=X) δ' T U id ∧ subty δ' U T id) ⊢
      subty δ (ty_mutref α T) (ty_mutref α U) id.
  Proof.
    rewrite subty_unseal ty_mutref_unseal. iIntros "#→sub". iSplit; [done|].
    iSplit; iModIntro=>/=.
    - iIntros (????). iDestruct 1 as (????) "($ & $ & $ & b)".
      rewrite !sem_cif_in /= /cif_pointsto_ty.
      iApply (pbor_wand with "[] b"). iIntros "!>/=" (??????).
      iSplit; iIntros "(% & $ & S) !>";
        iDestruct ("→sub" with "[//] [//]") as "sub";
        [iDestruct "sub" as "[[_[sub _]] _]"|
          iDestruct "sub" as "[_ [_[sub _]]]"]; iApply ("sub" with "S").
    - iIntros (?????). iDestruct 1 as (?????) "($ & $ & $ & $ & $ & #T)".
      iModIntro. rewrite !sem_cif_in /=. iApply (store_wand with "[] T").
      iIntros (????) "{T}T !>".
      iDestruct ("→sub" with "[//] [//]") as "[[_[_ sub]] _]".
      iApply ("sub" with "T").
  Qed.

  (** Read a copyable object from [ty_mutref] *)
  Lemma read_mutref `{!Ty (X:=X) T, !Copy T, !LftIncl κ α} :
    Read κ (ty_mutref α T) T (ty_mutref α T) fst' id.
  Proof.
    rewrite ty_mutref_unseal. split=>/= >. iIntros "κ $".
    iDestruct 1 as (????[=->]? eq) "b". rewrite sem_cif_in /=.
    iDestruct (lft_incl'_live_acc α with "κ") as (?) "[α →κ]".
    iMod (pbord_open (M:=borrowM) with "α b") as "/=[o (% & >$ & #T)]".
    iDestruct (ty_own_clair with "T") as "$". { move=>/= ?. by rewrite eq. }
    iModIntro. iSplit; [done|]. iIntros "↦".
    iMod (pobord_close (M:=borrowM) with "o [↦]") as "[α b]"=>/=; [by iFrame|].
    rewrite pbor_tok_pbor. iDestruct ("→κ" with "α") as "$". iModIntro.
    iExists _, _, _, _, _. rewrite sem_cif_in /=. iFrame "b"=>/=. iPureIntro.
    split=>//. split=>// ?. by rewrite eq.
  Qed.

  (** Write to [ty_mutref], updating the current value and keeping the prophecy
    the same *)
  #[export] Instance write_mutref `{!Ty (X:=X) T, !LftIncl κ α} :
    Write κ (ty_mutref α T) T T (ty_mutref α T) fst' (λ '(_, x')' x, (x, x')').
  Proof.
    rewrite ty_mutref_unseal. split=>/= >. iIntros "κ".
    iDestruct 1 as (????[=->]? eq) "b". rewrite sem_cif_in /=.
    iDestruct (lft_incl'_live_acc α with "κ") as (?) "[α →κ]".
    iMod (pbord_open (M:=borrowM) with "α b") as "/=[o (% & >$ & T)]".
    iDestruct (ty_own_clair with "T") as "$". { move=>/= ?. by rewrite eq. }
    iModIntro. iSplit; [done|]. iIntros (? du' ?) "↦ T".
    iMod (pobord_close (M:=borrowM) with "o [↦ T]") as "[α b]"=>/=;
      [by iFrame|].
    rewrite pbor_tok_pbor. iDestruct ("→κ" with "α") as "$". iModIntro.
    iExists (S du'), _, _, _, _. rewrite sem_cif_in /=. iFrame "b". iPureIntro.
    split=>//. split; [lia|]=> ?. by rewrite eq.
  Qed.
End ty_mutref.
