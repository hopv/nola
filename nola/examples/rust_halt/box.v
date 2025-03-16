(** * Box pointer type *)

From nola.examples.rust_halt Require Export uninit ptr.

Implicit Type (l : loc) (sz : nat).

Section ty_box.
  Context `{!rust_haltGS CON Σ, !rust_haltC CON, !rust_haltJ CON JUDG Σ,
    !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ), !rust_haltCS CON JUDG Σ,
    !rust_haltJS CON JUDG Σ}.

  (** [ty_box]: Box pointer type *)
  Definition ty'_box_def {X} (T : ty CON Σ X) : ty' CON Σ X :=
    (λ t d xπ vl, ∃ l d' xπ' wl, ⌜vl = [ #l]⌝ ∧ ⌜d' < d⌝ ∧ ⌜∀ π, xπ' π = xπ π⌝ ∧
        ▷ l ↦∗ wl ∗ ▷ †l…(length wl) ∗ cif_store (ty_own T t d' xπ' wl),
      λ t d l α xπ, ∃ l' d' α' xπ', ⌜d' < d⌝ ∧ ⌜∀ π, xπ' π = xπ π⌝ ∧
        ▷ (α ⊑□ α') ∗ ▷ l ↦ˢ[α] #l' ∗
        □ cif_store (ty_shr T t d' l' α' xπ'))%cif.
  Lemma ty'_box_aux : seal (@ty'_box_def). Proof. by eexists. Qed.
  Definition ty'_box {X} := ty'_box_aux.(unseal) X.
  Lemma ty'_box_unseal : @ty'_box = @ty'_box_def. Proof. exact: seal_eq. Qed.
  Definition ty_box {X} (T : ty CON Σ X) : ty CON Σ X := (1, ty'_box T).
  Lemma ty_box_unseal : @ty_box = λ _ T, (1, ty'_box_def T).
  Proof. by rewrite /ty_box ty'_box_unseal. Qed.

  (** [ty_box] is productive *)
  #[export] Instance ty_box_productive {X} : Productive (@ty_box X).
  Proof.
    rewrite ty_box_unseal=> ??? /ty_proeqv_later[eqvO eqvS].
    apply ty_proeqv=>/=. split=>//. split=> >.
    - do 4 f_equiv=> ?. by rewrite eqvO.
    - do 4 f_equiv=> ?. by rewrite eqvS.
  Qed.
  #[export] Instance ty_box_proper {X} : Proper ((≡) ==> (≡)) (@ty_box X).
  Proof. apply productive_proper, _. Qed.
  #[export] Instance ty_box_map_productive `(!Preserv' PR (ty _ _ X) F) :
    Productive (λ T, ty_box (F T)).
  Proof. move=> k ???. f_equiv. destruct k=>//=. by f_equiv. Qed.
  #[export] Instance ty_box_map_preserv `(!Preserv' PR (ty _ _ X) F) :
    Preserv (λ T, ty_box (F T)).
  Proof. apply productive_preserv, _. Qed.

  (** [ty_box] satisfies [Ty] *)
  #[export] Instance ty_box_ty {X T} : Ty (@ty_box X T).
  Proof.
    rewrite ty_box_unseal. split=>/= *. { exact _. }
    { by iDestruct 1 as (???? ->) "_". } { (do 11 f_equiv)=> ?. lia. }
    { (do 10 f_equiv)=> ?. lia. } { (do 12 f_equiv)=> eq ?. by rewrite eq. }
    { (do 11 f_equiv)=> eq ?. by rewrite eq. }
    iIntros "#⊑". iDestruct 1 as (??????) "(#? & #↦ & $)". do 2 iSplit=>//.
    iSplit; iNext; by [iApply lft_sincl_trans|iApply fbor_tok_lft].
  Qed.

  (** [ty_box] satisfies [TyOp] *)
  #[export] Instance ty_box_ty_op `(!Ty (X:=X) T, !TyOpLe T κ 1 d) :
    TyOpAt (ty_box T) κ d.
  Proof.
    rewrite ty_box_unseal. split=>/= *.
    - iIntros "κ". iDestruct 1 as (???? -> ? eq) "(↦ & † & T)".
      rewrite sem_cif_in /=. iMod (stored_acc with "T") as "T".
      iMod (ty_own_proph_le with "κ T") as (???) "[$ →T]"=>//. iModIntro.
      iSplit. { iPureIntro. by eapply proph_dep_proper. }
      iIntros "ξl". iMod ("→T" with "ξl") as "[$ T]".
      iMod (store_alloc with "T") as "T". iModIntro. iFrame "↦ †".
      iExists _, _. do 3 iSplit=>//. by rewrite sem_cif_in.
    - iIntros "κα". iDestruct 1 as (????? eq) "(>#⊑ & >#↦ & T)".
      rewrite sem_cif_in /=. iMod (stored_acc with "T") as "T".
      iMod (lft_sincl_live_acc with "[] κα") as (?) "[κα' →κα]";
        [by iApply lft_sincl_meet_mono_r|].
      iMod (ty_shr_proph_le with "κα' T") as (???) "[$ →κα']"=>//. iModIntro.
      iSplit. { iPureIntro. by eapply proph_dep_proper. }
      iIntros "ξl". iMod ("→κα'" with "ξl") as "κα'". iApply ("→κα" with "κα'").
    - iIntros "[κ α] b".
      iMod (bord_open (M:=borrowM) with "α b") as "/=[o (% & ↦ & big)]".
      iDestruct "big" as (???? -> ? eq) "(↦' & † & T)". rewrite sem_cif_in /=.
      iMod (stored_acc with "T") as "T".
      iDestruct (ty_own_size with "T") as %->.
      rewrite heap_pointsto_vec_singleton.
      iMod (obord_subdiv (FML:=cifOF _) (M:=borrowM)
        [▷ _ ↦ _; cif_pointsto_ty _ _ _ _ _]%cif
        with "[] o [$↦ $↦' $T //] [†]") as "(α & _ & b & b' & _)"=>/=.
      { iApply lft_sincl_refl. }
      { iIntros "_ (↦ & (% & $ & T) & _)". rewrite -heap_pointsto_vec_singleton.
        iDestruct (ty_own_size with "T") as %->.
        iMod (store_alloc with "T") as "T". iModIntro. iFrame "↦ †".
        iExists _, _. do 3 iSplit=>//. by rewrite sem_cif_in. }
      iMod (spointsto_alloc with "α b") as "[α $]". rewrite bor_tok_bor.
      iMod (ty_share_le (T:=T) with "[$κ $α //] b'") as "[$ T]"=>//.
      iMod (store_alloc_pers with "T") as "T". iModIntro. iExists _, _, _.
      do 2 iSplit=>//. iSplit; [|by rewrite sem_cif_in /=]. iNext.
      iApply lft_sincl_refl.
  Qed.

  (** [ty_box] preserves [Send] *)
  #[export] Instance ty_box_send `{!Send (X:=X) T} : Send (ty_box T).
  Proof.
    rewrite ty_box_unseal=> > /=. do 4 f_equiv=> ?. do 6 f_equiv. apply: send.
  Qed.
  (** [ty_box] preserves [Sync] *)
  #[export] Instance ty_box_sync `{!Sync (X:=X) T} : Sync (ty_box T).
  Proof.
    rewrite ty_box_unseal=> > /=. do 4 f_equiv=> ?. do 6 f_equiv.
    apply: sync.
  Qed.

  (** Resolution over [ty_box] *)
  #[export] Instance resol_box `(!ResolLe (X:=X) T κ post 1 d) :
    ResolAt (ty_box T) κ post d.
  Proof.
    split=> >. rewrite ty_box_unseal /=. iIntros "κ t".
    iDestruct 1 as (?????? eq) "(_ & _ & T)". rewrite sem_cif_in /=.
    iMod (stored_acc with "T") as "T". setoid_rewrite <-eq.
    by iApply (resol_le with "κ t T").
  Qed.

  (** Real part of [ty_box] *)
  #[export] Instance real_box `(!RealLe (X:=X) (A:=A) T κ get 1 d) :
    RealAt (ty_box T) κ get d.
  Proof.
    rewrite ty_box_unseal; split=>/= >; iIntros "κ t".
    - iDestruct 1 as (????) "($ & % & %eq & $ & $ & T)". rewrite sem_cif_in /=.
      iMod (stored_acc with "T") as "T".
      iMod (real_own_le with "κ t T") as ([? eq']) "($ & $ & T)"=>//.
      iMod (store_alloc with "T") as "T". iModIntro. iSplit.
      { iPureIntro. eexists _=> ?. by rewrite -eq. }
      iExists _, _. rewrite sem_cif_in /=. by iFrame.
    - iDestruct 1 as (????? eq) "(_ & _ & T)". rewrite sem_cif_in /=.
      iMod (stored_acc with "T") as "T".
      iMod (real_shr_le with "κ t T") as ([? eq']) "[$$]"=>//.
      iPureIntro. eexists _=> ?. by rewrite -eq.
  Qed.

  (** Subtyping over [ty_box] *)
  Lemma subty_box `{!Deriv ih δ} {X Y T U f} :
    □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → subty (X:=X) (Y:=Y) δ' T U f) ⊢
      subty δ (ty_box T) (ty_box U) f.
  Proof.
    rewrite subty_unseal ty_box_unseal /=. iIntros "#tosub". iSplit=>//.
    iSplit; iModIntro=>/=.
    - iIntros (????) "(% & % & %xπ' & % & % & % & %eq & $ & $ & T)".
      iExists _, (f ∘ xπ'). rewrite !sem_cif_in /=.
      iDestruct (store_wand with "[] T") as "$"; last first.
      { iPureIntro. (do 2 split=>//)=> ?. by rewrite eq. }
      iIntros (????) "? !>".
      iDestruct ("tosub" with "[//] [//]") as (_) "[sub _]". by iApply "sub".
    - iIntros (?????) "(% & % & % & %xπ' & % & %eq & $ & $ & #T)".
      iExists _, (f ∘ xπ'). rewrite !sem_cif_in /=.
      iDestruct (store_wand with "[] T") as "$"; last first.
      { iPureIntro. (split=>//)=> ?. by rewrite eq. }
      iIntros (????) "? !>".
      iDestruct ("tosub" with "[//] [//]") as (_) "[_ sub]". by iApply "sub".
  Qed.

  (** Read from [ty_box] *)
  #[export] Instance read_box `{!Ty (X:=X) T} {κ} :
    Read κ (ty_box T) T (ty_box (ty_uninit (ty_size T))) id (λ _, ())
    | 20.
  Proof.
    rewrite ty_box_unseal /ty_uninit ty_pty_unseal /=. split=>/= ? t >.
    iIntros "$$". iDestruct 1 as (????[=->]??) "(>$ & >† & T)".
    rewrite sem_cif_in /=. iMod (stored_acc with "T") as "T".
    iDestruct (ty_own_size with "T") as %?.
    iDestruct (ty_own_clair with "T") as "$"=>//. iModIntro. iSplit=>//.
    iIntros "$ !>". iFrame "†". iExists _, _, _. do 3 iSplit=>//.
    rewrite sem_cif_in /=. iApply store_acsr_store. iIntros (????) "!>/=".
    by iExists _.
  Qed.
  (** Reading a copyable object from [ty_box] *)
  #[export] Instance read_box_copy `{!Ty (X:=X) T, !Copy T} {κ} :
    Read κ (ty_box T) T (ty_box T) id id.
  Proof.
    split=> >. iIntros "$$". rewrite ty_box_unseal /=.
    iDestruct 1 as (????[=->]??) "(>$ & >† & T)". rewrite sem_cif_in /=.
    iMod (stored_acc with "T") as "#T". iDestruct (ty_own_size with "T") as %?.
    iDestruct (ty_own_clair with "T") as "$"=>//.
    iMod (store_alloc with "T") as "{T}T". iModIntro. iSplit=>//.
    iIntros "↦ !>". iFrame "↦ †". iExists _, _, _. rewrite sem_cif_in /=.
    by iFrame.
  Qed.

  (** Write to [ty_box] *)
  #[export] Instance write_box `{!Ty (X:=X) T, !Ty (X:=Y) U} {κ} :
    TCEq (ty_size T) (ty_size U) →
    Write κ (ty_box T) T U (ty_box U) id (λ _, id).
  Proof.
    move=> eq. split=> >. iIntros "$". rewrite ty_box_unseal /=.
    iDestruct 1 as (????[=->]??) "(>$ & >† & T)". rewrite sem_cif_in /=.
    iMod (stored_acc with "T") as "T". iDestruct (ty_own_size with "T") as %->.
    iDestruct (ty_own_clair with "T") as "$"=>//. iModIntro. iSplit=>//.
    iIntros (? du ?) "↦ U". iFrame "↦". iDestruct (ty_own_size with "U") as %->.
    iMod (store_alloc with "U") as "U". iModIntro. rewrite eq. iFrame "†".
    iExists (S du), _, _. rewrite sem_cif_in /=. iFrame "U". iPureIntro.
    do 2 split=>//. lia.
  Qed.

  (** Allocate [ty_box] *)
  Lemma type_alloc {Xl Γ κ sz} :
    sz > 0 →
    ⊢ type (Xl:=Xl) κ Γ (Alloc #sz) (λ r, r ◁ ty_box (ty_uninit sz) ᵖ:: Γ)
        (λ post xl, post ((), xl)').
  Proof.
    rewrite type_unseal ty_box_unseal /ty_uninit ty_pty_unseal=> ?.
    iIntros (????) "!>/= $ $ pre Γ". iApply twp_alloc=>//=; [lia|].
    iIntros (??) "(%eq & † & $) !>". rewrite repeat_length. iFrame "† pre Γ".
    iExists _, 1. iSplit=>//. iExists 0, _. iSplit=>//.
    iSplit; [iPureIntro; lia|]. iSplit=>//. rewrite sem_cif_in /=.
    iApply store_acsr_store. iIntros (????) "!>/= !%". eexists _. split=>//.
    lia.
  Qed.

  (** Free [ty_box] *)
  Lemma type_free p
    `(!EtcxExtract (X:=X) (Yl:=Yl) (Zl:=Zl) (p ◁ ty_box T) Γ Γr get getr,
      !Ty T, !Resol T κ postr) {sz} :
    ty_size T = sz →
    ⊢ type κ Γ (Free #sz p) (λ _, Γr)
        (λ post yl, postr (get yl) → post (getr yl))%type.
  Proof.
    rewrite type_unseal=> <-. iIntros (????) "!>/= κ t pre".
    rewrite etcx_extract ty_box_unseal /=. iIntros "[big Γr]".
    iDestruct "big" as (???????[=->]? eq) "(>↦ & >† & T)". wp_path p.
    rewrite sem_cif_in /=. iMod (stored_acc with "T") as "T".
    iDestruct (ty_own_size with "T") as %leq. rewrite -leq.
    iMod (resol with "κ t T") as "($ & $ & obs)". wp_free. iModIntro.
    iFrame "Γr". iApply (proph_obs_impl2 with "pre obs")=> ?. by rewrite -eq.
  Qed.
End ty_box.
