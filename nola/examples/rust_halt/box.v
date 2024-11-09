(** * Box pointer type *)

From nola.examples.rust_halt Require Export uninit ptr.

Implicit Type l : loc.

Section ty_box.
  Context `{!rust_haltGS CON Σ, !rust_haltC CON, !rust_haltJ CON JUDG Σ,
    !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ), !rust_haltCS CON JUDG Σ,
    !rust_haltJS CON JUDG Σ}.

  (** [ty_box]: Box pointer type *)
  Definition ty_box_def {X} (T : ty CON Σ X) : ty CON Σ X := pair 1
    (λ t d xπ vl, ∃ l d' xπ' wl, ⌜vl = [ #l]⌝ ∗ ⌜d' < d⌝ ∗ ⌜∀ π, xπ' π = xπ π⌝ ∗
        ▷ l ↦∗ wl ∗ ▷ †l…(length wl) ∗ cif_store (ty_own T t d' xπ' wl),
      λ t d l α xπ, ∃ l' d' xπ', ⌜d' < d⌝ ∗ ⌜∀ π, xπ' π = xπ π⌝ ∗
        ▷ l ↦ˢ[α] #l' ∗ □ cif_store (ty_shr T t d' l' α xπ'))%cif.
  Lemma ty_box_aux : seal (@ty_box_def). Proof. by eexists _. Qed.
  Definition ty_box {X} := ty_box_aux.(unseal) X.
  Lemma ty_box_unseal : @ty_box = @ty_box_def. Proof. exact: seal_eq. Qed.

  (** [ty_box] is productive *)
  #[export] Instance ty_box_productive {X} : Productive (@ty_box X).
  Proof.
    move=> ??? /ty_proeqv_later[eqvO eqvS]. rewrite ty_box_unseal /ty_box_def.
    apply ty_proeqv=>/=. split=>//. split=> >.
    - do 4 f_equiv=> ?. by rewrite eqvO.
    - do 3 f_equiv=> ?. by rewrite eqvS.
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
    { (do 8 f_equiv)=> ?. lia. } { (do 12 f_equiv)=> eq ?. by rewrite eq. }
    { (do 9 f_equiv)=> eq ?. by rewrite eq. }
  Qed.

  (** [ty_box] satisfies [TyOp] *)
  #[export] Instance ty_box_ty_op `(!Ty (X:=X) T, !TyOpLt T κ d) :
    TyOpAt (ty_box T) κ d.
  Proof.
    rewrite ty_box_unseal. split=>/= *.
    - iIntros "κ". iDestruct 1 as (???? -> ? eq) "(↦ & † & T)".
      rewrite sem_cif_in /=. iMod (stored_acc with "T") as "T".
      iMod (ty_own_proph_lt with "κ T") as (???) "[$ →T]"=>//. iModIntro.
      iSplit. { iPureIntro. by eapply proph_dep_proper. }
      iIntros "ξl". iMod ("→T" with "ξl") as "[$ T]".
      iMod (store_alloc with "T") as "T". iModIntro. iFrame "↦ †".
      iExists _, _. do 3 iSplit=>//. by rewrite sem_cif_in.
    - iIntros "κα". iDestruct 1 as (???? eq) "[↦ #T]". rewrite sem_cif_in /=.
      iMod (stored_acc with "T") as "{T}T".
      iMod (ty_shr_proph_lt with "κα T") as (???) "[$ →T]"=>//. iModIntro.
      iSplit. { iPureIntro. by eapply proph_dep_proper. }
      iIntros "ξl". iMod ("→T" with "ξl") as "[$ T]".
      iMod (store_alloc_pers with "T") as "T". iModIntro. iFrame "↦".
      iExists _, _. do 2 iSplit=>//. by rewrite sem_cif_in.
    - iIntros "[κ α] b".
      iMod (bord_open (M:=borrowM) with "α b") as "/=[o (% & ↦ & big)]".
      iDestruct "big" as (???? -> ? eq) "(↦' & † & T)". rewrite sem_cif_in /=.
      iMod (stored_acc with "T") as "T".
      iDestruct (ty_own_size with "T") as %->.
      rewrite heap_pointsto_vec_singleton.
      iMod (obord_subdiv (FML:=cifOF _) (M:=borrowM)
        [▷ _ ↦ _; ∃ wl, ▷ _ ↦∗ wl ∗ ty_own T _ _ _ wl]%cif
        with "[] o [$↦ $↦' $T //] [†]") as "(α & _ & b & b' & _)"=>/=.
      { iApply lft_sincl_refl. }
      { iIntros "_ (↦ & (% & $ & T) & _)". rewrite -heap_pointsto_vec_singleton.
        iDestruct (ty_own_size with "T") as %->.
        iMod (store_alloc with "T") as "T". iModIntro. iFrame "↦ †".
        iExists _, _. do 3 iSplit=>//. by rewrite sem_cif_in. }
      iMod (spointsto_alloc with "α b") as "[α $]". rewrite bor_tok_bor.
      iMod (ty_share_lt (T:=T) with "[$κ $α //] b'") as "[$ T]"=>//.
      iMod (store_alloc_pers with "T") as "T". iModIntro. iExists _, _.
      do 2 iSplit=>//. by rewrite sem_cif_in /=.
  Qed.

  (** [ty_box] preserves [Send] *)
  #[export] Instance ty_box_send `{!Send (X:=X) T} : Send (ty_box T).
  Proof.
    rewrite ty_box_unseal=> > /=. do 4 f_equiv=> ?. do 6 f_equiv. apply: send.
  Qed.
  (** [ty_box] preserves [Sync] *)
  #[export] Instance ty_box_sync `{!Sync (X:=X) T} : Sync (ty_box T).
  Proof.
    rewrite ty_box_unseal=> > /=. do 3 f_equiv=> ?. do 5 f_equiv. apply: sync.
  Qed.

  (** Subtyping over [ty_box] *)
  Lemma subty_box `{!Deriv ih δ} {X Y T U f} :
    □ (∀ δ', ⌜Deriv ih δ'⌝ -∗ ⌜ih δ'⌝ -∗ subty (X:=X) (Y:=Y) δ' T U f) ⊢
      subty δ (ty_box T) (ty_box U) f.
  Proof.
    rewrite subty_unseal ty_box_unseal. iIntros "#tosub". iSplit; iModIntro=>/=.
    - iIntros (????) "(% & % & %xπ' & % & % & % & %eq & $ & $ & T)".
      iExists _, (f ∘ xπ'). rewrite !sem_cif_in /=.
      iDestruct (store_wand with "[] T") as "$"; last first.
      { iPureIntro. (do 2 split=>//)=> ?. by rewrite eq. }
      iIntros (????) "? !>". by iApply ("tosub" with "[//] [//]").
    - iIntros (?????) "(% & % & %xπ' & % & %eq & $ & #T)". iExists _, (f ∘ xπ').
      rewrite !sem_cif_in /=.
      iDestruct (store_wand with "[] T") as "$"; last first.
      { iPureIntro. (split=>//)=> ?. by rewrite eq. }
      iIntros (????) "? !>". by iApply ("tosub" with "[//] [//]").
  Qed.

  (** Resolution over [ty_box] *)
  #[export] Instance resol_box `(!ResolLt (X:=X) T κ post d) :
    ResolAt (ty_box T) κ post d.
  Proof.
    split=> >. rewrite ty_box_unseal /=. iIntros "κ".
    iDestruct 1 as (?????? eq) "(_ & _ & T)". rewrite sem_cif_in /=.
    iMod (stored_acc with "T") as "T". setoid_rewrite <-eq.
    by iApply (resol_lt with "κ T").
  Qed.

  (** Read from [ty_box] *)
  #[export] Instance read_box `{!Ty (X:=X) T} {κ d} :
    Read κ (S d) (ty_box T) d T (ty_box (ty_uninit (ty_size T))) id (λ _, ())
    | 20.
  Proof.
    split=> ? t ??. iIntros "$ $". rewrite ty_box_unseal /=.
    iDestruct 1 as (????[= ->]??) "(>$ & >† & T)". rewrite sem_cif_in /=.
    iMod (stored_acc with "T") as "T". iDestruct (ty_own_size with "T") as %?.
    iDestruct (ty_own_depth (d':=d) with "T") as "T"; [lia|].
    iDestruct (ty_own_clair with "T") as "$"=>//.
    iMod (store_alloc (sty_own (sty_pty (pty_uninit _)) t 0 _ _) with "[]")
      as "u"=>/=; [by iExists ()|].
    iModIntro. iSplit=>//. iIntros "$ !>". iFrame "†". iExists _, _.
    rewrite sem_cif_in /=. by iFrame.
  Qed.
  (** Reading a copyable object from [ty_box] *)
  #[export] Instance read_box_copy `{!Ty (X:=X) T, !Copy T} {κ d} :
    Read κ (S d) (ty_box T) d T (ty_box T) id id.
  Proof.
    split=> >. iIntros "$ $". rewrite ty_box_unseal /=.
    iDestruct 1 as (????[= ->]??) "(>$ & >† & T)". rewrite sem_cif_in /=.
    iMod (stored_acc with "T") as "#T". iDestruct (ty_own_size with "T") as %?.
    iDestruct (ty_own_depth (d':=d) with "T") as "T'"; [lia|].
    iDestruct (ty_own_clair with "T'") as "$"=>//.
    iMod (store_alloc with "T") as "{T}T". iModIntro. iSplit=>//.
    iIntros "↦ !>". iFrame "↦ †". iExists _, _. rewrite sem_cif_in /=.
    by iFrame.
  Qed.

  (** Write to [ty_box] *)
  #[export] Instance write_box `{!Ty (X:=X) T, !Ty (X:=Y) U} {κ d d'} :
    TCEq (ty_size T) (ty_size U) →
    Write κ (S d) (ty_box T) d T d' U (S d') (ty_box U) id (λ _, id).
  Proof.
    move=> eq. split=> >. iIntros "$". rewrite ty_box_unseal /=.
    iDestruct 1 as (????[= ->]??) "(>$ & >† & T)". rewrite sem_cif_in /=.
    iMod (stored_acc with "T") as "T". iDestruct (ty_own_size with "T") as %->.
    iDestruct (ty_own_depth (d':=d) with "T") as "T"; [lia|].
    iDestruct (ty_own_clair with "T") as "$"=>//. iModIntro. iSplit=>//.
    iIntros (??) "↦ U". iFrame "↦". iDestruct (ty_own_size with "U") as %->.
    iMod (store_alloc with "U") as "U". iModIntro. rewrite eq. iFrame "†".
    iExists _, _. rewrite sem_cif_in /=. iFrame "U". iPureIntro. do 2 split=>//.
    lia.
  Qed.

  (** The depth of [ty_box] is positive *)
  Lemma type_box_depth v
    `(!EtcxExtract (Yl:=Yl) (Zl:=Zl) (v ◁{d} @ty_box X T) Γi Γr get getr)
    {Zl' κ e Γo pre} :
    (⌜d > 0⌝ → type (Yl:=Zl') κ (v ◁{d} ty_box T ᵖ:: Γr) e Γo pre) ⊢
      type κ Γi e Γo (λ post xl, pre post (get xl, getr xl)').
  Proof.
    rewrite type_unseal. iIntros "#type !>/=" (????) "κ t pre".
    rewrite etcx_extract ty_box_unseal /=. iIntros "[boxT Γr]".
    iDestruct "boxT" as (??????) "big".
    iApply ("type" with "[%] κ t pre [big $Γr]"); [lia|]=>/=. by iFrame.
  Qed.
End ty_box.
