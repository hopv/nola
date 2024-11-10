(** * Product type *)

From nola.examples.rust_halt Require Export type uninit.

Section ty_prod.
  Context `{!Csem CON JUDG Σ, !Jsem JUDG (iProp Σ), !rust_haltGS CON Σ,
    !rust_haltC CON, !rust_haltJ CON JUDG Σ, !rust_haltJS CON JUDG Σ}.

  (** [ty_prod]: Product type *)
  Definition ty'_prod_def {X Y} (T : ty CON Σ X) (U : ty CON Σ Y)
    : ty' CON Σ (X *'ₓ Y) :=
    (λ t d xyπ vl, ∃ wl wl', ⌜vl = wl ++ wl'⌝ ∧
      ty_own T t d (fst' ∘ xyπ) wl ∗ ty_own U t d (snd' ∘ xyπ) wl',
      λ t d l α xyπ, ty_shr T t d l α (fst' ∘ xyπ) ∗
        ty_shr U t d (l +ₗ ty_size T) α (snd' ∘ xyπ))%cif.
  Lemma ty'_prod_aux : seal (@ty'_prod_def). Proof. by eexists. Qed.
  Definition ty'_prod {X Y} := ty'_prod_aux.(unseal) X Y.
  Lemma ty'_prod_unseal : @ty'_prod = @ty'_prod_def. Proof. exact: seal_eq. Qed.
  Definition ty_prod {X Y} (T : ty CON Σ X) (U : ty CON Σ Y)
    : ty CON Σ (X *'ₓ Y) := (ty_size T + ty_size U, ty'_prod T U).
  Lemma ty_prod_unseal :
    @ty_prod = λ _ _ T U, (ty_size T + ty_size U, ty'_prod_def T U).
  Proof. by rewrite /ty_prod ty'_prod_unseal. Qed.

  (** [ty_prod] is size-preserving *)
  #[export] Instance ty_prod_preserv {X Y k} :
    Proper ((≡[k]≡) ==> (≡[k]≡) ==> (≡[k]≡)) (@ty_prod X Y).
  Proof.
    move=> ?? /ty_proeqv[eqZ[eqvO eqvS]]?? /ty_proeqv[eqZ'[eqvO' eqvS']].
    rewrite ty_prod_unseal. apply ty_proeqv=>/=. split; [by rewrite eqZ eqZ'|].
    rewrite eqZ. split=> >; [do 2 f_equiv=> ?; f_equiv|]; f_equiv;
      [exact: eqvO|exact: eqvO'|exact: eqvS|exact: eqvS'].
  Qed.
  #[export] Instance ty_prod_proper {X Y} :
    Proper ((≡) ==> (≡) ==> (≡)) (@ty_prod X Y).
  Proof.
    move=> ?*?*. apply equiv_proeqv=> ?. f_equiv; by apply equiv_proeqv.
  Qed.
  #[export] Instance ty_prod_map_preserv {X Y} `(!Preserv' PR _ F, !Preserv G) :
    Preserv (λ T, @ty_prod X Y (F T) (G T)).
  Proof. move=> ?*?*. by do 2 f_equiv. Qed.
  #[export] Instance ty_prod_map_productive {X Y}
    `(ProductiveF : !Productive' PR _ F, ProductiveG : !Productive G) :
    Productive (λ T, @ty_prod X Y (F T) (G T)).
  Proof. move=> ?*?*. f_equiv; by [apply: ProductiveF|apply: ProductiveG]. Qed.

  (** [ty_prod] preserves [Ty] *)
  #[export] Instance ty_prod_ty `{!Ty (X:=X) T, !Ty (X:=Y) U} :
    Ty (ty_prod T U).
  Proof.
    rewrite ty_prod_unseal. split=>/= >.
    - apply bi.sep_persistent; exact: ty_shr_persistent.
    - iDestruct 1 as (?? ->) "[T U]". rewrite !ty_own_size length_app.
      iDestruct "T" as %->. by iDestruct "U" as %->.
    - move=> ?. do 6 f_equiv; exact: ty_own_depth.
    - move=> ?. f_equiv; exact: ty_shr_depth.
    - move=> eq. do 6 f_equiv; apply: ty_own_clair=>/= ?; by rewrite eq.
    - move=> eq. f_equiv; apply: ty_shr_clair=>/= ?; by rewrite eq.
  Qed.

  (** [ty_prod] preserves [TyOpAt] *)
  #[export] Instance ty_prod_ty_op `{!Ty (X:=X) T}
    `(!TyOpAt T κ d, !TyOpAt (X:=Y) U κ d) :
    TyOpAt (ty_prod T U) κ d.
  Proof.
    rewrite ty_prod_unseal. split=>/=.
    - iIntros (? xπ ??) "[κ κ']". iDestruct 1 as (??->) "[T U]".
      iMod (ty_own_proph with "κ T") as (ξl r ?) "[ξl →T]".
      iMod (ty_own_proph with "κ' U") as (ηl r' ?) "[ηl →U]". iModIntro.
      iExists (ξl ++ ηl). case: (Qp.lower_bound r r')=> ?[?[?[->->]]].
      iDestruct "ξl" as "[$ ξl']". iDestruct "ηl" as "[$ ηl']". iSplit.
      { iPureIntro. have -> : xπ = λ π, ((fst' ∘ xπ) π, (snd' ∘ xπ) π)' by done.
        by apply proph_dep_f2. }
      iIntros "[ξl ηl]". iMod ("→T" with "[$ξl $ξl']") as "[$ $]".
      by iMod ("→U" with "[$ηl $ηl']") as "[$ $]".
    - iIntros (??? xπ q) "[[κ κ'] [α α']] [T U]".
      iMod (ty_shr_proph (T:=T) with "[$κ $α //] T") as (ξl r ?) "[ξl →T]".
      iMod (ty_shr_proph (T:=U) with "[$κ' $α' //] U") as (ηl r' ?) "[ηl →U]".
      iModIntro. iExists (ξl ++ ηl). case: (Qp.lower_bound r r')=> ?[?[?[->->]]].
      iDestruct "ξl" as "[$ ξl']". iDestruct "ηl" as "[$ ηl']". iSplit.
      { iPureIntro. have -> : xπ = λ π, ((fst' ∘ xπ) π, (snd' ∘ xπ) π)' by done.
        by apply proph_dep_f2. }
      iIntros "[ξl ηl]". iMod ("→T" with "[$ξl $ξl']") as "[$ $]".
      by iMod ("→U" with "[$ηl $ηl']") as "[$ $]".
    - iIntros (?????) "[κ α] b".
      iMod (bord_open (M:=borrowM) with "α b")
        as "/=[o (% & ↦ & % & % & -> & T & U)]".
      iDestruct (ty_own_size with "T") as %eq. rewrite heap_pointsto_vec_app.
      iDestruct "↦" as "[↦ ↦']". rewrite eq.
      iMod (obord_subdiv (M:=borrowM)
        [cif_pointsto_ty T _ _ _ _; cif_pointsto_ty U _ _ _ _]
        with "[] o [↦ ↦' T U] []") as "(α & _ & b & b' & _)"=>/=.
      { iApply lft_sincl_refl. } { iFrame. }
      { iIntros "_ ((% & ↦ & T) & (% & ↦' & $) & _) !>".
        iDestruct (ty_own_size with "T") as %eq'. iFrame "T". iExists _.
        iSplit; [|done]. rewrite heap_pointsto_vec_app eq'. iFrame. }
      rewrite !bor_tok_bor.
      iMod (ty_share (T:=T) with "[$κ $α //] b") as "[κα $]".
      iApply (ty_share (T:=U) with "κα b'").
  Qed.

  (** [ty_prod] preserves [Send] *)
  #[export] Instance ty_prod_send `{!Send (X:=X) T, !Send (X:=Y) U} :
    Send (ty_prod T U).
  Proof.
    rewrite ty_prod_unseal. move=>/= >. do 2 f_equiv=> ?.
    do 2 f_equiv; exact: send.
  Qed.
  (** [ty_prod] preserves [Sync] *)
  #[export] Instance ty_prod_sync `{!Sync (X:=X) T, !Sync (X:=Y) U} :
    Sync (ty_prod T U).
  Proof. rewrite ty_prod_unseal. move=>/= >. f_equiv; exact: sync. Qed.
  (** [ty_prod] preserves [Copy] *)
  #[export] Instance ty_prod_copy `{!Ty (X:=X) T, !Copy T, !Copy (X:=Y) U} :
    Copy (ty_prod T U).
  Proof.
    rewrite ty_prod_unseal. split=>/= >; [exact _|].
    iIntros (sub) "[α α'] t [T U]".
    iMod (copy_shr_acc with "α t T") as (r ?) "(↦t & t & T & cl)".
    { etrans; [|done]. apply shr_locsE_mono=>/=. lia. }
    iDestruct (ty_own_size with "T") as %eq.
    iMod (copy_shr_acc with "α' t U") as (r' ?) "(↦u & t & U & cl')".
    { etrans; [|exact: difference_mono_r].
      rewrite -assoc (shr_locsE_add (sz:=T.1)).
      apply subseteq_difference_r; [|set_solver]. symmetry.
      exact shr_locsE_disj. }
    iModIntro. case: (Qp.lower_bound r r')=> ?[?[?[->->]]]. iExists _, (_ ++ _).
    rewrite heap_pointsto_vec_app. iDestruct "↦t" as "[$ ↦t']". rewrite eq.
    iDestruct "↦u" as "[$ ↦u']". rewrite shr_locsE_add.
    rewrite difference_difference_l_L. iFrame "t T U". iSplit; [done|].
    iIntros "[↦t ↦u] t". iCombine "↦t ↦t'" as "↦t". iCombine "↦u ↦u'" as "↦u".
    iMod ("cl'" with "↦u t") as "[$ t]". iApply ("cl" with "↦t t").
  Qed.

  (** Resolution over [ty_prod] *)
  #[export] Instance resol_prod
    `(!ResolAt (X:=X) T κ post d, !ResolAt (X:=Y) U κ post' d) :
    ResolAt (ty_prod T U) κ (λ '(x, y)', post x ∧ post' y) d.
  Proof.
    rewrite ty_prod_unseal. split=> > /=. iIntros "κ (% & % & -> & T & U)".
    iMod (resol with "κ T") as "[κ post]".
    iMod (resol with "κ U") as "[$ post']". by iCombine "post post'" as "$".
  Qed.

  (** Subtyping on [ty_prod] *)
  Lemma subty_prod {δ X T X' T' f Y U Y' U' g} :
    subty (X:=X) (Y:=X') δ T T' f -∗ subty (X:=Y) (Y:=Y') δ U U' g -∗
      subty δ (ty_prod T U) (ty_prod T' U') (λ '(x, y)', (f x, g y)').
  Proof.
    rewrite ty_prod_unseal subty_unseal /=.
    iIntros "[%Tz[#To #Ts]][%Uz[#Uo #Us]]". rewrite Tz Uz. iSplit=>/=; [done|].
    iSplit; iModIntro.
    - iIntros (????). iDestruct 1 as (??) "($ & T & U)".
      iSplitL "T"; by [iApply "To"|iApply "Uo"].
    - iIntros (?????) "[T U]". rewrite Tz.
      iSplitL "T"; by [iApply "Ts"|iApply "Us"].
  Qed.

  (** Associativity of [ty_prod] *)
  Lemma subty_prod_assoc {δ X T Y T' Z T''} :
    ⊢ subty δ (@ty_prod X _ T (@ty_prod Y Z T' T''))
        (ty_prod (ty_prod T T') T'') (λ '(x, y, z)', ((x, y)', z)').
  Proof.
    rewrite ty_prod_unseal subty_unseal /=. iSplit=>/=; [iPureIntro; lia|].
    iSplit; iModIntro.
    - iIntros (????). iDestruct 1 as (??->) "($ & % & % & -> & $ & $)".
      iExists _. by rewrite assoc.
    - iIntros (?????) "[$[$ ?]]". by rewrite shift_loc_assoc_nat.
  Qed.
  Lemma subty_prod_assoc' {δ X T Y T' Z T''} :
    ⊢ subty δ (@ty_prod _ Z (@ty_prod X Y T T') T'')
        (ty_prod T (ty_prod T' T'')) (λ '((x, y)', z)', (x, y, z)').
  Proof.
    rewrite ty_prod_unseal subty_unseal /=. iSplit=>/=; [iPureIntro; lia|].
    iSplit; iModIntro.
    - iIntros (????). iDestruct 1 as (??->) "[(% & % & -> & $ & $) $]".
      iExists _. by rewrite -assoc.
    - iIntros (?????) "[[$ $] ?]". by rewrite shift_loc_assoc_nat.
  Qed.

  (** Eliminate a size-0 type over [ty_prod] *)
  Lemma subty_prod_0_elim_l {δ X T Y U} `{!Ty U} :
    ty_size U = 0 → ⊢ subty δ (@ty_prod X Y T U) T fst'.
  Proof.
    rewrite ty_prod_unseal subty_unseal /= => eq0.
    iSplit=>/=; [by rewrite eq0|]. iSplit; iModIntro.
    - iIntros (????). iDestruct 1 as (? wl->) "[T U]".
      iDestruct (ty_own_size with "U") as %eq. rewrite eq0 in eq.
      destruct wl=>//. by rewrite right_id.
    - iIntros (?????) "[$ _]".
  Qed.
  Lemma subty_prod_0_elim_r {δ X T Y U} `{!Ty T} :
    ty_size T = 0 → ⊢ subty δ (@ty_prod X Y T U) U snd'.
  Proof.
    rewrite ty_prod_unseal subty_unseal /= => eq0.
    iSplit=>/=; [by rewrite eq0|]. iSplit; iModIntro.
    - iIntros (????). iDestruct 1 as (wl ?->) "[T U]".
      iDestruct (ty_own_size with "T") as %eq. rewrite eq0 in eq.
      by destruct wl.
    - iIntros (?????) "[_ U]". by rewrite eq0 shift_loc_0.
  Qed.

  (** Introduce [ty_unit] over [ty_prod] *)
  Lemma subty_prod_unit_intro_l {δ X T} :
    ⊢ subty δ T (@ty_prod _ X ty_unit T) (λ x, ((), x)').
  Proof.
    rewrite ty_prod_unseal /ty_unit ty_pty_unseal subty_unseal.
    iSplit=>/=; [done|]. iSplit; iModIntro.
    - iIntros (????) "$". iExists []. iSplit=>//. by iExists ().
    - iIntros (?????) "T". rewrite shift_loc_0. iFrame "T". iExists []=>/=.
      iSplit=>//. by iExists ().
  Qed.
  Lemma subty_prod_unit_intro_r {δ X T} :
    ⊢ subty δ T (@ty_prod X _ T ty_unit) (λ x, (x, ())').
  Proof.
    rewrite ty_prod_unseal /ty_unit ty_pty_unseal subty_unseal.
    iSplit=>/=; [done|]. iSplit; iModIntro.
    - iIntros (????) "$". iExists []. iSplit; [by rewrite right_id|].
      by iExists ().
    - iIntros (?????) "$". iExists []=>/=. iSplit=>//. by iExists ().
  Qed.
End ty_prod.
