(** * Sum type *)

From nola.examples.rust_halt Require Export type.

Implicit Type b : bool.

Section ty_sum.
  Context `{!Csem CON JUDG Σ, !Jsem JUDG (iProp Σ), !rust_haltGS CON Σ,
    !rust_haltC CON, !rust_haltJ CON JUDG Σ, !rust_haltCS CON JUDG Σ,
    !rust_haltJS CON JUDG Σ}.

  (** [ty_sum]: Sum type *)
  Definition ty'_sum_def {X Y} (T : ty CON Σ X) (U : ty CON Σ Y)
    : ty' CON Σ (X +ₓ Y) :=
    let sz := ty_size T `max` ty_size U in
    (λ t d sπ vl, ∃ b wl wl', ⌜vl = #b :: wl ++ wl'⌝ ∧ if negb b
      then ∃ xπ, ⌜∀ π, sπ π = inl (xπ π)⌝ ∧
            ⌜length wl' = sz - ty_size T⌝ ∧ ty_own T t d xπ wl
      else ∃ yπ, ⌜∀ π, sπ π = inr (yπ π)⌝ ∧
            ⌜length wl' = sz - ty_size U⌝ ∧ ty_own U t d yπ wl,
      λ t d l α sπ, ∃ b, ▷ l ↦ˢ[α] #b ∗ if negb b
        then ∃ xπ, ⌜∀ π, sπ π = inl (xπ π)⌝ ∧ ty_shr T t d (l +ₗ 1) α xπ ∗
          ∃ wl, ⌜length wl = sz - ty_size T⌝ ∧ ▷ (l +ₗ 1 +ₗ ty_size T) ↦∗ˢ[α] wl
        else ∃ yπ, ⌜∀ π, sπ π = inr (yπ π)⌝ ∧ ty_shr U t d (l +ₗ 1) α yπ ∗
          ∃ wl, ⌜length wl = sz - ty_size U⌝ ∧ ▷ (l +ₗ 1 +ₗ ty_size U) ↦∗ˢ[α] wl
    )%cif.
  Lemma ty'_sum_aux : seal (@ty'_sum_def). Proof. by eexists. Qed.
  Definition ty'_sum {X Y} := ty'_sum_aux.(unseal) X Y.
  Lemma ty'_sum_unseal : @ty'_sum = @ty'_sum_def. Proof. exact: seal_eq. Qed.
  Definition ty_sum {X Y} (T : ty CON Σ X) (U : ty CON Σ Y)
    : ty CON Σ (X +ₓ Y) := (S (ty_size T `max` ty_size U), ty'_sum T U).
  Lemma ty_sum_unseal :
    @ty_sum = λ _ _ T U, (S (ty_size T `max` ty_size U), ty'_sum_def T U).
  Proof. by rewrite /ty_sum ty'_sum_unseal. Qed.

  (** [ty_sum] is size-preserving *)
  #[export] Instance ty_sum_preserv {X Y k} :
    Proper ((≡[k]≡) ==> (≡[k]≡) ==> (≡[k]≡)) (@ty_sum X Y).
  Proof.
    move=> ?? /ty_proeqv[Tz[To Ts]]?? /ty_proeqv[Uz[Uo Us]].
    rewrite ty_sum_unseal. apply ty_proeqv=>/=. rewrite Tz Uz. split; [done|].
    split=> >.
    - f_equiv=> b. do 2 f_equiv=> ?. f_equiv.
      case: b=>/=; f_equiv=> ?; do 2 f_equiv; [exact: Uo|exact: To].
    - f_equiv=> b. f_equiv.
      case: b=>/=; f_equiv=> ?; do 2 f_equiv; [exact: Us|exact: Ts].
  Qed.
  #[export] Instance ty_sum_proper {X Y} :
    Proper ((≡) ==> (≡) ==> (≡)) (@ty_sum X Y).
  Proof.
    move=> ?*?*. apply equiv_proeqv=> ?. f_equiv; by apply equiv_proeqv.
  Qed.
  #[export] Instance ty_sum_map_preserv {X Y} `(!Preserv' PR _ F, !Preserv G) :
    Preserv (λ T, @ty_sum X Y (F T) (G T)).
  Proof. move=> ?*?*. by do 2 f_equiv. Qed.
  #[export] Instance ty_sum_map_sumuctive {X Y}
    `(ProductiveF : !Productive' PR _ F, ProductiveG : !Productive G) :
    Productive (λ T, @ty_sum X Y (F T) (G T)).
  Proof. move=> ?*?*. f_equiv; by [apply: ProductiveF|apply: ProductiveG]. Qed.

  (** [ty_sum] preserves [Ty] *)
  #[export] Instance ty_sum_ty `{!Ty (X:=X) T, !Ty (X:=Y) U} :
    Ty (ty_sum T U).
  Proof.
    rewrite ty_sum_unseal. split=>/= >.
    - apply bi.exist_persistent. case=>/=; exact _.
    - iDestruct 1 as ([|]?? ->) "/=big"; iDestruct "big" as (? eq) "S";
        rewrite ty_own_size length_app; iDestruct "S" as %[->->];
        iPureIntro=>/=; lia.
    - move=> ?. f_equiv=> b. do 5 f_equiv.
      case: b=>/=; do 4 f_equiv; exact: ty_own_depth.
    - move=> ?. f_equiv=> b. f_equiv.
      case: b=>/=; do 4 f_equiv; exact: ty_shr_depth.
    - move=> eq. f_equiv=> b. do 5 f_equiv.
      case: b=>/=; (do 4 f_equiv)=> ??; by rewrite -eq.
    - move=> eq. f_equiv=> b. f_equiv.
      case: b=>/=; (do 4 f_equiv)=> ??; by rewrite -eq.
  Qed.

  (** [ty_sum] preserves [TyOpAt] *)
  #[export] Instance ty_sum_ty_op `{!Ty (X:=X) T, !Ty (X:=Y) U}
    `(!TyOpAt T κ d, !TyOpAt U κ d) :
    TyOpAt (ty_sum T U) κ d.
  Proof.
    rewrite ty_sum_unseal. split=>/=.
    - iIntros (? xπ ??) "κ".
      iDestruct 1 as ([|]??->) "/=S"; iDestruct "S" as (? eq eql) "S";
        [iMod (ty_own_proph with "κ S") as "big"|
          iMod (ty_own_proph with "κ S") as "big"];
        iDestruct "big" as (ξl r dep) "[$ →S]"; iModIntro;
        (iSplit; [iPureIntro; eapply proph_dep_proper;
          [exact: eq|done|exact: proph_dep_f]|]);
        iIntros "ξl"; iMod ("→S" with "ξl") as "[$ S]"; iModIntro;
        [iExists true|iExists false]=>/=; iFrame "S"; by iExists _.
    - iIntros (??? sπ q) "κα". iDestruct 1 as (b) "[↦ big]".
      case b=>/=; iDestruct "big" as (? eq) "(S & % & % & ↦r)";
        [iMod (ty_shr_proph with "κα S") as "big"|
          iMod (ty_shr_proph with "κα S") as "big"];
        iDestruct "big" as (???) "[$$]"; iPureIntro;
        (eapply proph_dep_proper; [exact: eq|done|exact: proph_dep_f]).
    - iIntros (?????) "[κ α] b".
      iMod (bord_open (M:=borrowM) with "α b") as "/=[o (% & ↦ & %b & big)]".
      case b=>/=; iDestruct "big" as (?? -> ? eq ?) "S";
        rewrite heap_pointsto_vec_cons heap_pointsto_vec_app;
        [iDestruct (ty_own_size with "S") as %->|
          iDestruct (ty_own_size with "S") as %->];
        iDestruct "↦" as "(↦ & ↦S & ↦r)".
      + iMod (obord_subdiv (FML:=cifOF _) (M:=borrowM)
          [▷ _ ↦ _; cif_pointsto_ty _ (_ +ₗ 1) _ _ _; ▷ (_ +ₗ _ +ₗ _) ↦∗ _]%cif
          with "[] o [↦ ↦S S ↦r] []") as "(α & _ & b & bS & br & _)"=>/=.
        { iApply lft_sincl_refl. } { iFrame. }
        { iIntros "_ (↦ & (% & ↦S & S) & ↦r & _) !>". iExists (_ :: _ ++ _).
          rewrite heap_pointsto_vec_cons heap_pointsto_vec_app. iFrame "↦ ↦S".
          iDestruct (ty_own_size with "S") as %->. iFrame "↦r".
          iExists true=>/=. iFrame "S". by iExists _. }
        iMod (spointsto_alloc with "α b") as "[α ↦]".
        iMod (spointsto_vec_alloc with "α br") as "[α ↦r]". rewrite bor_tok_bor.
        iMod (ty_share (T:=U) with "[$κ $α //] bS") as "[$ S]". iModIntro.
        iExists true=>/=. by iFrame.
      + iMod (obord_subdiv (FML:=cifOF _) (M:=borrowM)
          [▷ _ ↦ _; cif_pointsto_ty _ (_ +ₗ 1) _ _ _; ▷ (_ +ₗ _ +ₗ _) ↦∗ _]%cif
          with "[] o [↦ ↦S S ↦r] []") as "(α & _ & b & bS & br & _)"=>/=.
        { iApply lft_sincl_refl. } { iFrame. }
        { iIntros "_ (↦ & (% & ↦S & S) & ↦r & _) !>". iExists (_ :: _ ++ _).
          rewrite heap_pointsto_vec_cons heap_pointsto_vec_app. iFrame "↦ ↦S".
          iDestruct (ty_own_size with "S") as %->. iFrame "↦r".
          iExists false=>/=. iFrame "S". by iExists _. }
        iMod (spointsto_alloc with "α b") as "[α ↦]".
        iMod (spointsto_vec_alloc with "α br") as "[α ↦r]". rewrite bor_tok_bor.
        iMod (ty_share (T:=T) with "[$κ $α //] bS") as "[$ S]". iModIntro.
        iExists false=>/=. by iFrame.
  Qed.

  (** [ty_sum] preserves [Send] *)
  #[export] Instance ty_sum_send `{!Send (X:=X) T, !Send (X:=Y) U} :
    Send (ty_sum T U).
  Proof.
    rewrite ty_sum_unseal. move=>/= >. f_equiv=> b. do 2 f_equiv=> ?. f_equiv.
    case: b=>/=; f_equiv=> ?; do 2 f_equiv; exact: send.
  Qed.
  (** [ty_sum] preserves [Sync] *)
  #[export] Instance ty_sum_sync `{!Sync (X:=X) T, !Sync (X:=Y) U} :
    Sync (ty_sum T U).
  Proof.
    rewrite ty_sum_unseal. move=>/= >. f_equiv=> b. f_equiv.
    case: b=>/=; f_equiv=> ?; do 2 f_equiv; exact: sync.
  Qed.
  (** [ty_sum] preserves [Copy] *)
  #[export] Instance ty_sum_copy
    `{!Ty (X:=X) T, !Ty (X:=Y) U, !Copy T, !Copy U} :
    Copy (ty_sum T U).
  Proof.
    rewrite ty_sum_unseal. split=>/= >.
    { apply: bi.exist_persistent. case=>/=; exact _. }
    iIntros (sub) "(α & α' & α'') t (%b & >↦ & S)".
    case: b=>/=; iDestruct "S" as (? eq) "(S & % & % & >↦r)";
      (iMod (copy_shr_acc with "α t S") as (? r) "(↦S & t & S & cl)";
        [etrans; [|done]; apply union_subseteq_r', shr_locsE_mono=>/=; lia|]);
      iMod (spointsto_acc with "α' ↦") as (r') "[↦ →α']";
      iMod (spointsto_vec_acc with "α'' ↦r") as (r'') "[↦r →α'']"; iModIntro;
      case: (Qp.lower_bound r' r'')=> s[?[?[->->]]];
      case: (Qp.lower_bound r s)=> ?[?[?[->->]]]; iExists (_ :: _ ++ _), _;
      rewrite heap_pointsto_vec_cons heap_pointsto_vec_app -!Qp.add_assoc;
      iDestruct "↦S" as "[$ ↦S']"; iDestruct "↦" as "[$ ↦']";
      [iDestruct (ty_own_size with "S") as %->|
        iDestruct (ty_own_size with "S") as %->];
      iDestruct "↦r" as "[$ ↦r']";
      (iDestruct (na_own_acc with "t") as "[$ →t]";
        [apply difference_mono_l, union_subseteq_r', shr_locsE_mono=>/=; lia|]);
      [iSplitL "S"; [iExists true=>/=; iFrame "S"; by iExists _|]|
        iSplitL "S"; [iExists false=>/=; iFrame "S"; by iExists _|]];
      iIntros "(↦ & ↦S & ↦r) t'"; iDestruct ("→t" with "t'") as "t";
      iCombine ("↦S ↦S'") as "↦S"; iMod ("cl" with "↦S t") as "[$$]";
      iMod ("→α'" with "[$↦ $↦' //]") as "$"; iCombine ("↦r ↦r'") as "↦r";
      by iMod ("→α''" with "↦r").
  Qed.

  (** Resolution over [ty_sum] *)
  #[export] Instance resol_sum
    `(!ResolAt (X:=X) T κ post d, !ResolAt (X:=Y) U κ post' d) :
    ResolAt (ty_sum T U) κ
      (λ s, match s with inl x => post x | inr y => post' y end) d.
  Proof.
    rewrite ty_sum_unseal. split=> > /=. iIntros "κ t (%b & % & % & -> & big)".
    case: b=>/=; iDestruct "big" as (? eq _) "S";
      [iMod (resol with "κ t S") as "($ & $ & post)"|
        iMod (resol with "κ t S") as "($ & $ & post)"]; iModIntro;
      iApply (proph_obs_impl with "post")=> ?; by rewrite eq.
  Qed.

  (** Real part of [ty_sum] *)
  #[export] Instance real_sum
    `(!RealAt (A:=A) (X:=X) T κ get d, !RealAt (A:=B) (X:=Y) U κ get' d) :
    RealAt (ty_sum T U) κ
      (λ s, match s with inl x => inl (get x) | inr y => inr (get' y) end) d.
  Proof.
    rewrite ty_sum_unseal. split=> > /=; iIntros "κ t".
    - iDestruct 1 as (b) "(% & % & $ & big)".
      case: b=>/=; iDestruct "big" as (? eq) "[$ S]";
        [iMod (real_own with "κ t S") as ([? eq']) "($ & $ & $)"|
          iMod (real_own with "κ t S") as ([? eq']) "($ & $ & $)"]; iPureIntro;
        (split; [|done]); eexists _=> ?; by rewrite eq eq'.
    - iDestruct 1 as (b) "[_ big]".
      case: b=>/=; iDestruct "big" as (? eq) "[S _]";
        [iMod (real_shr with "κ t S") as ([? eq']) "[$ $]"|
          iMod (real_shr with "κ t S") as ([? eq']) "[$ $]"]; iPureIntro;
        eexists _=> ?; by rewrite eq eq'.
  Qed.

  (** Subtyping on [ty_sum] *)
  Lemma subty_sum {δ X T X' T' f Y U Y' U' g} :
    subty (X:=X) (Y:=X') δ T T' f -∗ subty (X:=Y) (Y:=Y') δ U U' g -∗
      subty δ (ty_sum T U) (ty_sum T' U')
        (λ s, match s with inl x => inl (f x) | inr y => inr (g y) end).
  Proof.
    rewrite ty_sum_unseal subty_unseal /=.
    iIntros "[%Tz[#To #Ts]][%Uz[#Uo #Us]]". iSplit=>/=; [by rewrite Tz Uz|].
    iSplit; iModIntro; rewrite Tz Uz.
    - iIntros (????). iDestruct 1 as (b ?? ->) "big". iExists b.
      case: b=>/=; iDestruct "big" as (? eq) "[$ S]"; iExists _;
        (iSplit; [done|]); iExists _; setoid_rewrite eq; (iSplit; [done|]);
        by [iApply "Uo"|iApply "To"].
    - iIntros (?????) "(%b & $ & big)".
      case: b=>/=; iDestruct "big" as (? eq) "(S & % & $)"; iExists _;
        setoid_rewrite eq; (iSplit; [done|]); by [iApply "Us"|iApply "Ts"].
  Qed.
End ty_sum.
