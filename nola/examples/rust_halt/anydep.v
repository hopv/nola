(** * Any-depth type *)

From nola.examples.rust_halt Require Export type.

Implicit Type X Y : xty.

Section ty_anydep.
  Context `{!Csem CON JUDG Σ, !Jsem JUDG (iProp Σ), !rust_haltGS CON Σ,
    !rust_haltC CON, !rust_haltJ CON JUDG Σ, !rust_haltJS CON JUDG Σ}.

  (** [ty_anydep]: Any-depth type *)
  Definition ty'_anydep_def {X} (T : ty CON Σ X) : ty' CON Σ X :=
    (λ t d xπ vl, ∃ d', ty_own T t d' xπ vl,
      λ t d l α xπ, ∃ d', ty_shr T t d' l α xπ)%cif.
  Lemma ty'_anydep_aux : seal (@ty'_anydep_def). Proof. by eexists _. Qed.
  Definition ty'_anydep {X} := ty'_anydep_aux.(unseal) X.
  Lemma ty'_anydep_unseal : @ty'_anydep = @ty'_anydep_def.
  Proof. by exact: seal_eq. Qed.
  Definition ty_anydep {X} (T : ty CON Σ X) : ty CON Σ X :=
    (ty_size T, ty'_anydep T).
  Lemma ty_anydep_unseal : @ty_anydep = λ _ T, (ty_size T, ty'_anydep_def T).
  Proof. by rewrite /ty_anydep ty'_anydep_unseal. Qed.

  (** [ty_anydep] is size-preserving *)
  #[export] Instance ty_anydep_preserv {X} : Preserv (@ty_anydep X).
  Proof.
    move=> ??? /ty_proeqv[?[eqvO eqvS]]. rewrite ty_anydep_unseal.
    apply ty_proeqv=>/=. split=>//.
    split=> *; f_equiv=> ?; [exact: eqvO|exact: eqvS].
  Qed.
  #[export] Instance ty_anydep_proper{X} : Proper ((≡) ==> (≡)) (@ty_anydep X).
  Proof. apply preserv_proper, _. Qed.
  #[export] Instance ty_anydep_map_preserv {X} `(!Preserv' PR _ F) :
    Preserv (λ T, @ty_anydep X (F T)).
  Proof. move=> ?*?*. by do 2 f_equiv. Qed.
  #[export] Instance ty_anydep_map_productive {X} `(!Productive' PR _ F) :
    Productive (λ T, @ty_anydep X (F T)).
  Proof. move=> ?*?*. by do 2 f_equiv. Qed.

  (** [ty_anydep] preserves [Ty] *)
  #[export] Instance ty_anydep_ty `{!Ty (X:=X) T} : Ty (ty_anydep T).
  Proof.
    rewrite ty_anydep_unseal. split=>//= *. { exact _. }
    { iIntros "[% T]". by rewrite ty_own_size. }
    { iIntros "[% T]". iExists _. by iApply (ty_own_clair with "T"). }
    { iIntros "[% T]". iExists _. by iApply (ty_shr_clair with "T"). }
  Qed.

  (** [ty_anydep] preserves [TyOp] *)
  #[export] Instance ty_anydep_ty_op {X} `(!TyOp T κ) : TyOp (@ty_anydep X T) κ.
  Proof.
    rewrite ty_anydep_unseal=> ?. split=>/= >.
    - iIntros "κ [% T]". iMod (ty_own_proph with "κ T") as (??) "($ & $ & →T)".
      iIntros "!> ξl". by iMod ("→T" with "ξl") as "[$$]".
    - iIntros "κα [% T]".
      iMod (ty_shr_proph with "κα T") as (??) "($ & $ & →T)". iIntros "!> ξl".
      by iMod ("→T" with "ξl") as "[$$]".
    - iIntros "[κ α] b".
      iMod (bord_open (M:=borrowM) with "α b") as "/=[o (% & ↦ & % & T)]".
      iMod (obord_subdiv (M:=borrowM) [cif_pointsto_ty _ _ _ _ _]
        with "[] o [$↦ $T //] []") as "(α & _ & b & _)"=>/=.
      { iApply lft_sincl_refl. } { by iIntros "_ [(% & $ & $) _]". }
      rewrite bor_tok_bor.
      by iMod (ty_share (T:=T) with "[$κ $α //] b") as "[$$]".
  Qed.

  (** [ty_anydep] preserves [Send] *)
  #[export] Instance ty_anydep_send `{!Send (X:=X) T} : Send (ty_anydep T).
  Proof.
    rewrite ty_anydep_unseal. move=>/= *. f_equiv=> ?. exact: send.
  Qed.
  (** [ty_anydep] preserves [Sync] *)
  #[export] Instance ty_anydep_sync `{!Sync (X:=X) T} : Sync (ty_anydep T).
  Proof.
    rewrite ty_anydep_unseal. move=>/= *?. f_equiv=> ?. exact: sync.
  Qed.
  (** [ty_anydep] preserves [Copy] *)
  #[export] Instance ty_anydep_copy `{!Copy (X:=X) T} : Copy (ty_anydep T).
  Proof.
    rewrite ty_anydep_unseal. split; [exact _|]=>/= *.
    iIntros "α t [% T]".
    iMod (copy_shr_acc with "α t T") as (??) "($ & $ & $ & $)"=>//.
  Qed.

  (** Resolution over [ty_mod] *)
  #[export] Instance resol_anydep {X} `(!Resol T κ post) :
    Resol (ty_anydep (X:=X) T) κ post.
  Proof.
    rewrite ty_anydep_unseal. split=> > /=. iIntros "κ [% T]".
    iApply (resol with "κ T").
  Qed.

  (** Subtyping on [ty_anydep] *)
  Lemma subty_to_anydep {δ X T} : ⊢ subty (X:=X) δ T (ty_anydep T) id.
  Proof.
    rewrite subty_unseal ty_anydep_unseal. iSplit=>//. iSplit; iModIntro=>/=.
    { iIntros (????) "$". } { iIntros (?????) "$". }
  Qed.
  Lemma subty_anydep {δ X Y T U f} :
    subty (X:=X) (Y:=Y) δ T U f ⊢ subty δ (ty_anydep T) (ty_anydep U) f.
  Proof.
    rewrite subty_unseal ty_anydep_unseal. iIntros "[%[#subO #subS]]".
    iSplit=>//. iSplit; iModIntro=>/=.
    - iIntros (????) "[% T]". iExists _. by iApply "subO".
    - iIntros (?????) "[% T]". iExists _. by iApply "subS".
  Qed.

  (** Eliminate [ty_anydep] *)
  Lemma type_anydep_elim v
    `(!EtcxExtract (Yl:=Yl) (Zl:=Zl) (v ◁{d'} @ty_anydep X T) Γi Γr get getr)
    {Zl' κ e Γo pre} :
    (∀ d, type (Yl:=Zl') κ (v ◁{d} T ᵖ:: Γr) e Γo pre) ⊢
      type κ Γi e Γo (λ post xl, pre post (get xl, getr xl)').
  Proof.
    rewrite type_unseal. iIntros "#type !>/=" (????) "κ t pre".
    rewrite etcx_extract ty_anydep_unseal /=. iIntros "[[% T] Γr]".
    iApply ("type" with "κ t pre [$T $Γr]").
  Qed.

  (** Update the depth under [ty_anydep] *)
  Lemma sub_anydep_depth v
    `(!EtcxExtract (Yl:=Yl) (Zl:=Zl) (v ◁{d} @ty_anydep X T) Γi Γr get getr)
    {κ d'} :
    ⊢ sub κ Γi (v ◁{d'} ty_anydep T ᵖ:: Γr)
        (λ post xl, post (get xl, getr xl)').
  Proof.
    rewrite sub_unseal. iIntros (????) "!> $ $ pre". rewrite etcx_extract.
    rewrite ty_anydep_unseal /=. iIntros "[[% T] Γr] !>".
    iFrame "pre". iFrame.
  Qed.
End ty_anydep.
