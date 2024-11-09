(** * Any-depth type *)

From nola.examples.rust_halt Require Export type.

Implicit Type X Y : xty.

Section ty_anydep.
  Context `{!Csem CON JUDG Σ, !Jsem JUDG (iProp Σ), !rust_haltGS CON Σ,
    !rust_haltC CON, !rust_haltJ CON JUDG Σ, !rust_haltJS CON JUDG Σ}.

  (** [ty_anydep]: Any-depth type *)
  Definition ty_anydep {X} (T : ty CON Σ X) : ty CON Σ X :=
    (λ t d xπ vl, ∃ d', T.1 t d' xπ vl,
      λ t d l α xπ, ∃ d', T.2 t d' l α xπ)%cif.

  (** [ty_anydep] is size-preserving *)
  #[export] Instance ty_anydep_preserv {X} : Preserv (@ty_anydep X).
  Proof.
    move=> ?[??][??][/=eqvO eqvS].
    split=>/= >; f_equiv=> ?; [apply eqvO|apply eqvS].
  Qed.
  #[export] Instance ty_anydep_map_preserv {X} `(!Preserv' PR _ F) :
    Preserv (λ T, @ty_anydep X (F T)).
  Proof. solve_proper. Qed.
  #[export] Instance ty_anydep_map_productive {X} `(!Productive' PR _ F) :
    Productive (λ T, @ty_anydep X (F T)).
  Proof. solve_proper. Qed.

  (** [ty_anydep] preserves [Ty] *)
  #[export] Instance ty_anydep_ty `{!Ty (X:=X) T sz} : Ty (ty_anydep T) sz.
  Proof.
    split=>//= *. { exact _. }
    { iIntros "[% T]". by rewrite ty_own_size. }
    { iIntros "[% T]". iExists _. by iApply (ty_own_clair with "T"). }
    { iIntros "[% T]". iExists _. by iApply (ty_shr_clair with "T"). }
  Qed.

  (** [ty_anydep] preserves [TyOp] *)
  #[export] Instance ty_anydep_ty_op {X} `(!TyOp T κ) :
    TyOp (ty_anydep (X:=X) T) κ.
  Proof.
    move=> ?. split=>/= >.
    - iIntros "κ [% T]". iMod (ty_own_proph with "κ T") as (??) "($ & $ & →T)".
      iIntros "!> ξl". by iMod ("→T" with "ξl") as "[$$]".
    - iIntros "κα [% T]".
      iMod (ty_shr_proph with "κα T") as (??) "($ & $ & →T)". iIntros "!> ξl".
      by iMod ("→T" with "ξl") as "[$$]".
    - iIntros "[κ α] b".
      iMod (bord_open (M:=borrowM) with "α b") as "/=[o (% & ↦ & % & T)]".
      iMod (obord_subdiv (FML:=cifOF _) (M:=borrowM)
        [∃ vl, ▷ _ ↦∗ vl ∗ T.1 _ _ _ vl]%cif with "[] o [$↦ $T //] []")
        as "(α & _ & b & _)"=>/=.
      { iApply lft_sincl_refl. } { by iIntros "_ [(% & $ & $) _]". }
      rewrite bor_tok_bor.
      by iMod (ty_share (T:=T) with "[$κ $α //] b") as "[$$]".
  Qed.

  (** [ty_anydep] preserves [Send] *)
  #[export] Instance ty_anydep_send `{!Send (X:=X) T} : Send (ty_anydep T).
  Proof. move=>/= >. f_equiv=> ?. apply: send. Qed.
  (** [ty_anydep] preserves [Sync] *)
  #[export] Instance ty_anydep_sync `{!Sync (X:=X) T} : Sync (ty_anydep T).
  Proof. move=>/= >. f_equiv=> ?. apply: sync. Qed.
  (** [ty_anydep] preserves [Copy] *)
  #[export] Instance ty_anydep_copy `{!Copy (X:=X) T sz} :
    Copy (ty_anydep T) sz.
  Proof.
    split; [exact _|]=>/= *. iIntros "α t [% T]".
    iMod (copy_shr_acc with "α t T") as (??) "($ & $ & $ & $)"=>//.
  Qed.

  (** Subtyping on [ty_anydep] *)
  Lemma subty_to_ty_anydep {δ X T} : ⊢ subty (X:=X) δ T (ty_anydep T) id.
  Proof.
    rewrite subty_unseal. iSplit; iModIntro=>/=.
    { iIntros (????) "$". } { iIntros (?????) "$". }
  Qed.
  Lemma subty_ty_anydep {δ X Y T U f} :
    subty (X:=X) (Y:=Y) δ T U f ⊢ subty δ (ty_anydep T) (ty_anydep U) f.
  Proof.
    rewrite subty_unseal. iIntros "#[subO subS]". iSplit; iModIntro=>/=.
    - iIntros (????) "[% T]". iExists _. by iApply "subO".
    - iIntros (?????) "[% T]". iExists _. by iApply "subS".
  Qed.

  (** Eliminate [ty_anydep] *)
  Lemma type_elim_anydep v
    `(!EtcxExtract (Yl:=Yl) (Zl:=Zl) (v ◁{d'} ty_anydep (X:=X) T)
        Γi Γr get getr) {Zl' κ e Γo pre} :
    (∀ d, type (Yl:=Zl') κ (v ◁{d} T ᵖ:: Γr) e Γo pre) ⊢
      type κ Γi e Γo (λ post xl, pre post (get xl, getr xl)').
  Proof.
    rewrite type_unseal. iIntros "#type !>/=" (????) "κ t pre".
    rewrite etcx_extract /=. iIntros "[[% T] Γr]".
    iApply ("type" with "κ t pre [$T $Γr]").
  Qed.
End ty_anydep.
