(** * Box pointer type *)

From nola.examples.rust_halt Require Export type.

Implicit Type l : loc.

Section ty_box.
  Context `{!rust_haltGS CON Σ, !rust_haltC CON, !rust_haltJ CON JUDG Σ,
    !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ), !rust_haltCS CON JUDG Σ,
    !rust_haltJS CON JUDG Σ}.

  (** [ty_box]: Box pointer type *)
  Definition ty_box_def {X} (T : ty CON Σ X) : ty CON Σ X :=
    (λ t d xπ vl, ∃ l d' xπ' wl, ⌜vl = [ #l]⌝ ∗ ⌜d' < d⌝ ∗ ⌜∀ π, xπ' π = xπ π⌝ ∗
        ▷ l ↦∗ wl ∗ ▷ †l…(length wl) ∗ cif_store (T.1 t d' xπ' wl),
      λ t d l α xπ, ∃ l' d' xπ', ⌜d' < d⌝ ∗ ⌜∀ π, xπ' π = xπ π⌝ ∗
        ▷ l ↦ˢ[α] #l' ∗ □ cif_store (T.2 t d' l' α xπ'))%cif.
  Lemma ty_box_aux : seal (@ty_box_def). Proof. by eexists _. Qed.
  Definition ty_box {X} := ty_box_aux.(unseal) X.
  Lemma ty_box_unseal : @ty_box = @ty_box_def. Proof. exact: seal_eq. Qed.

  (** [ty_box] is productive *)
  #[export] Instance ty_box_productive {X} : Productive (ty_box (X:=X)).
  Proof.
    move=> ?[??][??] /ty_proeq_later [/=eqO eqS].
    rewrite ty_box_unseal /ty_box_def. apply ty_proeq=>/=. split=> >.
    { do 4 f_equiv=> ?. by rewrite eqO. } { do 3 f_equiv=> ?. by rewrite eqS. }
  Qed.

  (** [ty_box] satisfies [Ty] *)
  #[export] Instance ty_box_ty {X T} : Ty (ty_box (X:=X) T) 1.
  Proof.
    rewrite ty_box_unseal. split=>/= *. { exact _. }
    { by iIntros "(% & % & % & % & -> & _)". }
    { do 10 f_equiv. iPureIntro. lia. } { do 7 f_equiv. iPureIntro. lia. }
    { do 11 f_equiv. iPureIntro=> eq ?. by rewrite eq. }
    { (do 9 f_equiv)=> eq ?. by rewrite eq. }
  Qed.

  (** [ty_box] satisfies [TyOp] *)
  #[export] Instance ty_box_ty_op `{!Ty (X:=X) T sz, !TyOpLt T α d} :
    TyOpAt (ty_box T) α d.
  Proof.
    rewrite ty_box_unseal. split=>/= *.
    - iIntros "α". iDestruct 1 as (???? -> ? eq) "(↦ & † & T)".
      rewrite sem_cif_in /=. iMod (stored_acc with "T") as "T".
      iMod (ty_own_proph_lt with "α T") as (???) "[$ →T]"=>//. iModIntro.
      iSplit. { iPureIntro. by eapply proph_dep_proper. }
      iIntros "ξl". iMod ("→T" with "ξl") as "[$ T]".
      iMod (store_alloc with "T") as "T". iModIntro. iFrame "↦ †".
      iExists _, _. do 3 iSplit=>//. by rewrite sem_cif_in.
    - iIntros "αβ". iDestruct 1 as (???? eq) "[↦ #T]". rewrite sem_cif_in /=.
      iMod (stored_acc with "T") as "{T}T".
      iMod (ty_shr_proph_lt with "αβ T") as (???) "[$ →T]"=>//. iModIntro.
      iSplit. { iPureIntro. by eapply proph_dep_proper. }
      iIntros "ξl". iMod ("→T" with "ξl") as "[$ T]".
      iMod (store_alloc_pers with "T") as "T". iModIntro. iFrame "↦".
      iExists _, _. do 2 iSplit=>//. by rewrite sem_cif_in.
    - iIntros "[α β] b".
      iMod (bord_open (M:=borrowM) with "β b") as "/=[o (% & ↦ & big)]".
      iDestruct "big" as (???? -> ? eq) "(↦' & † & T)". rewrite sem_cif_in /=.
      iMod (stored_acc with "T") as "T".
      iDestruct (ty_own_size with "T") as %->.
      rewrite heap_pointsto_vec_singleton.
      iMod (obord_subdiv (FML:=cifOF _) (M:=borrowM)
        [▷ _ ↦ _; ∃ wl, ▷ _ ↦∗ wl ∗ T.1 _ _ _ wl]%cif
        with "[] o [$↦ $↦' $T //] [†]") as "(β & _ & b & b' & _)"=>/=.
      { iApply lft_sincl_refl. }
      { iIntros "_ (↦ & (% & $ & T) & _)". rewrite -heap_pointsto_vec_singleton.
        iDestruct (ty_own_size with "T") as %->.
        iMod (store_alloc with "T") as "T". iModIntro. iFrame "↦ †".
        iExists _, _. do 3 iSplit=>//. by rewrite sem_cif_in. }
      iMod (spointsto_alloc with "β b") as "[β $]". rewrite bor_tok_bor.
      iMod (ty_share_lt (T:=T) with "[$α $β //] b'") as "[$ T]"=>//.
      iMod (store_alloc_pers with "T") as "T". iModIntro. iExists _, _.
      do 2 iSplit=>//. by rewrite sem_cif_in /=.
  Qed.

  (** [ty_box] preserves [Send] *)
  #[export] Instance ty_box_send `{!Send (X:=X) T} : Send (ty_box T).
  Proof.
    rewrite ty_box_unseal. move=>/= ?????. do 4 f_equiv=> ?. do 6 f_equiv.
    apply: send.
  Qed.
  (** [ty_box] preserves [Sync] *)
  #[export] Instance ty_box_sync `{!Sync (X:=X) T} : Sync (ty_box T).
  Proof.
    rewrite ty_box_unseal. move=>/= ??????. do 3 f_equiv=> ?. do 5 f_equiv.
    apply: sync.
  Qed.

  (** Subtyping over [ty_box] *)
  Lemma subty_ty_box `{!Deriv ih δ} {X Y T U f} :
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
End ty_box.
