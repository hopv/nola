(** * Shared reference type *)

From nola.examples.rust_halt Require Export ptr.

Implicit Type l : loc.

Section ty_shrref.
  Context `{!rust_haltGS CON Σ, !rust_haltC CON, !rust_haltJ CON JUDG Σ,
    !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ), !rust_haltCS CON JUDG Σ,
    !rust_haltJS CON JUDG Σ}.

  (** [ty_shrref]: Shared reference type *)
  Definition sty'_shrref_def {X} (α : lft) (T : ty CON Σ X) : ownty CON Σ X :=
    λ t d xπ vl,
      (∃ l d' xπ', ⌜vl = [ #l]⌝ ∧ ⌜d' < d⌝ ∧ ⌜∀ π, xπ' π = xπ π⌝ ∧
        □ cif_store (ty_shr T t d' l α xπ'))%cif.
  Lemma sty'_shrref_aux : seal (@sty'_shrref_def). Proof. by eexists. Qed.
  Definition sty'_shrref {X} := sty'_shrref_aux.(unseal) X.
  Lemma sty'_shrref_unseal : @sty'_shrref = @sty'_shrref_def.
  Proof. exact: seal_eq. Qed.
  Definition sty_shrref {X} (α : lft) (T : ty CON Σ X) : sty CON Σ X :=
    (1, sty'_shrref α T).
  Lemma sty_shrref_unseal : @sty_shrref = λ _ α T, (1, sty'_shrref_def α T).
  Proof. by rewrite /sty_shrref sty'_shrref_unseal. Qed.
  Definition ty_shrref {X} (α : lft) (T : ty CON Σ X) : ty CON Σ X :=
    ty_sty (sty_shrref α T).
  Lemma ty_shrref_unseal :
    @ty_shrref = λ _ α T, (1, ty'_sty_def (1, sty'_shrref_def α T)).
  Proof. by rewrite /ty_shrref ty_sty_unseal sty_shrref_unseal. Qed.

  (** [ty_shrref] is productive *)
  #[export] Instance ty_shrref_productive {X α} :
    Productive (@ty_shrref X α).
  Proof.
    move=> ??? /ty_proeqv_later [_ eqv]. apply: ty_sty_preserv.
    rewrite sty_shrref_unseal. apply sty_proeqv=>/=. split=>// >.
    unfold sty'_shrref_def=>/=. do 3 f_equiv=> ?. by rewrite eqv.
  Qed.
  #[export] Instance ty_shrref_proper {X α} :
    Proper ((≡) ==> (≡)) (@ty_shrref X α).
  Proof. apply productive_proper, _. Qed.
  #[export] Instance ty_shrref_map_productive `(!Preserv' PR (ty _ _ X) F) {α} :
    Productive (λ T, ty_shrref α (F T)).
  Proof. move=> k ???. f_equiv. destruct k=>//=. by f_equiv. Qed.
  #[export] Instance ty_shrref_map_preserv `(!Preserv' PR (ty _ _ X) F) {α} :
    Preserv (λ T, ty_shrref α (F T)).
  Proof. apply productive_preserv, _. Qed.

  (** [sty_shrref] satisfies [Sty] *)
  #[export] Instance sty_shrref_sty {X α T} : Sty (@sty_shrref X α T).
  Proof.
    rewrite sty_shrref_unseal. split=>/= *. { exact _. }
    { by iIntros "(% & % & % & -> & _)". }
    { (do 9 f_equiv)=> ?. lia. } { (do 10 f_equiv)=> eq ?. by rewrite eq. }
  Qed.

  (** [ty_shrref] satisfies [TyOp] *)
  #[export] Instance ty_shrref_ty_op `{!Ty (X:=X) T}
    `(!TyOpLe T κ 1 d, !LftIncl κ α) :
    TyOpAt (ty_shrref α T) κ d.
  Proof.
    apply: sty_op_at=> >. rewrite sty_shrref_unseal /=. iIntros "κ".
    iDestruct 1 as (??? -> ??) "T". rewrite sem_cif_in /=.
    iMod (stored_acc with "T") as "T".
    iDestruct (lft_incl'_live_acc (κ ⊓ α) with "κ") as (?) "[κα →κ]".
    iMod (ty_shr_proph_le with "κα T") as (???) "[$ →κα]"=>//. iModIntro.
    iSplit. { iPureIntro. by eapply proph_dep_proper. }
    iIntros "ξl". iMod ("→κα" with "ξl") as "κα". iModIntro. by iApply "→κ".
  Qed.

  (** [ty_shrref] is [Send] when the body type is [Sync] *)
  #[export] Instance ty_shrref_send `{!Sync (X:=X) T} {α} :
    Send (ty_shrref α T).
  Proof.
    rewrite ty_shrref_unseal /sty'_shrref_def=> > /=. do 3 f_equiv=> ?.
    do 5 f_equiv. exact: sync.
  Qed.
  (** [ty_shrref] preserves [Sync] *)
  #[export] Instance ty_shrref_sync `{!Sync (X:=X) T} {α} :
    Sync (ty_shrref α T).
  Proof. exact _. Qed.

  (** [ty_shrref] satisfies [Copy] *)
  #[export] Instance ty_shrref_copy {X α T} : Copy (@ty_shrref X α T).
  Proof. exact _. Qed.

  (** Trivial resolution over [ty_shrref] *)
  #[export] Instance resol_shrref {X T α κ} :
    Resol (ty_shrref (X:=X) α T) κ (λ _, True).
  Proof. exact _. Qed.

  (** Real part of [ty_shrref] *)
  #[export] Instance real_shrref `(!RealLe (X:=X) (A:=A) T κ get 1 d) {α} :
    RealAt (ty_shrref α T) κ get d.
  Proof.
    apply: sty_real=>/= >. rewrite sty'_shrref_unseal /=. iIntros "κ t".
    iDestruct 1 as (??? _ ? eq) "T". rewrite sem_cif_in /=.
    iMod (stored_acc with "T") as "T".
    iMod (real_shr_le with "κ t T") as ([? eq']) "[$$]"=>//.
    iPureIntro. eexists _=> π. by rewrite -(eq π).
  Qed.

  (** Modify the lifetime of [ty_shrref] *)
  Lemma subty_shrref_lft `{!Deriv ih δ, !Ty (X:=X) T} {β α} :
    β ⊑□ α ⊢ subty δ (ty_shrref α T) (ty_shrref β T) id.
  Proof.
    iIntros "#⊑". iApply subty_sty=>//. rewrite sty_shrref_unseal.
    iIntros (????) "!>/=". iDestruct 1 as (???) "($ & $ & $ & #?)". iModIntro.
    rewrite !sem_cif_in /=. iApply store_wand; [|done]. iIntros (????) "T !>".
    by iApply (ty_shr_lft with "⊑ T").
  Qed.

  (** Subtyping over [ty_shrref] *)
  Lemma subty_shrref `{!Deriv ih δ} {X Y T U f α} :
    □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → subty (X:=X) (Y:=Y) δ' T U f) ⊢
      subty δ (ty_shrref α T) (ty_shrref α U) f.
  Proof.
    iIntros "#tosub". iApply subty_sty=>//. rewrite sty_shrref_unseal.
    iIntros (????) "!>/=". iDestruct 1 as (???) "($ & $ & %eq & #T)". iExists _.
    rewrite !sem_cif_in /=. iSplit. { iPureIntro=> ?. by rewrite -eq. }
    iModIntro. iApply (store_wand with "[] T"). iIntros (????) "{T}T !>".
    rewrite subty_unseal. iDestruct ("tosub" with "[//] [//]") as (_) "sub".
    by iApply "sub".
  Qed.

  (** Read a copyable object from [ty_shrref] *)
  #[export] Instance read_shrref `{!Ty (X:=X) T, !Copy T, !LftIncl κ α} :
    Read κ (ty_shrref α T) T (ty_shrref α T) id id.
  Proof.
    rewrite ty_shrref_unseal. split=>/= >. iIntros "κ t".
    iDestruct 1 as (???[=->]??) "#sT".
    rewrite sem_cif_in /=. iMod (stored_acc with "sT") as "sT'".
    iDestruct (lft_incl'_live_acc α with "κ") as (?) "[α →κ]".
    iMod (copy_shr_acc with "α t sT'") as (??) "(↦ & t & #T & cl)"=>//.
    iModIntro. iDestruct (ty_own_clair with "T") as "$"=>//. iFrame "↦".
    iSplit=>//. iIntros "↦". iMod ("cl" with "↦ t") as "[α $]". iModIntro.
    iDestruct ("→κ" with "α") as "$". iExists _, _, _, _. rewrite sem_cif_in /=.
    by iFrame "sT".
  Qed.
End ty_shrref.
