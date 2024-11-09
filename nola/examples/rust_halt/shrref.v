(** * Shared reference type *)

From nola.examples.rust_halt Require Export ptr.

Implicit Type l : loc.

Section ty_shrref.
  Context `{!rust_haltGS CON Σ, !rust_haltC CON, !rust_haltJ CON JUDG Σ,
    !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ), !rust_haltCS CON JUDG Σ,
    !rust_haltJS CON JUDG Σ}.

  (** [ty_shrref]: Shared reference type *)
  Definition sty_shrref_def {X} (α : lft) (T : ty CON Σ X) : sty CON Σ X :=
    λ t d xπ vl, (∃ l d' xπ', ⌜vl = [ #l]⌝ ∗ ⌜d' < d⌝ ∗ ⌜∀ π, xπ' π = xπ π⌝ ∗
      □ cif_store (T.2 t d' l α xπ'))%cif.
  Lemma sty_shrref_aux : seal (@sty_shrref_def). Proof. by eexists _. Qed.
  Definition sty_shrref {X} := sty_shrref_aux.(unseal) X.
  Lemma sty_shrref_unseal : @sty_shrref = @sty_shrref_def.
  Proof. exact: seal_eq. Qed.
  Definition ty_shrref {X} (α : lft) (T : ty CON Σ X) : ty CON Σ X :=
    ty_sty (sty_shrref α T).

  (** [ty_shrref] is productive *)
  #[export] Instance ty_shrref_productive {X α} :
    Productive (ty_shrref (X:=X) α).
  Proof.
    move=> ??? /ty_proeq_later [_ eq]. unfold ty_shrref. f_equiv.
    rewrite sty_shrref_unseal /sty_shrref_def=>/= >. do 3 f_equiv=> ?.
    by rewrite eq.
  Qed.

  (** [sty_shrref] satisfies [Sty] *)
  #[export] Instance sty_shrref_sty {X α T} : Sty (sty_shrref (X:=X) α T) 1.
  Proof.
    rewrite sty_shrref_unseal. split=>/= *. { exact _. }
    { by iIntros "(% & % & % & -> & _)". }
    { (do 9 f_equiv)=> ?. lia. } { (do 10 f_equiv)=> eq ?. by rewrite eq. }
  Qed.

  (** [ty_shrref] satisfies [TyOp] *)
  #[export] Instance ty_shrref_ty_op `{!Ty (X:=X) T sz}
    `(!TyOpLt T κ d, !LftIncl κ α) :
    TyOpAt (ty_shrref α T) κ d.
  Proof.
    apply: sty_op_at=> >. rewrite sty_shrref_unseal /=.
    iIntros "κ". iDestruct 1 as (??? -> ??) "#T". rewrite sem_cif_in /=.
    iMod (stored_acc with "T") as "{T}T".
    iDestruct (lft_incl'_live_acc (α:=κ ⊓ α) with "κ") as (?) "[κα →κ]".
    iMod (ty_shr_proph_lt with "κα T") as (???) "[$ →T]"=>//. iModIntro.
    iSplit. { iPureIntro. by eapply proph_dep_proper. }
    iIntros "ξl". iMod ("→T" with "ξl") as "[κα T]".
    iDestruct ("→κ" with "κα") as "$". iMod (store_alloc_pers with "T") as "T".
    iModIntro. iExists _, _, _. rewrite sem_cif_in /=. by iFrame.
  Qed.

  (** [ty_shrref] is [Send] when the body type is [Sync] *)
  #[export] Instance ty_shrref_send `{!Sync (X:=X) T} {α} :
    Send (ty_shrref α T).
  Proof.
    move=>/= >. rewrite sty_shrref_unseal /sty_shrref_def. do 3 f_equiv=> ?.
    do 5 f_equiv. apply: sync.
  Qed.
  (** [ty_shrref] preserves [Sync] *)
  #[export] Instance ty_shrref_sync `{!Sync (X:=X) T} {α} :
    Sync (ty_shrref α T).
  Proof. exact _. Qed.

  (** [ty_shrref] satisfies [Copy] *)
  #[export] Instance ty_shrref_copy {X α T} : Copy (ty_shrref (X:=X) α T) 1.
  Proof. exact _. Qed.

  (** Subtyping over [ty_shrref] *)
  Lemma subty_ty_shrref `{!Deriv ih δ} {X Y T U f α} :
    □ (∀ δ', ⌜Deriv ih δ'⌝ -∗ ⌜ih δ'⌝ -∗ subty (X:=X) (Y:=Y) δ' T U f) ⊢
      subty δ (ty_shrref α T) (ty_shrref α U) f.
  Proof.
    rewrite -subty_sty sty_shrref_unseal. iIntros "#tosub !>/=" (????).
    iDestruct 1 as (???) "($ & $ & %eq & #T)". iExists _.
    rewrite !sem_cif_in /=. iSplit. { iPureIntro=> ?. by rewrite -eq. }
    iModIntro. iApply (store_wand with "[] T"). iIntros (????) "{T}T !>".
    rewrite subty_unseal. by iApply ("tosub" with "[//] [//]").
  Qed.

  (** Read a copyable object from [ty_shrref] *)
  Lemma read_ty_shrref `{!Ty (X:=X) T sz, !Copy T sz, !LftIncl κ α} {d} :
    Read κ (S d) (ty_shrref α T) d T (ty_shrref α T) id id.
  Proof.
    split=>/= >. iIntros "κ t". rewrite sty_shrref_unseal /=.
    iDestruct 1 as (???[= ->]??) "#sT".
    rewrite sem_cif_in /=. iMod (stored_acc with "sT") as "sT'".
    iDestruct (lft_incl'_live_acc (α:=α) with "κ") as (?) "[α →κ]".
    iMod (copy_shr_acc with "α t sT'") as (??) "(↦ & t & #T & cl)"=>//.
    iModIntro. iDestruct (ty_own_depth (d':=d) with "T") as "T'"; [lia|].
    iDestruct (ty_own_clair with "T'") as "$"=>//. iFrame "↦".
    iSplit=>//. iIntros "↦". iMod ("cl" with "↦ t") as "[α $]". iModIntro.
    iDestruct ("→κ" with "α") as "$". iExists _, _, _. rewrite sem_cif_in /=.
    by iFrame "sT".
  Qed.
End ty_shrref.