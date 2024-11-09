(** * Modification type *)

From nola.examples.rust_halt Require Export type.

Implicit Type X Y : xty.

Section ty_mod.
  Context `{!Csem CON JUDG Σ, !Jsem JUDG (iProp Σ), !rust_haltGS CON Σ,
    !rust_haltC CON, !rust_haltJ CON JUDG Σ}.

  (** [ty_mod]: Modification type *)
  Definition ty'_mod_def {X Y} (f : Y → X) (T : ty CON Σ X) : ty' CON Σ Y :=
    (λ t d yπ vl, ty_own T t d (f ∘ yπ) vl,
      λ t d l α yπ, ty_shr T t d l α (f ∘ yπ)).
  Lemma ty'_mod_aux : seal (@ty'_mod_def). Proof. by eexists _. Qed.
  Definition ty'_mod {X Y} := ty'_mod_aux.(unseal) X Y.
  Lemma ty'_mod_unseal : @ty'_mod = @ty'_mod_def.
  Proof. by exact: seal_eq. Qed.
  Definition ty_mod {X Y} (f : Y → X) (T : ty CON Σ X) : ty CON Σ Y :=
    (ty_size T, ty'_mod f T).
  Lemma ty_mod_unseal : @ty_mod = λ _ _ f T, (ty_size T, ty'_mod_def f T).
  Proof. by rewrite /ty_mod ty'_mod_unseal. Qed.

  Context {X Y} {f : X → Y}.

  (** [ty_mod] is size-preserving *)
  #[export] Instance ty_mod_preserv : Preserv (@ty_mod _ _ f).
  Proof.
    move=> ??? /ty_proeqv[?[eqvO eqvS]]. rewrite ty_mod_unseal.
    apply ty_proeqv=>/=. split; [done|]. split=> >; [exact: eqvO|exact: eqvS].
  Qed.
  #[export] Instance ty_mod_proper : Proper ((≡) ==> (≡)) (@ty_mod _ _ f).
  Proof. apply preserv_proper, _. Qed.
  #[export] Instance ty_mod_map_preserv `(!Preserv' PR _ F) :
    Preserv (λ T, @ty_mod _ _ f (F T)).
  Proof. move=> ?*?*. by do 2 f_equiv. Qed.
  #[export] Instance ty_mod_map_productive `(!Productive' PR _ F) :
    Productive (λ T, @ty_mod _ _ f (F T)).
  Proof. move=> ?*?*. by do 2 f_equiv. Qed.

  (** [ty_mod] preserves [Ty] *)
  #[export] Instance ty_mod_ty `{!Ty T} : Ty (ty_mod f T).
  Proof.
    rewrite ty_mod_unseal. split=>/= >. { exact _. }
    { exact: ty_own_size. } { exact: ty_own_depth. } { exact: ty_shr_depth. }
    { move=> eq. apply: ty_own_clair=>/= ?. by rewrite eq. }
    { move=> eq. apply: ty_shr_clair=>/= ?. by rewrite eq. }
  Qed.

  (** [ty_mod] preserves [TyOpAt] *)
  #[export] Instance ty_mod_ty_op `(!TyOpAt T κ d, !Inj (=) (=) f) :
    TyOpAt (ty_mod f T) κ d.
  Proof.
    rewrite ty_mod_unseal. split=>/= >.
    - iIntros "κ T". iMod (ty_own_proph with "κ T") as (???) "[$$]".
      iPureIntro. by eapply proph_dep_unf.
    - iIntros "κα T". iMod (ty_shr_proph with "κα T") as (???) "[$$]".
      iPureIntro. by eapply proph_dep_unf.
    - exact ty_share.
  Qed.

  (** [ty_mod] preserves [Send] *)
  #[export] Instance ty_mod_send `{!Send T} : Send (ty_mod f T).
  Proof. rewrite ty_mod_unseal. move=>/= >. exact: send. Qed.
  (** [ty_mod] preserves [Sync] *)
  #[export] Instance ty_mod_sync `{!Sync T} : Sync (ty_mod f T).
  Proof. rewrite ty_mod_unseal. move=>/= >. exact: sync. Qed.
  (** [ty_mod] preserves [Copy] *)
  #[export] Instance ty_mod_copy `{!Copy T} : Copy (ty_mod f T).
  Proof.
    rewrite ty_mod_unseal. split=>/= >; [exact _|exact: copy_shr_acc].
  Qed.

  (** Subtyping on [ty_mod] *)
  Lemma subty_of_mod {δ T} : ⊢ subty δ (ty_mod f T) T f.
  Proof.
    rewrite subty_unseal ty_mod_unseal. iSplit; iModIntro; by iIntros.
  Qed.
  Lemma subty_to_mod {δ g} `{!Ty T} :
    (∀ x, f (g x) = x) → ⊢ subty δ T (ty_mod f T) g.
  Proof.
    rewrite subty_unseal ty_mod_unseal=> eq. iSplit; iModIntro=>/=.
    - iIntros (????) "T". iApply (ty_own_clair with "T")=>//=.
    - iIntros (?????) "T". iApply (ty_shr_clair with "T")=>//=.
  Qed.

  (** Resolution over [ty_mod] *)
  #[export] Instance resol_mod `(!ResolAt T κ post d) :
    ResolAt (ty_mod f T) κ (post ∘ f) d.
  Proof. rewrite ty_mod_unseal. split=> > /=. exact: resol. Qed.
End ty_mod.
