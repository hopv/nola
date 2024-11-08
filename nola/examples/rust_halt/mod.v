(** * Modification type *)

From nola.examples.rust_halt Require Export type.

Implicit Type X Y : xty.

(** ** Modification type *)

Definition ty_mod {CON Σ X Y} (f : Y → X) (T : ty CON Σ X) : ty CON Σ Y :=
  (λ t d yπ vl, T.1 t d (f ∘ yπ) vl, λ t d l α yπ, T.2 t d l α (f ∘ yπ)).

Section ty_mod.
  Context `{!Csem CON JUDG Σ, !Jsem JUDG (iProp Σ), !rust_haltGS CON Σ,
    !rust_haltC CON, !rust_haltJ CON JUDG Σ, !rust_haltJS CON JUDG Σ}.
  Context {X Y} {f : X → Y} {T : ty CON Σ Y}.

  (** [ty_mod] is size-preserving *)
  #[export] Instance ty_mod_preserv : Preserv (@ty_mod CON Σ _ _ f).
  Proof.
    move=> ?[??][??][/=eqvO eqvS]. split=>/= >; [apply eqvO|apply eqvS].
  Qed.
  #[export] Instance ty_mod_map_preserv `{!Preserv' (ty CON Σ X') _ F} :
    Preserv (λ T, @ty_mod CON Σ _ _ f (F T)).
  Proof. solve_proper. Qed.
  #[export] Instance ty_mod_map_productive `{!Productive' (ty CON Σ X') _ F} :
    Productive (λ T, @ty_mod CON Σ _ _ f (F T)).
  Proof. solve_proper. Qed.

  (** [ty_mod] preserves [Ty] *)
  #[export] Instance ty_mod_ty `{!Ty T sz} : Ty (ty_mod f T) sz.
  Proof.
    split=>/= >. { exact _. } { exact: ty_own_size. }
    { exact: ty_own_depth. } { exact: ty_shr_depth. }
    { move=> eq. apply: ty_own_clair=>/= ?. by rewrite eq. }
    { move=> eq. apply: ty_shr_clair=>/= ?. by rewrite eq. }
  Qed.

  (** [ty_mod] preserves [TyOpAt] *)
  #[export] Instance ty_mod_ty_op `{!TyOpAt T β d, !Inj (=) (=) f} :
    TyOpAt (ty_mod f T) β d.
  Proof.
    split=>/= >.
    - iIntros "β T". iMod (ty_own_proph with "β T") as (???) "[$$]".
      iPureIntro. by eapply proph_dep_unf.
    - iIntros "αβ T". iMod (ty_shr_proph with "αβ T") as (???) "[$$]".
      iPureIntro. by eapply proph_dep_unf.
    - exact ty_share.
  Qed.

  (** [ty_mod] preserves [Send] *)
  #[export] Instance ty_mod_send `{!Send T} : Send (ty_mod f T).
  Proof. move=>/= ????. apply: send. Qed.
  (** [ty_mod] preserves [Sync] *)
  #[export] Instance ty_mod_sync `{!Sync T} : Sync (ty_mod f T).
  Proof. move=>/= ??????. apply: sync. Qed.
  (** [ty_mod] preserves [Copy] *)
  #[export] Instance ty_mod_copy `{!Copy T} : Copy (ty_mod f T).
  Proof.
    split=>/= >. { exact: copy_persistent. } { exact: copy_shr_acc. }
  Qed.

  (** Subtyping on [ty_mod] *)
  Lemma subty_of_ty_mod {δ} : ⊢ subty δ (ty_mod f T) T f.
  Proof. rewrite subty_unseal. iSplit; iModIntro; by iIntros. Qed.
  Lemma subty_to_ty_mod {δ g} `{!Ty T sz} :
    (∀ x, f (g x) = x) → ⊢ subty δ T (ty_mod f T) g.
  Proof.
    rewrite subty_unseal=> eq. iSplit; iModIntro=>/=.
    - iIntros (????) "T". iApply (ty_own_clair with "T")=>//=.
    - iIntros (?????) "T". iApply (ty_shr_clair with "T")=>//=.
  Qed.
End ty_mod.
