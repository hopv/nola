(** * Singly linked list over a mutable reference *)

From nola.examples.rust_halt Require Export rec mod sum prod mutref verify.util.

Section mutlist.
  Context `{!rust_haltGS CON Σ, !rust_haltC CON, !rust_haltJ CON JUDG Σ,
    !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ), !rust_haltCS CON JUDG Σ,
    !rust_haltJS CON JUDG Σ}.

  (** [ty_mutlist_gen]: Generator of the [mutlist] type *)
  Definition ty_mutlist_gen' {X} (α : lft) (T : ty CON Σ X)
    (Self : ty CON Σ (binₓ X)) : ty CON Σ (unitₓ +ₓ X *'ₓ binₓ X *'ₓ binₓ X) :=
    ty_sum ty_unit (ty_prod T (ty_mutref α Self)).
  Definition ty_mutlist_gen {X} (α : lft) (T : ty CON Σ X)
    (Self : ty CON Σ (binₓ X)) : ty CON Σ (binₓ X) :=
    ty_mod (X:=unitₓ +ₓ X *'ₓ binₓ X *'ₓ binₓ X) (Y:=binₓ X)
      (bin_unwrap (A:=X)) (ty_mutlist_gen' α T Self).
  (** [ty_mutlist_gen] is productive *)
  #[export] Instance ty_mutlist_gen_productive {α X T} :
    Productive (@ty_mutlist_gen α X T).
  Proof.
    move=> k ???. apply: ty_mod_preserv. apply: ty_sum_preserv=>//.
    apply ty_prod_preserv=>//. exact: ty_mutref_productive.
  Qed.

  (** [ty_mutlist]: List over a mutable reference, modeled as a binary tree *)
  Definition ty_mutlist {X} (α : lft) (T : ty CON Σ X) : ty CON Σ (binₓ X) :=
    ty_rec (ty_mutlist_gen α T).

  (** [ty_mutlist] satisfies [Ty] *)
  #[export] Instance ty_mutlist_ty `{!Ty (X:=X) T} {α} :
    Ty (ty_mutlist α (X:=X) T).
  Proof. exact _. Qed.

  (** [ty_mutlist] satisfies [TyOp] *)
  #[export] Instance ty_mutlist_ty_op
    `(!Ty (X:=X) T, !TyOpLe T κ 0 d, !LftIncl κ α) :
    TyOpAt (ty_mutlist α T) κ d.
  Proof.
    apply (ty_rec_ty_op (F:=ty_mutlist_gen α T) ᵖ[(T, 0)'])=>/=; [|exact _].
    move=> ??[??]. apply: ty_mod_ty_op. apply: ty_sum_ty_op.
    apply: ty_prod_ty_op. exact: ty_op_le.
  Qed.

  (** [ty_mutlist] preserves [Send] *)
  #[export] Instance ty_mutlist_send `{!Send (X:=X) T} {α} :
    Send (ty_mutlist α T).
  Proof. exact _. Qed.
  (** [ty_mutlist] preserves [Sync] *)
  #[export] Instance ty_mutlist_sync `{!Sync (X:=X) T} {α} :
    Sync (ty_mutlist α T).
  Proof. exact _. Qed.

  (** [Resol] over [ty_mutlist] *)
  Definition post_mutlist {A} (post : A → Prop) (t : bin A) :=
    match t with BinLeaf => True | BinNode a tl tr => post a ∧ tr = tl end.
  #[export] Instance resol_mutlist
    `(!Ty (X:=X) T, !TyOp T κ, !ResolAt (X:=X) T κ post d, !LftIncl κ α) :
    ResolAt (ty_mutlist α T) κ (post_mutlist post) d.
  Proof.
    rewrite /ty_mutlist. setoid_rewrite (ty_rec_unfold (F:=ty_mutlist_gen _ _)).
    eapply resol_post.
    { apply @resol_mod, @resol_sum; [exact: _|].
      apply @resol_prod; [exact: _|exact: resol_mutref]. }
    move=>/= [|??]//=.
  Qed.

  (** Left spine of [bin] *)
  Fixpoint bin_lefts {A} (t : bin A) : list A :=
    match t with BinLeaf => [] | BinNode a tl _ => a :: bin_lefts tl end.
  (** [Real] over [ty_mutlist] *)
  #[export] Instance real_mutlist
    `(!LftIncl κ α, !TyOp' X T κ, !RealLe (A:=A) T κ get 0 d) :
    RealAt (ty_mutlist α T) κ (λ t, get <$> bin_lefts t) d.
  Proof.
    apply (ty_rec_real (F:=ty_mutlist_gen α T) ᵖ[(T, existT A get, 0)'])=>/=;
      [|exact _]=> ??[??].
    eapply real_eq.
    { apply @real_mod. eapply (real_compose list_wrap).
      apply @real_sum; [exact: _|].
      apply @real_prod; [exact: real_le|exact: real_mutref]. }
    move=>/= [|???]//=.
  Qed.
  #[export] Instance real_mutlist_length `(!LftIncl κ α, !TyOp' X T κ) :
    Real (ty_mutlist α (X:=X) T) κ (λ t, length (bin_lefts t)).
  Proof.
    move=> ?. eapply real_eq. { eapply (real_compose length). exact _. }
    move=>/= ?. by rewrite length_map.
  Qed.

  (** Fold and unfold [ty_mutlist] *)
  Lemma ty_mutlist_unfold {α X T} :
    ty_mutlist (X:=X) α T ≡ ty_mutlist_gen α T (ty_mutlist (X:=X) α T).
  Proof. exact ty_rec_unfold. Qed.
  Lemma subty_mutlist_fold `{!Ty (X:=X) T} {α δ} :
    ⊢ subty δ (ty_mutlist_gen' α T (ty_mutlist α T)) (ty_mutlist (X:=X) α T)
        bin_wrap.
  Proof.
    erewrite subty_proper_fun.
    { iApply subty_trans; [|by iApply subty_rec_fold].
      iApply (subty_to_mod (T:=ty_mutlist_gen' _ T _))=> ?.
      exact bin_unwrap_wrap. }
    move=>/= [[]|?]//=.
  Qed.
  Lemma subty_mutlist_unfold `{!Ty (X:=X) T} {α δ} :
    ⊢ subty δ (ty_mutlist (X:=X) α T) (ty_mutlist_gen' α T (ty_mutlist α T))
        bin_unwrap.
  Proof.
    erewrite subty_proper_fun.
    { iApply subty_trans; [by iApply subty_rec_unfold|]. iApply subty_of_mod. }
    by case.
  Qed.

  (** Subtyping over [ty_mutlist] *)
  Lemma subty_mutlist `{!Deriv ih δ, !Ty (X:=X) T, !Ty U} {α} :
    (∀ δ', ⌜Deriv ih δ'⌝ → subty δ' T U id ∧ subty δ' U T id) ⊢
      subty δ (ty_mutlist α T) (ty_mutlist α U) id.
  Proof.
    move: T Ty0 U Ty1. apply Deriv_ind. clear dependent δ=> δ ?.
    iIntros (????) "#TU". erewrite subty_proper_fun.
    { iApply subty_trans; [iApply (subty_mutlist_unfold (T:=T))|].
      iApply subty_trans; [|iApply (subty_mutlist_fold (T:=U))].
      iApply (subty_sum (T:=ty_unit) (T':=ty_unit)
        (U:=ty_prod _ (ty_mutref _ (ty_mutlist _ _)))
        (U':=ty_prod _ (ty_mutref _ (ty_mutlist _ _))));
        [by iApply subty_refl|].
      iApply (subty_prod (U:=ty_mutref _ (ty_mutlist _ _))
        (U':=ty_mutref _ (ty_mutlist _ _))).
      { iApply bi.and_elim_l. iApply "TU". iPureIntro.
        by apply Deriv_mono=> ?[_ ?]. }
      iApply subty_mutref. iIntros "!>" (??[IH ?]).
      iSplit; iApply IH; by [|setoid_rewrite bi.and_comm at 2]. }
    move=>/= [|??]//=.
  Qed.
End mutlist.
