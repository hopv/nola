(** * Singly linked list type *)

From nola.examples.rust_halt Require Export rec mod sum box prod.

Section list.
  Context `{!rust_haltGS CON Σ, !rust_haltC CON, !rust_haltJ CON JUDG Σ,
    !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ), !rust_haltCS CON JUDG Σ,
    !rust_haltJS CON JUDG Σ}.

  (** [list_unwrap]: Unwrap function for the list type *)
  Definition list_unwrap {A} (l : list A) : unit + A *' list A :=
    match l with [] => inl () | a :: l' => inr (a, l')' end.
  (** [list_unwrap] is injective *)
  #[export] Instance list_unwrap_inj {A} : Inj (=) (=) (@list_unwrap A).
  Proof. by move=> [|??][|??]//=[<-<-]. Qed.

  (** [list_wrap]: Wrap function for the list type *)
  Definition list_wrap {A} (s : unit + A *' list A) : list A :=
    match s with inl () => [] | inr (a, l')' => a :: l' end.

  (** [list_wrap] and [list_unwrap] are mutually inverse *)
  Lemma list_wrap_unwrap {A l} : @list_wrap A (list_unwrap l) = l.
  Proof. by case l. Qed.
  Lemma list_unwrap_wrap {A s} : @list_unwrap A (list_wrap s) = s.
  Proof. by case s=> [[]|?]. Qed.

  (** [ty_list_gen]: Generator of the list type *)
  Definition ty_list_gen' {X} (T : ty CON Σ X) (Self : ty CON Σ (listₓ X))
    : ty CON Σ (unitₓ +ₓ X *'ₓ listₓ X) :=
    ty_sum ty_unit (ty_box (ty_prod T Self)).
  Definition ty_list_gen {X} (T : ty CON Σ X) (Self : ty CON Σ (listₓ X))
    : ty CON Σ (listₓ X) :=
    ty_mod (X:=unitₓ +ₓ X *'ₓ listₓ X) (Y:=listₓ X)
      (list_unwrap (A:=X)) (ty_list_gen' T Self).
  (** [ty_list_gen] is productive *)
  #[export] Instance ty_list_gen_productive {X T} :
    Productive (@ty_list_gen X T).
  Proof.
    move=> k ???. apply: ty_mod_preserv. apply: ty_sum_preserv=>//.
    apply ty_box_productive. destruct k=>//=. exact: ty_prod_preserv.
  Qed.

  (** [ty_list]: List type *)
  Definition ty_list {X} (T : ty CON Σ X) : ty CON Σ (listₓ X) :=
    ty_rec (ty_list_gen T).

  (** [ty_list] satisfies [Ty] *)
  #[export] Instance ty_list_ty {X T} : Ty (ty_list (X:=X) T).
  Proof. exact _. Qed.

  (** [ty_list] satisfies [TyOp] *)
  #[export] Instance ty_list_ty_op `(!Ty (X:=X) T, !TyOpLe T κ 1 d) :
    TyOpAt (ty_list T) κ d.
  Proof.
    apply (ty_rec_ty_op (F:=ty_list_gen T) ᵖ[(T, 1)'])=>/=; [|exact _]=> ??[??].
    apply: ty_mod_ty_op. apply: ty_sum_ty_op. apply: ty_box_ty_op=> ??.
    apply: ty_prod_ty_op; by apply ty_op_le.
  Qed.

  (** [ty_list] preserves [Send] *)
  #[export] Instance ty_list_send `{!Send (X:=X) T} : Send (ty_list T).
  Proof. exact _. Qed.
  (** [ty_list] preserves [Sync] *)
  #[export] Instance ty_list_sync `{!Sync (X:=X) T} : Sync (ty_list T).
  Proof. exact _. Qed.

  (** [Resol] over [ty_list] *)
  #[export] Instance resol_list `(!ResolLe (X:=X) T κ post 1 d) :
    ResolAt (ty_list T) κ (λ xl, Forall post xl) d.
  Proof.
    apply (ty_rec_resol (F:=ty_list_gen T) ᵖ[(T, post, 1)'])=>/=; [|exact _].
    move=> ??[??]. eapply resol_post.
    { apply @resol_mod, @resol_sum; [exact: _|]. eapply resol_box=> ??.
      eapply resol_post; [apply @resol_prod; exact: resol_le'|done]. }
    move=>/= [|??]//= ?. by apply Forall_cons.
  Qed.

  (** [Real] over [ty_list] *)
  #[export] Instance real_list `(!RealLe (X:=X) (A:=A) T κ get 1 d) :
    RealAt (ty_list T) κ (λ xl, get <$> xl) d.
  Proof.
    apply (ty_rec_real (F:=ty_list_gen T) ᵖ[(T, existT A get, 1)'])=>/=;
      [|exact _]=> ??[??].
    eapply real_eq.
    { apply @real_mod. eapply (real_compose list_wrap).
      apply @real_sum; [exact: _|]. apply real_box=> ??.
      eapply real_eq; [apply @real_prod; exact: real_le|done]. }
    move=> [|??]//=.
  Qed.
  #[export] Instance real_list_length {X T κ} :
    Real (ty_list (X:=X) T) κ (λ xl, length xl).
  Proof.
    move=> ?. eapply real_eq. { eapply (real_compose length). exact _. }
    move=>/= ?. by rewrite length_map.
  Qed.

  (** Fold and unfold [ty_list] *)
  Lemma ty_list_unfold {X T} :
    ty_list (X:=X) T ≡ ty_list_gen T (ty_list (X:=X) T).
  Proof. exact ty_rec_unfold. Qed.
  Lemma subty_list_fold {X T δ} :
    ⊢ subty δ (ty_list_gen' T (ty_list T)) (ty_list (X:=X) T) list_wrap.
  Proof.
    erewrite subty_proper_fun.
    { iApply subty_trans; [|by iApply subty_rec_fold].
      iApply (subty_to_mod (T:=ty_list_gen' _ _))=> ?. exact list_unwrap_wrap. }
    move=>/= [[]|[??]]//=.
  Qed.
  Lemma subty_list_unfold {X T δ} :
    ⊢ subty δ (ty_list (X:=X) T) (ty_list_gen' T (ty_list T)) list_unwrap.
  Proof.
    erewrite subty_proper_fun.
    { iApply subty_trans; [by iApply subty_rec_unfold|]. iApply subty_of_mod. }
    by case.
  Qed.
End list.
