(** * More on [mutlist] *)

From nola.examples.rust_halt Require Export verify.mutlist ptrs_more prod_more
  sum_more core.

Implicit Type (X : xty) (v : val).

Section mutlist.
  Context `{!rust_haltGS CON Σ, !rust_haltC CON, !rust_haltJ CON JUDG Σ,
    !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ), !rust_haltCS CON JUDG Σ,
    !rust_haltJS CON JUDG Σ}.

  (** [iter_mutlist]: Iterate over [mutlist] *)
  Definition iter_mutlist (sz : nat) : val := rec: "self" ["f"; "l"] :=
    case! !"l" of [
      #☠;
      "f" ["l" +ₗ #1 +ₗ #0];; "self" ["f"; !("l" +ₗ #1 +ₗ #sz)]
    ].

  (** Predicate transformer for [type_iter_mutlist_mut] *)
  Section pre_iter_mutlist_mut.
    Context {X Yl} (pre : xpred Yl → xpred ((X *'ₓ X) :: Yl)) (post : xpred Yl).
    Fixpoint pre_iter_mutlist_mut (xt xt' : bin X) (yl : xlist Yl) : Prop :=
      match xt with
      | BinLeaf => xt' = BinLeaf → post yl
      | BinNode x xtl xtr => ∀ x' xtl' xtr', xt' = BinNode x' xtl' xtr' →
          pre (λ yl, xtr' = xtr → pre_iter_mutlist_mut xtl xtl' yl)
            ((x, x')', yl)'
      end.
    Definition pre_iter_mutlist_mut' : xpred ((binₓ X *'ₓ binₓ X) :: Yl) :=
      λ '((xt, xt')', yl)', pre_iter_mutlist_mut xt xt' yl.
  End pre_iter_mutlist_mut.

  (** Iterate via a mutable reference to a list *)
  Lemma type_iter_mutlist_mut {Yl}
    `(!Ty (X:=X) T, !TyOp T κ, !LftIncl κ α, !LftIncl κ β,
      !Closed [] (of_val f),
      !Proper (pointwise_relation _ impl ==> pointwise_relation _ impl) pre)
    {Γ p} :
    α ⊑□ β -∗
    (∀ q, type (Yl:=Yl) κ (q ◁ ty_mutref α T ᵖ:: Γ) (f [q]) (λ _, Γ) pre) -∗
      type κ (p ◁ ty_mutref α (ty_mutlist β T) ᵖ:: Γ)
        (iter_mutlist (ty_size T) [of_val f; p]) (λ _, Γ)
        (pre_iter_mutlist_mut' pre).
  Proof.
    iIntros "#⊑ #f".
    iAssert (∀ n p,
      type κ (p ◁ ty_mutref α (ty_mutlist β T) ᵖ:: Γ)
        (iter_mutlist (ty_size T) [of_val f; p]) (λ _, Γ)
        (λ post '((xt, xt')', yl)', length (bin_lefts xt) = n ∧
          pre_iter_mutlist_mut pre post xt xt' yl)%type)%I
        as "Goal"; last first.
    { iApply type_pre; last first.
      { iApply (type_real p nat (pre_iter_mutlist_mut' pre)). iIntros (n).
        iApply "Goal". } { done. } }
    clear p. iIntros (n p). iInduction n as [|n] "IH" forall (p).
    { iApply type_pre; last first.
      { type_path p as (v). iApply type_call.
        iApply (type_mutref_subty v);
          [|iApply (subty_mutlist_unfold (T:=T))|
            iApply (subty_mutlist_fold (T:=T))|].
        { move=> ?. exact bin_unwrap_wrap. }
        iApply (type_case_sum_mutref v); [|by iApply type_false].
        iApply (type_leak ᵖ[_]). iApply type_value. }
      move=>/= ?[[[|???]?]?]/=[? to]//[] /(f_equal bin_wrap)/=.
      rewrite bin_wrap_unwrap=> ? _. exact: to. }
    iApply type_pre; last first.
    { type_path p as (v). iApply type_call.
      iApply (type_mutref_subty v);
        [|iApply (subty_mutlist_unfold (T:=T))|
          iApply (subty_mutlist_fold (T:=T))|].
      { move=> ?. exact bin_unwrap_wrap. }
      iApply (type_case_sum_mutref v); [by iApply type_false|].
      iApply type_mutref_prod_split. iApply type_seq.
      { iApply (type_frame ᵖ[_]); [|by iApply "f"].
        apply: tcx_extract_cons; [|exact _]. exact: etcx_extract_tl. }
      iIntros (?). type_bind (!_)%E; [by iApply type_deref_mutref_mutref|].
      iIntros (v'). iApply type_subty; [|by iApply "IH"].
      iApply (subty_mutref_lft (T:=ty_mutlist _ T)).
      iApply lft_sincl_meet_intro; by [iApply lft_sincl_refl|]. }
    move=>/= ?[[[|???]?]?]/=[leq to]//=[?[??]] /(f_equal bin_wrap)/=.
    rewrite bin_wrap_unwrap=> eq. move: (to _ _ _ eq). apply Proper0=> ? H eq'.
    move: (H eq')=> ?. split=>//. by case: leq.
  Qed.

  (** Lemma for [type_iter_mutlist_mut_fun] *)
  Lemma pre_iter_mutlist_mut_fun {X Yl} (g : X → X) {post xt xt' yl} :
    @pre_iter_mutlist_mut X Yl
      (λ post '((x, x')', yl)', x' = g x → post yl) post xt xt' yl ↔
      (xt' = bin_lspine_map g xt → post yl).
  Proof.
    move: xt' yl. elim: xt=>//= ?? IH ? _ xt' yl. split.
    - case: xt'=>//= ??? H [???]. subst. eapply IH; [exact: H|done].
    - move=> H ??????. subst. apply IH=> ?. apply H. by f_equal.
  Qed.
  (** [type_iter_mutlist_mut] over a typical predicate transformer that resolves
    the prophecy by some function *)
  Lemma type_iter_mutlist_mut_fun {X} (g : X → X) {Yl}
    `(!Ty (X:=X) T, !TyOp T κ, !LftIncl κ α, !LftIncl κ β,
      !Closed [] (of_val f)) {Γ p} :
    α ⊑□ β -∗
    (∀ q, type (Yl:=Yl) κ
      (q ◁ ty_mutref α T ᵖ:: Γ) (f [q]) (λ _, Γ)
        (λ post '((x, x')', yl)', x' = g x → post yl)%type) -∗
      type κ (p ◁ ty_mutref α (ty_mutlist β T) ᵖ:: Γ)
        (iter_mutlist (ty_size T) [of_val f; p]) (λ _, Γ)
          (λ post '((xt, xt')', yl)', xt' = bin_lspine_map g xt → post yl)%type.
  Proof.
    iIntros "#⊑ type". iApply type_pre; last first.
    { iApply (type_iter_mutlist_mut with "⊑ type"). move=>/= ?? to ? H ?.
      by apply to, H. }
    by move=>/= > /pre_iter_mutlist_mut_fun.
  Qed.
End mutlist.
