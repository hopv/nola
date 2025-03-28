(** * More on the list type *)

From nola.examples.rust_halt Require Export core ptrs_more prod_more sum_more
  verify.list.

Implicit Type (X : xty) (v : val).

Section list.
  Context `{!rust_haltGS CON Σ, !rust_haltC CON, !rust_haltJ CON JUDG Σ,
    !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ), !rust_haltCS CON JUDG Σ,
    !rust_haltJS CON JUDG Σ}.

  (** [iter_list]: Iterate over a list *)
  Definition iter_list (sz : nat) : val := rec: "self" ["f"; "l"] :=
    case:: !"l" of [
      #☠;
      "f" ["l" +ₗ #1 +ₗ #0];; "self" ["f"; !("l" +ₗ #1 +ₗ #sz)]
    ].

  (** Predicate transformer for [type_iter_list_mut] *)
  Section pre_iter_list_mut.
    Context {X Yl} (pre : xpred Yl → xpred ((X *'ₓ X) :: Yl)) (post : xpred Yl).
    Fixpoint pre_iter_list_mut (xl xl' : list X) (yl : xlist Yl) : Prop :=
      match xl with
      | [] => xl' = [] → post yl
      | x :: xlt => ∀ x' xlt', xl' = x' :: xlt' →
          pre (pre_iter_list_mut xlt xlt') ((x, x')', yl)'
      end.
    Definition pre_iter_list_mut' : xpred ((listₓ X *'ₓ listₓ X) :: Yl) :=
      λ '((xl, xl')', yl)', pre_iter_list_mut xl xl' yl.
  End pre_iter_list_mut.

  (** Iterate via a mutable reference to a list *)
  Lemma type_iter_list_mut {Yl}
    `(!Ty (X:=X) T, !TyOp T κ, !LftIncl κ α, !Closed [] (of_val f),
      !Proper (pointwise_relation _ impl ==> pointwise_relation _ impl) pre)
    {Γ p} :
    (∀ q, type (Yl:=Yl) κ (q ◁ ty_mutref α T ᵖ:: Γ) (f [q]) (λ _, Γ) pre) ⊢
      type κ (p ◁ ty_mutref α (ty_list T) ᵖ:: Γ)
        (iter_list (ty_size T) [of_val f; p]) (λ _, Γ) (pre_iter_list_mut' pre).
  Proof.
    iIntros "#f".
    iAssert (∀ n p,
      type κ (p ◁ ty_mutref α (ty_list T) ᵖ:: Γ)
        (iter_list (ty_size T) [of_val f; p]) (λ _, Γ)
        (λ post '((xl, xl')', yl)',
          length xl = n ∧ pre_iter_list_mut pre post xl xl' yl)%type)%I
        as "Goal"; last first.
    { iApply type_pre; last first.
      { iApply (type_real p nat (pre_iter_list_mut' pre)). iIntros (n).
        iApply "Goal". } { done. } }
    clear p. iIntros (n p). iInduction n as [|n] "IH" forall (p).
    { iApply type_pre; last first.
      { type_path p as (v). iApply type_call.
        iApply (type_mutref_subty v);
          [|iApply (subty_list_unfold (T:=T))|iApply (subty_list_fold (T:=T))|].
        { move=> ?. exact list_unwrap_wrap. }
        iApply (type_case_sum_mutref v); [|by iApply type_false].
        iApply (type_leak ᵖ[_]); [exact resol_tcx_true|]. iApply type_value. }
      move=>/= ?[[[|??]?]?]/=[? to]//[] /(f_equal list_wrap)/=.
      rewrite list_wrap_unwrap=> ? _. exact: to. }
    iApply type_pre; last first.
    { type_path p as (v). iApply type_call.
      iApply (type_mutref_subty v);
        [|iApply (subty_list_unfold (T:=T))|iApply (subty_list_fold (T:=T))|].
      { move=> ?. exact list_unwrap_wrap. }
      iApply (type_case_sum_mutref v); [by iApply type_false|].
      iApply type_mutref_prod_split. iApply type_seq.
      { iApply (type_frame ᵖ[_ +ₗ #T.1 ◁ _]); [solve_extract|by iApply "f"]. }
      iIntros (?). type_bind (!_)%E; [by iApply type_deref_mutref_box|].
      iIntros (v'). iApply "IH". }
    move=>/= ?[[[|??]?]?]/=[leq to]//=[??] /(f_equal list_wrap)/=.
    rewrite list_wrap_unwrap=> eq. move: (to _ _ eq). apply Proper0=> ??.
    split=>//. by case: leq.
  Qed.

  (** Lemma for [type_iter_list_mut_fun] *)
  Lemma pre_iter_list_mut_fun {X Yl} (g : X → X) {post xl xl' yl} :
    @pre_iter_list_mut X Yl
      (λ post '((x, x')', yl)', x' = g x → post yl) post xl xl' yl ↔
      (xl' = g <$> xl → post yl).
  Proof.
    move: xl' yl. elim: xl=>//= ?? IH xl' yl. split.
    - case: xl'=>//= ?? H [??]. subst. eapply IH; [exact: H|done].
    - move=> H ????. subst. apply IH=> ?. apply H. by f_equal.
  Qed.
  (** [type_iter_list_mut] over a typical predicate transformer that resolves
    the prophecy by some function *)
  Lemma type_iter_list_mut_fun {X} (g : X → X) {Yl}
    `(!Ty (X:=X) T, !TyOp T κ, !LftIncl κ α, !Closed [] (of_val f)) {Γ p} :
    (∀ q, type (Yl:=Yl) κ
      (q ◁ ty_mutref α T ᵖ:: Γ) (f [q]) (λ _, Γ)
        (λ post '((x, x')', yl)', x' = g x → post yl)%type) ⊢
      type κ (p ◁ ty_mutref α (ty_list T) ᵖ:: Γ)
        (iter_list (ty_size T) [of_val f; p]) (λ _, Γ)
          (λ post '((xl, xl')', yl)', xl' = g <$> xl → post yl)%type.
  Proof.
    iIntros "type". iApply type_pre; last first.
    { iApply (type_iter_list_mut with "type"). move=>/= ?? to ? H ?.
      by apply to, H. }
    by move=>/= > /pre_iter_list_mut_fun.
  Qed.
End list.
