(** * Shared mutable infinite list *)

From nola.examples.type.rules Require Export conv expr ref.

(** Shared mutable infinite list *)
Definition ilist `{! i ≤ⁿ j} {Γᵘ Γᵍ} (T : type i (;ᵞ Γᵘ ++ Γᵍ))
  : type j (Γᵘ;ᵞ Γᵍ) :=
  recᵗ: i, ref{i,_::_}: ¢ᵍ T ∧ᵗ ref{i,_::_}[1] %ᵍ !0 _.

Section verify.
  Context `{!tintpGS L Σ}.

  (** Type conversion on [ilist] *)
  Lemma teqv_ilist_expand `{! i ≤ⁿ j} {d} {T : _ i (;ᵞ)} :
    ilist T ≃{j,i}(d) ref: T ∧ᵗ ref[1] ilist (j:=i) T.
  Proof.
    eapply teqv_trans; [apply teqv_rec_expand|]=>/=.
    by erewrite (proof_irrel (nle_trans _ _) _).
  Qed.
  Lemma teqv_ilist_lev `{! i ≤ⁿ j, ! i ≤ⁿ k} {d} {T : _ i (;ᵞ)} :
    ilist T ≃{j,k}(d) ilist T.
  Proof. exact teqv_rec_lev. Qed.

  (** Verify [fiter] over [ilist] *)
  Lemma texpr_fiter_ilist `{! i <ⁿ j, ! i ≤ⁿ j} {T} :
    ⊢ (λ: "f", fiter (λ: "l", "f" "l";; !("l" +ₗ # 1))) :ᵉ{j}(0)
        ((ref{i,_}: T →(j) ref: T) →(0) (ℕ × ilist T →(j) ilist T)).
  Proof.
    iApply (texpr_fun_intro (i:=0)). iIntros "/=!> %f #f".
    iApply (texpr_fun_fiter (i:=j) (j:=j)).
    iApply (texpr_fun_intro (i:=j)). iIntros "/=!> %il #il".
    rewrite (tobj_teqv (v:=il)); [|apply teqv_ilist_expand]. iApply texpr_seq.
    { iApply (texpr_fun_call (i:=j) (j:=j)); iApply texpr_val; [done|].
      iApply tobj_tsub; [|done].
      eapply tsub_trans; [apply tsub_and_elim_l|apply tsub_ref_lev]. }
    rewrite texpr_teqv; [|apply (teqv_ilist_lev (k:=i))].
    iApply texpr_ref_load. iApply texpr_ref_off. iApply texpr_val.
    iApply tobj_tsub; [|done]. apply tsub_and_elim_r.
  Qed.
End verify.
