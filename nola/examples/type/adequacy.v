(** * Adequacy *)

From nola.examples.type Require Export deriv.
From nola.examples.heap_lang Require Export adequacy total_adequacy.

(** [tinvGpreS']: Product of [ninvGpreS (tinvd ?) Σ] over [[o..o+i]] *)
Fixpoint tinvGpreS' (L o : nat) Σ : Type :=
  match L with 0 => unit | S L =>
    ninvGpreS (tinvd o) Σ *' tinvGpreS' L (S o) Σ
  end.
Arguments tinvGpreS' : simpl never.
Existing Class tinvGpreS'.
Notation tinvGpreS L Σ := (tinvGpreS' L 0 Σ).
#[export] Instance tinvGpreS'_S_ninvGpreS' `{tΣ : !tinvGpreS' (S L) o Σ}
  : ninvGpreS (tinvd o) Σ := tΣ.1'.
#[export] Instance tinvGpreS'_S_tinvGpreS' `{tΣ : !tinvGpreS' (S L) o Σ}
  : tinvGpreS' L (S o) Σ := tΣ.2'.

(** Precursor of [tintpGS] *)
Class tintpGpreS L (Σ : gFunctors) := TintpGpreS {
  tintpGpreS_tinvGpreS :: tinvGpreS L Σ;
  tintpGpreS_heapGpreS :: heapGpreS Σ;
}.

(** [gFunctors] for [tinvGpreS] *)
Fixpoint tinvΣ' L o : gFunctors :=
  match L with 0 => #[] | S L => #[ninvΣ (tinvd o); tinvΣ' L (S o)] end.
Notation tinvΣ L := (tinvΣ' L 0).
#[export] Instance subG_tinvGpreS' `{sΣ : !subG (tinvΣ' L o) Σ} :
  tinvGpreS' L o Σ.
Proof.
  move: o sΣ. elim: L; [done|]=>/= L IH o /subG_inv[? /subG_inv[? _]].
  split; [exact _|by apply IH].
Qed.
#[export] Instance subG_tinvGpreS `{sΣ : !subG (tinvΣ L) Σ} : tinvGpreS L Σ.
Proof. exact _. Qed.

(** [gFunctors] for [tintpGpreS] *)
Definition tintpΣ L : gFunctors := #[tinvΣ L; heapΣ].
#[export] Instance subG_tintpGpreS `{!subG (tintpΣ L) Σ} : tintpGpreS L Σ.
Proof. solve_inG. Qed.

(** Allocate [tinv_wsat'] *)
Lemma tinv_wsat''_alloc `{!heapGS_gen HasNoLc Σ, tpreΣ : !tinvGpreS' L o Σ} :
  ⊢ |==> ∃ _ : tinvGS' L o Σ, ∀ intp, tinv_wsat'' L L o _ intp.
Proof.
  move: L o tpreΣ. elim=> [|L IH] o tpreΣ. { iModIntro. by iExists (). }
  iMod (ninv_wsat_alloc (PROP:=tinvd o)) as (nΣ) "nw". iMod IH as (tΣ) "tw".
  iModIntro. iExists (nΣ, tΣ)'. iIntros (intp). by iSplitL "nw".
Qed.
Lemma tinv_wsat'_alloc `{!heapGS_gen HasNoLc Σ, !tinvGpreS L Σ} :
  ⊢ |==> ∃ _ : tinvGS L Σ, ∀ intp, tinv_wsat' L intp.
Proof. iMod tinv_wsat''_alloc as (?) "?". iExists _. by iIntros "!>" (?). Qed.

(** Adequacy of [texpr] *)
Lemma texpr_adequacy `{!tintpGpreS L Σ} {e i T σ} :
  (∀ `{!tintpGS L Σ}, ⊢ e :ᵉ{i}(L) T) → sn erased_step ([e], σ).
Proof.
  move=> totwp. eapply (heap_total _ _ _ _ (λ _, True))=> ?.
  iMod tinv_wsat'_alloc as (?) "tw". iModIntro. iExists (tinv_wsatd L).
  iSplitL; [done|]. iIntros "_".
  iApply twp_mono; [|iApply (totwp (TintpGS _ _))]. by iIntros.
Qed.
