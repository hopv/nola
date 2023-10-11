(** * Adequacy *)

From nola.examples.logic Require Export deriv.
From nola.examples.heap_lang Require Export adequacy total_adequacy.

(** Precursor of [nintpGS] *)
Class nintpGpreS Σ := NintpGpreS {
  nintpGpreS_agree :: agreeG (nPropL (;ᵞ)) Σ;
  nintpGpreS_ninv :: ninvGpreS (nPropS (;ᵞ)) Σ;
  nintpGpreS_na_ninv :: na_ninvGpreS (nPropS (;ᵞ)) Σ;
  nintpGpreS_na_inv :: na_invG Σ;
  nintpGpreS_cinv :: cinvG Σ;
  nintpGpreS_borrow :: borrowGpreS (nPropS (;ᵞ)) Σ;
  nintpGpreS_fborrow :: fborrowGpreS (nPropS (;ᵞ)) Σ;
  nintpGpreS_proph :: prophGpreS nsynty Σ;
  nintpGpreS_heap :: heapGpreS Σ;
}.

(** [gFunctors] for [nintpGpreS] *)
Definition nintpΣ : gFunctors :=
  #[agreeΣ (nPropL (;ᵞ)); ninvΣ (nPropS (;ᵞ)); na_ninvΣ (nPropS (;ᵞ));
    na_invΣ; cinvΣ; borrowΣ (nPropS (;ᵞ)); fborrowΣ (nPropS (;ᵞ));
    prophΣ nsynty; heapΣ].
#[export] Instance subG_nintpGpreS `{!subG nintpΣ Σ} : nintpGpreS Σ.
Proof. solve_inG. Qed.

(** Whole world satisfaction *)
Definition nwsatd `{!nintpGS Σ} W E c : iProp Σ :=
  inv_wsatd ∗ na_inv_wsatd ∗ borrow_wsatd W E ∗ fborrow_wsat c.

(** Adequacy of [wp] over [inv_wsatd] *)
Lemma wp_n_adequacy `{!nintpGpreS Σ} {s e σ φ} :
  (∀ `{!nintpGS Σ}, ⊢ ∃ W E c, proph_ctx -∗ inv_heap_inv -∗
    WP[nwsatd W E c] e @ s; ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate s e σ (λ v _, φ v).
Proof.
  move=> towp. apply (heap_adequacy Σ HasNoLc)=> ?.
  iMod inv_wsat_alloc as (?) "W0". iMod na_inv_wsat_alloc as (?) "W1".
  iMod borrow_wsat_alloc as (?) "W2". iMod fborrow_wsat_alloc as (?) "W3".
  iMod proph_init as (?) "PROPH"; [done|]. iModIntro.
  iDestruct (towp (NintpGS _ _ _ _ _ _ _ _ _)) as (W E c) "big".
  iExists (nwsatd W E c). iDestruct ("big" with "PROPH") as "$".
  iSplitL "W0"; [done|]. iSplitL "W1"; [done|]. by iSplitL "W2".
Qed.

(** Adequacy of [twp] over [inv_wsatd] *)
Lemma twp_n_adequacy `{!nintpGpreS Σ} {s e σ φ} :
  (∀ `{!nintpGS Σ}, ⊢ ∃ W E c, proph_ctx -∗ inv_heap_inv -∗
    WP[nwsatd W E c] e @ s; ⊤ [{ v, ⌜φ v⌝ }]) →
  sn erased_step ([e], σ).
Proof.
  move=> totwp. apply (heap_total Σ s _ _ φ)=> ?.
  iMod inv_wsat_alloc as (?) "W0". iMod na_inv_wsat_alloc as (?) "W1".
  iMod borrow_wsat_alloc as (?) "W2". iMod fborrow_wsat_alloc as (?) "W3".
  iMod proph_init as (?) "PROPH"; [done|]. iModIntro.
  iDestruct (totwp (NintpGS _ _ _ _ _ _ _ _ _)) as (W E c) "big".
  iExists (nwsatd W E c). iDestruct ("big" with "PROPH") as "$".
  iSplitL "W0"; [done|]. iSplitL "W1"; [done|]. by iSplitL "W2".
Qed.
