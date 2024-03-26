(** * Adequacy *)

From nola.examples.logic Require Export deriv.
From nola.examples.heap_lang Require Export adequacy total_adequacy.

(** Precursor of [nintpGS] *)
Class nintpGpreS Σ := NintpGpreS {
  nintpGpreS_sinv :: sinvGpreS (nPropSO (;ᵞ)) Σ;
  nintpGpreS_ninv :: ninvGpreS (nPropSO (;ᵞ)) Σ;
  nintpGpreS_na_ninv :: na_ninvGpreS (nPropSO (;ᵞ)) Σ;
  nintpGpreS_na_inv :: na_invG Σ;
  nintpGpreS_cinv :: cinvG Σ;
  nintpGpreS_pborrow :: pborrowGpreS nsynty (nPropS (;ᵞ)) Σ;
  nintpGpreS_heap :: heapGpreS Σ;
}.

(** [gFunctors] for [nintpGpreS] *)
Definition nintpΣ : gFunctors :=
  #[sinvΣ (nPropSO (;ᵞ)); ninvΣ (nPropSO (;ᵞ)); na_ninvΣ (nPropSO (;ᵞ));
    na_invΣ; cinvΣ; pborrowΣ nsynty (nPropS (;ᵞ)); heapΣ].
#[export] Instance subG_nintpGpreS `{!subG nintpΣ Σ} : nintpGpreS Σ.
Proof. solve_inG. Qed.

(** Whole world satisfaction *)
Definition nwsatd `{!nintpGS Σ} M : iProp Σ :=
  sinv_wsatd ∗ inv_wsatd ∗ na_inv_wsatd ∗ pborrow_wsatd M.

(** Adequacy of [wp] over [inv_wsatd] *)
Lemma wp_n_adequacy `{!nintpGpreS Σ} {s e σ φ} :
  (∀ `{!nintpGS Σ}, ⊢ ∃ M,
    inv_heap_inv -∗ WP[nwsatd M] e @ s; ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate s e σ (λ v _, φ v).
Proof.
  move=> towp. apply (heap_adequacy Σ HasNoLc)=> ?.
  iMod sinv_wsat_alloc as (?) "W0". iMod inv_wsat_alloc as (?) "W1".
  iMod na_inv_wsat_alloc as (?) "W2". iMod pborrow_wsat_alloc as (?) "W3".
  iModIntro. iDestruct (towp (NintpGS _ _ _ _ _ _ _)) as (M) "big".
  iExists (nwsatd M). iFrame "big". iSplitL "W0"; [done|].
  iSplitL "W1"; [done|]. by iSplitL "W2".
Qed.

(** Adequacy of [twp] over [inv_wsatd] *)
Lemma twp_n_adequacy `{!nintpGpreS Σ} {s e σ φ} :
  (∀ `{!nintpGS Σ}, ⊢ ∃ M,
    inv_heap_inv -∗ WP[nwsatd M] e @ s; ⊤ [{ v, ⌜φ v⌝ }]) →
  sn erased_step ([e], σ).
Proof.
  move=> totwp. apply (heap_total Σ s _ _ φ)=> ?.
  iMod sinv_wsat_alloc as (?) "W0". iMod inv_wsat_alloc as (?) "W1".
  iMod na_inv_wsat_alloc as (?) "W2". iMod pborrow_wsat_alloc as (?) "W3".
  iModIntro. iDestruct (totwp (NintpGS _ _ _ _ _ _ _)) as (M) "big".
  iExists (nwsatd M). iFrame "big". iSplitL "W0"; [done|].
  iSplitL "W1"; [done|]. by iSplitL "W2".
Qed.
