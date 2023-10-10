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
  nintpGpreS_heap :: heapGpreS Σ;
}.

(** [gFunctors] for [nintpGpreS] *)
Definition nintpΣ : gFunctors :=
  #[agreeΣ (nPropL (;ᵞ)); ninvΣ (nPropS (;ᵞ)); na_ninvΣ (nPropS (;ᵞ));
    na_invΣ; cinvΣ; heapΣ].
#[export] Instance subG_nintpGpreS `{!subG nintpΣ Σ} : nintpGpreS Σ.
Proof. solve_inG. Qed.

(** Adequacy of [wp] over [inv_wsatd] *)
Lemma wp_n_adequacy `{!nintpGpreS Σ} {s e σ φ} :
  (∀ `{!nintpGS Σ}, inv_heap_inv -∗
    WP[inv_wsatd ∗ na_inv_wsatd] e @ s; ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate s e σ (λ v _, φ v).
Proof.
  move=> towp. apply (heap_adequacy Σ HasNoLc)=> ?.
  iMod inv_wsat_alloc as (?) "W". iMod na_inv_wsat_alloc as (?) "W'". iModIntro.
  iExists (inv_wsatd ∗ na_inv_wsatd)%I. iSplitL; [by iSplitL "W"|].
  iApply (towp (NintpGS _ _ _ _ _ _)).
Qed.

(** Adequacy of [twp] over [inv_wsatd] *)
Lemma twp_n_adequacy `{!nintpGpreS Σ} {s e σ φ} :
  (∀ `{!nintpGS Σ}, inv_heap_inv -∗
    WP[inv_wsatd ∗ na_inv_wsatd] e @ s; ⊤ [{ v, ⌜φ v⌝ }]) →
  sn erased_step ([e], σ).
Proof.
  move=> totwp. apply (heap_total Σ s _ _ φ)=> ?.
  iMod inv_wsat_alloc as (?) "W". iMod na_inv_wsat_alloc as (?) "W'". iModIntro.
  iExists (inv_wsatd ∗ na_inv_wsatd)%I. iSplitL; [by iSplitL "W"|].
  iApply (totwp (NintpGS _ _ _ _ _ _)).
Qed.
