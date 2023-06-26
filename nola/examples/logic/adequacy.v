(** * Adequacy *)

From nola.examples.logic Require Export sintp.
From nola.examples.heap_lang Require Export adequacy total_adequacy.

(** Precursor of [nintpGS] *)
Class nintpGpreS (Σ : gFunctors) := NintpGpreS {
  nintpGpreS_ninvGpreS :: ninvGpreS nInvd Σ;
  nintpGpreS_na_invG :: na_invG Σ;
  nintpGpreS_cinvG :: cinvG Σ;
  nintpGpreS_heapGpreS :: heapGpreS Σ;
}.

(** [gFunctors] for [nintpGpreS] *)
Definition nintpΣ : gFunctors := #[ninvΣ nInvd; na_invΣ; cinvΣ; heapΣ].
Global Instance subG_nintpGpreS {Σ} : subG nintpΣ Σ → nintpGpreS Σ.
Proof. solve_inG. Qed.

(** Adequacy of [wp] over [nninv_wsats] *)
Lemma wp_n_adequacy `{!nintpGpreS Σ} {s e σ φ} :
  (∀ `{!nintpGS Σ}, inv_heap_inv -∗ WP[nninv_wsats] e @ s; ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate s e σ (λ v _, φ v).
Proof.
  move=> towp. apply (heap_adequacy Σ HasNoLc)=> ?.
  iMod ninv_wsat_alloc as (?) "?". iModIntro. iExists nninv_wsats.
  iSplitL; [done|]. iApply (towp (NintpGS _ _ _ _)).
Qed.

(** Adequacy of [twp] over [nninv_wsats] *)
Lemma twp_n_adequacy `{!nintpGpreS Σ} {s e σ φ} :
  (∀ `{!nintpGS Σ}, inv_heap_inv -∗ WP[nninv_wsats] e @ s; ⊤ [{ v, ⌜φ v⌝ }]) →
  sn erased_step ([e], σ).
Proof.
  move=> totwp. apply (heap_total Σ s _ _ φ)=> ?.
  iMod ninv_wsat_alloc as (?) "?". iModIntro. iExists nninv_wsats.
  iSplitL; [done|]. iApply (totwp (NintpGS _ _ _ _)).
Qed.
