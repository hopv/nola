(** ** Adequacy of the program logic *)

From iris.program_logic Require Export adequacy weakestpre.
From iris.algebra Require Import auth.
From nola.rust_lang Require Export heap.
From nola.rust_lang Require Import proofmode notation.
From iris.prelude Require Import options.
Import WpwNotation.

Class lrustGpreS Σ : Type := HeapGpreS {
  lrustGpreS_inv :: invGpreS Σ;
  lrustGpreS_heap :: inG Σ (authR heapUR);
  lrustGpreS_heap_freeable :: inG Σ (authR heap_freeableUR)
}.

Definition lrustΣ : gFunctors :=
  #[invΣ;
    GFunctor (constRF (authR heapUR));
    GFunctor (constRF (authR heap_freeableUR))].
Global Instance subG_lrustGpreS {Σ} : subG lrustΣ Σ → lrustGpreS Σ.
Proof. solve_inG. Qed.

(** Partial correctness adequacy *)
Theorem lrust_adequacy `{!lrustGpreS Σ} {hlc s e σ φ} :
  (∀ `{!lrustGS_gen hlc Σ}, own heap_name (◯ to_heap σ) ={⊤}=∗
    ∃ W : iProp Σ, W ∗ WP[W] e @ s; ⊤ {{ v,
      ∀ σ', own heap_name (● to_heap σ') -∗ W ={⊤,∅}=∗ ⌜φ v σ'⌝ }}) →
  adequate s e σ φ.
Proof.
  move=> big. apply adequate_alt=> ?? /erased_steps_nsteps[?[??]].
  eapply (wpw_strong_adequacy_gen hlc Σ _); [|done]=> Hinv.
  iMod (own_alloc (● to_heap σ ⋅ ◯ to_heap σ)) as (vγ) "[? ◯σ]".
  { apply auth_both_valid. split=>//. exact: to_heap_valid. }
  iMod (own_alloc (● (∅ : heap_freeableUR))) as (fγ) "?";
    first by apply auth_auth_valid.
  set Hheap := HeapGS _ _ _ vγ fγ.
  iMod (big (LRustGS _ _ Hinv Hheap) with "◯σ") as (W) "[??]". iModIntro.
  iExists _, [_], _, _, _=>/=. iFrame. iSplit; [done|].
  iIntros (??->??) "W [%[●σ' _]] H _".
  iDestruct (big_sepL2_cons_inv_r with "H") as (e' ? ->) "[→φ H]".
  iDestruct (big_sepL2_nil_inv_r with "H") as %->=>/=. case eq: (to_val e')=>/=.
  - iMod ("→φ" with "●σ' W") as %?. iModIntro. iSplit; [|done].
    iIntros (??[=-><-]). move: eq. rewrite to_of_val=> [[->]]. by iPureIntro.
  - iApply fupd_mask_intro_discard; [done|]. iSplit; [|done]. iPureIntro.
    move=> ??[??]. subst. move: eq. by rewrite to_of_val.
Qed.

(** Termination adequacy *)
Theorem lrust_total `{!lrustGpreS Σ} {s e σ} :
  (∀ `{!lrustGS_gen HasNoLc Σ}, own heap_name (◯ to_heap σ) ={⊤}=∗
    ∃ W Φ, W ∗ WP[W] e @ s; ⊤ [{ Φ }]) →
  sn erased_step ([e], σ).
Proof.
  move=> big. eapply (twpw_total _ _ _ _ _ 0)=> Hinv.
  iMod (own_alloc (● to_heap σ ⋅ ◯ to_heap σ)) as (vγ) "[? ◯σ]".
  { apply auth_both_valid. split=>//. exact: to_heap_valid. }
  iMod (own_alloc (● (∅ : heap_freeableUR))) as (fγ) "?";
    first by apply auth_auth_valid.
  set Hheap := HeapGS _ _ _ vγ fγ.
  iMod (big (LRustGS _ _ Hinv Hheap) with "◯σ") as (??) "[??]". iModIntro.
  iExists _, _, _, _, _. by iFrame.
Qed.
