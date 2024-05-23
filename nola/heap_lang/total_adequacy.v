From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat.
From iris.program_logic Require Export total_adequacy.
From nola.heap_lang Require Export adequacy.
From nola.heap_lang Require Import proofmode notation.
From iris.prelude Require Import options.
Import WpwNotation.

Theorem heap_total Σ `{!heapGpreS Σ} s e σ φ :
  (∀ `{!heapGS_gen HasNoLc Σ},
    inv_heap_inv ={⊤}=∗ ∃ W : iProp Σ, W ∗ WP[W] e @ s; ⊤ [{ v, ⌜φ v⌝ }]) →
  sn erased_step ([e], σ).
Proof.
  move=> big. eapply (twpw_total _ _)=> ?.
  iMod gen_heap_init as (?) "[? _]". iMod inv_heap_init as (?) ">IHI".
  iMod proph_map_init as (?) "?". iMod (mono_nat_own_alloc 0) as (?) "[? _]".
  iMod (big (HeapGS _ _ _ _ _ _) with "IHI") as (?) "[??]". iModIntro.
  iExists _, _, _, _, _. iFrame.
Qed.
