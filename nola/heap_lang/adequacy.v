(** * Safety adequacy of the program logic *)

From iris.algebra Require Import auth.
From iris.base_logic.lib Require Import mono_nat.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre adequacy.
From nola.heap_lang Require Import proofmode notation.
From iris.prelude Require Import options.
Import WpwNotation.

Class heapGpreS Σ : Type := HeapGpreS {
  heapGpreS_iris :: invGpreS Σ;
  heapGpreS_heap :: gen_heapGpreS loc (option val) Σ;
  heapGpreS_inv_heap :: inv_heapGpreS loc (option val) Σ;
  heapGpreS_proph :: proph_mapGpreS proph_id (val * val) Σ;
  heapGS_step_cnt :: mono_natG Σ;
}.

Definition heapΣ : gFunctors :=
  #[invΣ; gen_heapΣ loc (option val); inv_heapΣ loc (option val);
    proph_mapΣ proph_id (val * val); mono_natΣ].
Global Instance subG_heapGpreS {Σ} : subG heapΣ Σ → heapGpreS Σ.
Proof. solve_inG. Qed.

(** Safety adequacy of the partial weakest precondition *)
Theorem heap_adequacy Σ `{!heapGpreS Σ} hlc s e σ φ :
  (∀ `{!heapGS_gen hlc Σ},
    inv_heap_inv ={⊤}=∗ ∃ W : iProp Σ, W ∗ WP[W] e @ s; ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate s e σ (λ v _, φ v).
Proof.
  move=> big. apply adequate_alt=> ?? /erased_steps_nsteps[?[??]].
  eapply (wpw_strong_adequacy_gen _ Σ _); [|done]=> ?.
  iMod gen_heap_init as (?) "[? _]". iMod inv_heap_init as (?) ">IHI".
  iMod proph_map_init as (?) "?". iMod mono_nat_own_alloc as (?) "[? _]".
  iMod (big (HeapGS _ _ _ _ _ _) with "IHI") as (?) "[??]". iModIntro.
  iExists _, [_], _, _, _=>/=. iFrame. iIntros (??->??) "_ _ H _".
  iApply fupd_mask_intro_discard; [done|]. iSplit; [|done].
  iDestruct (big_sepL2_cons_inv_r with "H") as (?? ->) "[? H]".
  iDestruct (big_sepL2_nil_inv_r with "H") as %->. iIntros (??[=-><-]).
  by rewrite to_of_val.
Qed.
