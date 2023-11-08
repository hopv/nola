(** * Verification on borrowing *)

From nola.examples.logic Require Export borrow.
From nola.examples.heap_lang Require Export proofmode notation.
From iris.base_logic.lib Require Export ghost_var.

Implicit Type X : nsynty.

Section borrow.
  Context `{!nintpGS Σ}.

  (** Dereference a nested mutable reference *)
  Lemma bor_bor_deref {α β l Φ q} :
    [[{ q.[α ⊓ β] ∗
      bord α (∃ l' : loc, l ↦ #l' ∗ n_bor' [] β (Φ l')) }]]
      [proph_wsat ∗ pborrow_wsatd]
      !#l
    [[{ l', RET #l' ; q.[α ⊓ β] ∗ bord (α ⊓ β) (Φ l') }]].
  Proof.
    iIntros "%Ψ [[α β] b] →Ψ". iMod (bor_open with "α b") as "[o big]"=>/=.
    iDestruct "big" as (l') "[↦ b']". iApply twpw_fupdw_nonval; [done|].
    wp_load. iModIntro. iMod (bor_reborrow α with "β b'") as "[β[b' →b']]".
    rewrite [_⊓_]comm.
    iMod (obor_subdiv [] with "[] o [//] [↦ →b']") as "[α _]"=>/=.
    { iApply lft_sincl_refl. }
    { iIntros "† _". iModIntro. iExists _. iFrame "↦". by iApply "→b'". }
    iModIntro. iApply "→Ψ". rewrite borc_bor. iFrame.
  Qed.

  (** Dereference a nested prophetic mutable reference *)
  Lemma proph_bor_bor_deref {X η ξ α β l q} {x : X} {Φ : _ → _ → nPropS (;ᵞ)} :
    [[{ q.[α ⊓ β] ∗
      pbord α ((x, ξ)' : _ *'ₛ prvarₛ _) η
        (λ '(x', ξ')', ∃ v : val, l ↦ v ∗ n_pbor' [] β x' ξ' (Φ v))%n }]]
      [proph_wsat ∗ pborrow_wsatd]
      !#l
    [[{ v, RET v; q.[α ⊓ β] ∗ ∃ ξ' : prvar X,
      ⟨π, π η = (π ξ', ξ)'⟩ ∗ pborcd (α ⊓ β) x ξ' (Φ v) }]].
  Proof.
    iIntros "%Ψ [[α β] b] →Ψ". iMod (pbor_open with "α b") as "/=[o[%[↦ b']]]".
    iApply twpw_fupdw_nonval; [done|]. wp_load. iModIntro.
    iMod (opbor_pbor_reborrow (λ _, (_,_)' : _ *'ₛ _) with "o β b' [↦]")
      as (?) "[α[β[obs c]]]".
    { iIntros "/=% _ ? !>". iExists _. iFrame. }
    iModIntro. iApply "→Ψ". iFrame "α β". iExists _. iFrame.
  Qed.
End borrow.
