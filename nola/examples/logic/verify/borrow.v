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
      bord α (∃ l' : loc, l ↦ #l' ∗ n_bor' [] β (Φ l')) }]][pborrow_wsatd bupd]
      !#l
    [[{ l', RET #l' ; q.[α ⊓ β] ∗ bord (α ⊓ β) (Φ l') }]].
  Proof.
    iIntros "%Ψ [[α β] b] →Ψ".
    iMod (bor_open (M:=bupd) with "α b") as "[o big]"=>/=.
    iDestruct "big" as (l') "[↦ b']". iApply twpw_fupdw_nonval; [done|].
    wp_load. iModIntro.
    iMod (bor_reborrow (M:=bupd) α with "β b'") as "[β[b' →b']]".
    rewrite [_⊓_]comm.
    iMod (obor_subdiv (M:=bupd) [] with "[] o [//] [↦ →b']") as "[α _]"=>/=.
    { iApply lft_sincl_refl. }
    { iIntros "† _". iModIntro. iExists _. iFrame "↦". by iApply "→b'". }
    iModIntro. iApply "→Ψ". rewrite borc_bor. iFrame.
  Qed.

  (** Dereference a nested prophetic mutable reference *)
  Lemma proph_bor_bor_deref {X η ξ α β l q} {x : X} {Φ : _ → _ → nPropS (;ᵞ)} :
    [[{ q.[α ⊓ β] ∗
      pbord α ((x, ξ)' : _ *'ₛ prvarₛ _) η
        (λ '(x', ξ')', ∃ l' : loc, l ↦ #l' ∗ n_pbor' [] β x' ξ' (Φ l'))%n }]]
      [pborrow_wsatd bupd]
      !#l
    [[{ l', RET #l'; q.[α ⊓ β] ∗ ∃ ξ' : prvar X,
      ⟨π, π η = (π ξ', ξ)'⟩ ∗ pborcd (α ⊓ β) x ξ' (Φ l') }]].
  Proof.
    iIntros "%Ψ [[α β] b] →Ψ".
    iMod (pbor_open (M:=bupd) with "α b") as "/=[o[%[↦ b']]]".
    iApply twpw_fupdw_nonval; [done|]. wp_load. iModIntro.
    iMod (pobor_pbor_reborrow (M:=bupd) (λ _, (_,_)' : _ *'ₛ _)
      with "o β b' [↦]") as (?) "[α[β[obs c]]]".
    { iIntros "/=% _ ? !>". iExists _. iFrame. }
    iModIntro. iApply "→Ψ". iFrame "α β". iExists _. iFrame.
  Qed.
End borrow.
