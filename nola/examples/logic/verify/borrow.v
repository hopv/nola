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
      [proph_wsat ∗ borrow_wsatd]
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
  Lemma proph_bor_bor_deref
    {γ X η ξ α β l q} {x : X} {Φ : _ → _ → nPropS (;ᵞ)} :
    [[{ q.[α ⊓ β] ∗ val_obs γ ((x, ξ)' : (X *'ₛ prvarₛ X)) ∗
      bord α (∃ (x : X) ξ γ' (l' : loc),
        n_proph_ctrl γ ((x, ξ)' : (X *'ₛ prvarₛ X)) η ∗ l ↦ #l' ∗
        n_val_obs γ' x ∗ n_bor' [] β (∃ x, n_proph_ctrl γ' x ξ ∗ Φ l' x)) }]]
      [proph_wsat ∗ borrow_wsatd]
      !#l
    [[{ l', RET #l' ; q.[α ⊓ β] ∗ ∃ (ζ : prvar X) γ'',
      ⟨π, π η = (π ζ, ξ)'⟩ ∗ val_obs γ'' x ∗
      bord (α ⊓ β) (∃ x, n_proph_ctrl γ'' x ζ ∗ Φ l' x) }]].
  Proof.
    iIntros "%Ψ [[α β][vo b]] →Ψ". iMod (bor_open with "α b") as "[o big]"=>/=.
    iDestruct "big" as (x2 ξ2 γ' l') "[pc[↦[vo' b']]]".
    iApply twpw_fupdw_nonval; [done|]. wp_load. iModIntro.
    iDestruct (vo_pc_agree with "vo pc") as %eq. case: eq=> <-<-.
    iMod (bor_reborrow α with "β b'") as "[[β β'][b' →b']]". rewrite [β⊓_]comm.
    iMod (obor_subdiv
      [∃ x : X,
        n_proph_ctrl γ ((x, ξ)' : (X *'ₛ prvarₛ X)) η ∗ n_val_obs γ' x]%n
      with "[] o [pc vo'] [↦ →b']") as "[[α α'][c _]]"=>/=.
    { iApply lft_sincl_refl. } { iSplit; [|done]. iExists _. iFrame. }
    { iIntros "† [big _]". iDestruct "big" as (x'') "[pc vo']". iModIntro.
      iExists _, _, _, _. iFrame "↦ vo' pc". by iApply "→b'". }
    iMod (borc_open with "α c") as "[o big]"=>/=.
    iDestruct "big" as (x') "[pc vo']".
    iMod (borc_open with "[α' β] b'") as "[o' big]"; [by iFrame|]=>/=.
    iDestruct "big" as (x'2) "[pc' Φ]".
    iDestruct (vo_pc_agree with "vo' pc'") as %<-.
    iDestruct (vo_pc_agree with "vo pc") as %eq. case: eq=> <-.
    iMod (proph_alloc (X:=X) x) as (ζ) "ζ".
    iMod (vo_pc_preresolve (ξ:=η) (λ π, (π ζ, ξ)') [ζ : aprvarn]
      with "[$ζ//] vo pc") as "[[ζ _][#obs →pc]]".
    { apply (proph_dep_constr (λ x, (x, ξ)')), (proph_dep_one ζ). }
    iMod (vo_pc_alloc with "ζ") as (γ'') "[vo'' pc'']".
    iMod (obor_merge_subdiv [(_,_,_)';(_,_,_)']
      [∃ x, n_proph_ctrl γ'' x ζ ∗ Φ l' x]%n
      with "[$o $o'] [pc'' Φ] [→pc vo' pc']") as "[[α[[α' β] _]][c _]]"=>/=.
    { iSplit; [by iApply lft_sincl_meet_l|].
      iSplit; by [iApply lft_sincl_refl|]. }
    { iSplit; [|done]. iExists _. iFrame. }
    { iIntros "† [big _]". iDestruct "big" as (x'') "[pc'' Φ]".
      iMod (vo_pc_update with "vo' pc'") as "[vo' pc']".
      iMod (pc_resolve with "pc''") as "#obs'". iModIntro. iSplitL "→pc vo'".
      - iExists x''. iFrame "vo'". iApply "→pc".
        by iApply (proph_obs_impl with "obs'")=> ?->.
      - iSplit; [|done]. iExists _. iFrame. }
    iModIntro. iApply "→Ψ". iFrame "α α' β β'". iExists _, _. rewrite borc_bor.
    by iFrame.
  Qed.
End borrow.
