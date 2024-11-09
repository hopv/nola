(** * Borrow examples *)

From nola.examples Require Export xty con.
From nola.rust_lang Require Export notation proofmode.
Import ProdNotation FunPRNotation ModwNotation WpwNotation CsemNotation
  LftNotation ProphNotation XtyNotation.

Section borrow.
  Context `{!Csem CON JUDG Σ, !Jsem JUDG (iProp Σ), !lrustGS_gen hlc Σ,
    !borrowGS (cifOF CON) Σ, !bor_tokC CON, !bor_tokCS CON JUDG Σ,
    !inv'GS (cifOF CON) Σ, !inv_tokC CON, !inv_tokCS CON JUDG Σ}.
  Implicit Type l : loc.

  (** Dereference a nested mutable reference *)
  Lemma bor_bor_deref {α β l Φx q} :
    [[{ β ⊑□ α ∗ q.[β] ∗
      bor_tok β (∃ l', ▷ l ↦ #l' ∗ cif_bor_tok α (Φx l'))%cif }]]
      [borrow_wsat bupd ⟦⟧ᶜ]
      !#l
    [[{ l', RET #l'; q.[β] ∗ bor_tok β (Φx l') }]].
  Proof.
    iIntros (Ψ) "(#⊑ & [β β'] & b) →Ψ".
    iMod (bor_tok_open (M:=bupd) with "β b") as "/=[o [%l'[>↦ b']]]".
    iApply twpw_fupdw_nonval; [done|]. wp_read.
    iMod (lft_sincl_live_acc with "⊑ β'") as (?) "[α →β']".
    rewrite sem_cif_in /=.
    iMod (bor_tok_reborrow (M:=bupd) with "⊑ α b'") as "(α & →b' & b')".
    iDestruct ("→β'" with "α") as "β'".
    iMod (obor_tok_subdiv (M:=bupd) [] with "[] o [] [↦ →b']") as "[β _]"=>/=.
    { iApply lft_sincl_refl. } { done. }
    { iIntros "† _ !>". iExists _. iFrame "↦". rewrite sem_cif_in /=.
      by iApply "→b'". }
    iModIntro. iApply "→Ψ". iFrame.
  Qed.

  (** Load from an immutable shared borrow *)
  Lemma imbor_load {l α q} {n : Z} :
    [[{ q.[α] ∗ inv_tok nroot (cif_bor_tok α (▷ l ↦ #n)) }]]
      [inv_wsat ⟦⟧ᶜ ∗ borrow_wsat bupd ⟦⟧ᶜ]
      !ˢᶜ#l
    [[{ RET #n; q.[α] }]].
  Proof.
    iIntros (Φ) "[α #i] →Φ". iMod (inv_tok_acc with "i") as "/=[b cl]"; [done|].
    rewrite sem_cif_in /=.
    iMod (bor_tok_open (M:=bupd) with "α b") as "/=[o >↦]". wp_read.
    iMod (obor_tok_close (M:=bupd) with "o [↦]") as "[α b]"=>/=; [done|].
    iMod ("cl" with "b") as "_". iModIntro. by iApply "→Φ".
  Qed.

  Context `{!prophGS xty Σ, !proph_agG unit xty Σ, !proph_agC unit xty CON,
    !proph_agCS unit xty CON JUDG Σ, !pbor_tokC unit xty CON,
    !pbor_tokCS unit xty CON JUDG Σ}.
  Implicit Type X : xty.

  (** Dereference a nested prophetic mutable reference *)
  Lemma pbor_pbor_deref {X η α β l Φx q pπ} :
    [[{ β ⊑□ α ∗ q.[β] ∗
        pbor_tok (X:=X *'ₓ X) β () pπ η
          (λ _ pπ, ∃ l' (xπ : clair _ X) (ξ : prvar X),
            ⌜pπ = λ π, (xπ π, π ξ)'⌝ ∗
            ▷ l ↦ #l' ∗ cif_pbor_tok α () xπ ξ (Φx l'))%cif }]]
      [borrow_wsat bupd ⟦⟧ᶜ]
      !#l
    [[{ l', RET #l'; ∃ (xπ : clair _ X) (ξ ξ' : prvar X),
        ⌜pπ = λ π, (xπ π, π ξ)'⌝ ∗ ⟨π, π η = (π ξ', π ξ)'⟩ ∗ q.[β] ∗
        pbor_tok β () xπ ξ' (Φx l') }]].
  Proof.
    iIntros (Ψ) "(#⊑ & [β β'] & b) →Ψ".
    iMod (pbor_tok_open (M:=bupd) with "β b") as "/=[o big]".
    iDestruct "big" as (l' xπ ξ ->) "[>↦ b]". rewrite sem_cif_in /=.
    iApply twpw_fupdw_nonval; [done|]. wp_read.
    iMod (lft_sincl_live_acc with "⊑ β'") as (?) "[α →β']".
    iMod (pobor_pbor_tok_reborrow (M:=bupd) (λ π x, (x, π ξ)' : _ *'ₓ _)
      with "⊑ α o b [↦]") as "(ξ & Φx & big)"=>/=. { by move=> ????[]. }
    { iIntros ([]?) "_ ? !>". iExists _, _, _. rewrite sem_cif_in /=.
    by iFrame. }
    iMod ("big" $! [Aprvar _ ξ] with "[%] [$ξ //]")
      as (?) "(obs & [ξ _ ] & big)".
    { move=> ?. apply proph_dep_f. apply: proph_dep_one. }
    iMod ("big" with "ξ Φx") as "(β & α & b)". iModIntro. iApply "→Ψ".
    iDestruct ("→β'" with "α") as "$". by iFrame.
  Qed.
End borrow.
