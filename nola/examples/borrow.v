(** * Borrow examples *)

From nola.examples Require Export nsynty con.
From nola.heap_lang Require Export notation proofmode.
Import ProdNotation FunPRNotation UpdwNotation WpwNotation DsemNotation
  LftNotation ProphNotation NsyntyNotation.

Section borrow.
  Context `{!heapGS_gen hlc Σ, !SemCifcon JUDG CON Σ, !Jsem JUDG (iProp Σ),
    !inv'GS (cifOF CON) Σ, !InvCon CON, !InvSem JUDG CON Σ,
    !pborrowGS nsynty (cifOF CON) Σ, !BorCon CON, !BorSem JUDG CON Σ}.
  Implicit Type (Px Qx : cif CON Σ) (Φx Ψx : loc → cif CON Σ) (l : loc).

  (** Dereference a nested mutable reference *)
  Lemma bor_bor_deref {α β l Φx q} :
    [[{ β ⊑□ α ∗ q.[β] ∗
      nbor_tok β (∃ l', ▷ l ↦ #l' ∗ cif_bor α (Φx l'))%cif }]]
      [pborrow_wsat bupd_0 ⟦⟧]
      !#l
    [[{ l', RET #l'; q.[β] ∗ nbor_tok β (Φx l') }]].
  Proof.
    iIntros (Ψ) "(#⊑ & [β β'] & b) →Ψ".
    iMod (nbor_tok_open (M:=bupd_0) with "β b") as "/=[o [%l'[>↦ b']]]".
    iApply twpw_fupdw_nonval; [done|]. wp_load. iModIntro.
    iMod (lft_sincl_live_acc with "⊑ β'") as (?) "[α →β']".
    rewrite sem_ecustom /=.
    iMod (nbor_tok_reborrow (M:=bupd_0) with "⊑ α b'") as "(α & →b' & b')".
    iDestruct ("→β'" with "α") as "β'".
    iMod (nobor_tok_subdiv (M:=bupd_0) [] with "[] o [] [↦ →b']")
      as "[β _]"=>/=. { iApply lft_sincl_refl. } { done. }
    { iIntros "† _ !>". iExists _. iFrame "↦". rewrite sem_ecustom /=.
      by iApply "→b'". }
    iModIntro. iApply "→Ψ". iFrame.
  Qed.

  Context `{!PborCon nsynty CON, !PborSem nsynty JUDG CON Σ}.
  Implicit Type X : nsynty.

  (** Dereference a nested prophetic mutable reference *)
  Lemma pbor_pbor_deref {X η ξ α β l Φxx q} {x : X} :
    [[{ β ⊑□ α ∗ q.[β] ∗
        pbor_tok β ((x, ξ)' : _ *'ₛ prvarₛ _) η
          (λ '(x', ξ')', ∃ l', ▷ l ↦ #l' ∗ cif_pbor α x' ξ' (Φxx l'))%cif }]]
      [pborrow_wsat bupd_0 ⟦⟧]
      !#l
    [[{ l', RET #l';
        q.[β] ∗ ∃ ξ' : prvar X,
          ⟨π, π η = (π ξ', ξ)'⟩ ∗ pbor_tok β x ξ' (Φxx l') }]].
  Proof.
    iIntros (Ψ) "(#⊑ & [β β'] & b) →Ψ".
    iMod (pbor_tok_open (M:=bupd_0) with "β b") as "/=[o[%l'[>↦ b']]]".
    iApply twpw_fupdw_nonval; [done|]. wp_load. iModIntro.
    iMod (lft_sincl_live_acc with "⊑ β'") as (?) "[α →β']".
    rewrite sem_ecustom /=.
    iMod (pobor_pbor_tok_reborrow (TY:=nsynty) (M:=bupd_0)
      (λ _, (_,_)' : _ *'ₛ _) with "⊑ o α b' [↦]") as (?) "(β & α & obs & b)".
    { iIntros "/=% _ ? !>". iExists _. iFrame "↦". by rewrite sem_ecustom /=. }
    iModIntro. iApply "→Ψ". iDestruct ("→β'" with "α") as "$". iFrame.
  Qed.

  (** Load from an immutable shared borrow *)
  Lemma imbor_load {l α q} {n : Z} :
    [[{ q.[α] ∗ inv_tok nroot (cif_bor α (▷ l ↦ #n)) }]]
      [inv_wsat ⟦⟧ ∗ pborrow_wsat bupd_0 ⟦⟧]
      !#l
    [[{ RET #n; q.[α] }]].
  Proof.
    iIntros (Φ) "[α #i] →Φ". iMod (inv_tok_acc with "i") as "/=[b cl]"; [done|].
    rewrite sem_ecustom /=.
    iMod (nbor_tok_open (M:=bupd_0) with "α b") as "/=[o >↦]". wp_load.
    iModIntro.
    iMod (nobor_tok_close (M:=bupd_0) with "o [↦]") as "[α b]"=>/=; [done|].
    iMod ("cl" with "b") as "_". iModIntro. by iApply "→Φ".
  Qed.
End borrow.
