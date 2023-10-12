(** * Verification on borrowing *)

From nola.examples.logic Require Export borrow.
From nola.examples.heap_lang Require Export notation.

Section borrow.
  Context `{!nintpGS Σ}.

  (** Convert a nested borrow *)
  Lemma bor_bor_conv' `{!nderivy ih δ} {α β P Q} :
    α ⊑□ β -∗ β ⊑□ α -∗ □ conv δ P Q -∗ □ conv δ Q P -∗
    conv δ (n_bor' [] α P) (n_bor' [] β Q).
    iIntros "#⊑ #⊑' #PQ #QP". iApply (derivy_byintp (δ:=δ))=>/=.
    iIntros "% % % _ #→ _ b". iDestruct (bor_lft with "⊑' b") as "b".
    iApply (bor_conv with "[] [] b"); iModIntro; by iApply "→".
  Qed.
  Lemma bor_bor_conv `{!nderivy ih δ} {α β P Q} :
    α ⊑□ β -∗ β ⊑□ α -∗ □ conv δ P Q -∗ □ conv δ Q P -∗
    bor δ α (n_bor' [] α P) -∗ bor δ β (n_bor' [] β Q).
  Proof.
    iIntros "#⊑ #⊑' #PQ #QP b". iDestruct (bor_lft with "⊑' b") as "b".
    iApply (bor_conv with "[] [] b"); iModIntro; by iApply bor_bor_conv'.
  Qed.

  (** Dereference a nested mutable reference *)
  Lemma bor_bor_deref {E l α β Φ q} :
    q.[α ⊓ β] -∗
    bord α (∃ l' : loc, l ↦ #l' ∗ n_bor' [] β (∃ v, l' ↦ v ∗ Φ v))
      =[borrow_wsatd ∗ fborrow_wsat']{E}=∗
      q.[α ⊓ β] ∗ ∃ l' : loc,
        l ↦[α] #l' ∗ bord (α ⊓ β) (∃ v, l' ↦ v ∗ Φ v).
  Proof.
    iIntros "[α β] b". iMod (bor_open with "α b") as "[o big]"=>/=.
    iDestruct "big" as (l') "[↦ b']".
    iMod (bor_reborrow α with "β b'") as "[$[b' →b']]".
    iMod (boro_subdiv [] [(λ _,_↦{_}_,_)']%n with "o [//] [↦] [→b']")
      as "[$[_[f _]]]"=>/=; last first.
    { iModIntro. iExists _. iFrame "f". by rewrite borc_bor comm. }
    { iIntros "† _ [↦ _]". iModIntro. iExists _. iFrame "↦". by iApply "→b'". }
    iFrame.
  Qed.
End borrow.
