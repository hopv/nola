(** * On the borrowing *)

From nola.examples.logic Require Export deriv.

Implicit Type (P Q : nPropS (;ᵞ)) (Pl Ql : list (nPropS (;ᵞ))).

(** ** On borrowing *)

Section borrow.
  Context `{!nintpGS Σ, !nDeriv ih δ}.

  (** [fbor] is persistent *)
  Fact fbor_persistent {α Φ} : Persistent (fbor δ α Φ).
  Proof. exact _. Qed.

  (** Lemmas for conversion *)
  Local Lemma convert_trans {P Q R : nPropS (;ᵞ)} :
    ⸨ ↑ˡ P ==∗ ↑ˡ Q ⸩(δ) -∗ ⸨ ↑ˡ Q ==∗ ↑ˡ R ⸩(δ) -∗ ⸨ ↑ˡ P ==∗ ↑ˡ R ⸩(δ).
  Proof.
    iIntros "PQ QR". iApply (Deriv_map2 with "[] PQ QR")=>/=.
    iIntros "% _ _ PQ QR P". iMod ("PQ" with "P"). by iApply "QR".
  Qed.
  Local Lemma convert_refl {P : nPropS (;ᵞ)} :
    ⊢ ⸨ ↑ˡ P ==∗ ↑ˡ P ⸩(δ).
  Proof. iApply Deriv_intro=>/=. by iIntros. Qed.
  Local Lemma convert_use {P Q : nPropS (;ᵞ)} :
    ⸨ ↑ˡ P ==∗ ↑ˡ Q ⸩ ⊢ ⟦ P ⟧ ==∗ ⟦ Q ⟧.
  Proof.
    iIntros "PQ". iDestruct (nderiv_sound with "PQ") as "?".
    by rewrite/= !nintp_nlarge.
  Qed.

  (** Convert borrower and lender tokens *)
  Lemma borc_convert {α P Q} :
    ⸨ ↑ˡ P ==∗ ↑ˡ Q ⸩(δ) -∗ ⸨ ↑ˡ Q ==∗ ↑ˡ P ⸩(δ) -∗ borc δ α P -∗ borc δ α Q.
  Proof.
    iIntros "PQ QP [%R[PR[RP c]]]". iExists _. iFrame "c".
    iSplitL "QP PR";
      [iApply (convert_trans with "QP PR")|iApply (convert_trans with "RP PQ")].
  Qed.
  Lemma bor_convert {α P Q} :
    ⸨ ↑ˡ P ==∗ ↑ˡ Q ⸩(δ) -∗ ⸨ ↑ˡ Q ==∗ ↑ˡ P ⸩(δ) -∗ bor δ α P -∗ bor δ α Q.
  Proof.
    iIntros "PQ QP [%R[PR[RP b]]]". iExists _. iFrame "b".
    iSplitL "QP PR";
      [iApply (convert_trans with "QP PR")|iApply (convert_trans with "RP PQ")].
  Qed.
  Lemma obor_convert {α q P Q} :
    ⸨ ↑ˡ Q ==∗ ↑ˡ P ⸩(δ) -∗ obor δ α q P -∗ obor δ α q Q.
  Proof.
    iIntros "QP [%R[PR o]]". iExists _. iFrame "o".
    iApply (convert_trans with "QP PR").
  Qed.
  Lemma lend_convert {α P Q} :
    ⸨ ↑ˡ P ==∗ ↑ˡ Q ⸩(δ) -∗ lend δ α P -∗ lend δ α Q.
  Proof.
    iIntros "PQ [%R[RP l]]". iExists _. iFrame "l".
    iApply (convert_trans with "RP PQ").
  Qed.
  Lemma fbor_convert {α Φ Ψ} :
    □ ⸨ (∀ q, ↑ˡ Φ q ==∗ ↑ˡ Ψ q) ∗ (∀ q, ↑ˡ Ψ q ==∗ ↑ˡ Φ q) ⸩(δ) -∗
    fbor δ α Φ -∗ fbor δ α Ψ.
  Proof.
    iIntros "#ΦΨ [%[%Φ'[⊑[#ΦΦ' s]]]]". iExists _, _. iFrame "⊑ s". iModIntro.
    iApply (Deriv_map2 with "[] ΦΨ ΦΦ'")=>/=.
    iIntros "% _ _ {ΦΨ}[ΦΨ ΨΦ] {ΦΦ'}[ΦΦ' Φ'Φ]". iSplitL "ΨΦ ΦΦ'".
    - iIntros "% Ψ". iMod ("ΨΦ" with "Ψ"). by iApply "ΦΦ'".
    - iIntros "% Φ". iMod ("Φ'Φ" with "Φ"). by iApply "ΦΨ".
  Qed.

  (** Modify tokens with lifetime inclusion *)
  Lemma borc_lft {α β P} : β ⊑□ α -∗ borc δ α P -∗ borc δ β P.
  Proof.
    iIntros "⊑ [%[?[? c]]]". iDestruct (bor_ctok_lft with "⊑ c") as "c".
    iExists _. iFrame.
  Qed.
  Lemma bor_lft {α β P} : β ⊑□ α -∗ bor δ α P -∗ bor δ β P.
  Proof.
    iIntros "⊑ [%[?[? b]]]". iDestruct (bor_tok_lft with "⊑ b") as "b".
    iExists _. iFrame.
  Qed.
  Lemma obor_lft {α β q r P} :
    β ⊑□ α -∗ (q.[α] -∗ r.[β]) -∗ obor δ α q P -∗ obor δ β r P.
  Proof.
    iIntros "⊑ → [%[? o]]". iDestruct (obor_tok_lft with "⊑ → o") as "o".
    iExists _. iFrame.
  Qed.
  Lemma lend_lft {α β P} : α ⊑□ β -∗ lend δ α P -∗ lend δ β P.
  Proof.
    iIntros "⊑ [%[? l]]". iDestruct (lend_tok_lft with "⊑ l") as "l". iExists _.
    iFrame.
  Qed.
  Lemma fbor_lft {α β Φ} : β ⊑□ α -∗ fbor δ α Φ -∗ fbor δ β Φ.
  Proof.
    iIntros "#? [%[%[#? s]]]". iExists _, _. iFrame "s".
    by iApply lft_sincl_trans.
  Qed.

  (** Other conversions *)
  Lemma borc_bor {α P} : borc δ α P ⊢ bor δ α P.
  Proof. iIntros "[% c]". rewrite bor_ctok_tok. by iExists _. Qed.
  Lemma borc_fake {α} P : [†α] ⊢ borc δ α P.
  Proof.
    iIntros "†". iExists _. rewrite bor_ctok_fake. iFrame "†".
    iSplitL; iApply convert_refl.
  Qed.
  Lemma bor_fake {α} P : [†α] ⊢ bor δ α P.
  Proof. by rewrite borc_fake borc_bor. Qed.
End borrow.

Section borrow.
  Context `{!nintpGS Σ}.

  (** Create borrowers and lenders *)
  Lemma borc_lend_new_list α Pl Ql :
    ([∗ list] P ∈ Pl, ⟦ P ⟧) -∗
    ([†α] -∗ ([∗ list] P ∈ Pl, ⟦ P ⟧) =[proph_wsat]=∗ [∗ list] Q ∈ Ql, ⟦ Q ⟧)
      =[borrow_wsatd]=∗
      ([∗ list] P ∈ Pl, borcd α P) ∗ [∗ list] Q ∈ Ql, lendd α Q.
  Proof.
    iIntros "Pl →Ql". setoid_rewrite <-nintpS_nintp.
    iMod (bor_lend_tok_new_list with "Pl [→Ql]") as "[bl ll]".
    { iIntros "#† ?". by iApply "→Ql". } iModIntro.
    iSplitL "bl"; iStopProof; do 3 f_equiv; iIntros "?"; iExists _; iFrame;
      [iSplitL|idtac]; iApply convert_refl.
  Qed.
  (** Simply create a borrower and a lender *)
  Lemma borc_lend_new α (P : nPropS (;ᵞ)) :
    ⟦ P ⟧ -∗ ([†α] -∗ ⟦ P ⟧ =[proph_wsat]=∗ ⟦ P ⟧) =[borrow_wsatd]=∗
      borcd α P ∗ lendd α P.
  Proof.
    iIntros "P". iMod (borc_lend_new_list α [P] [P] with "[P] []")
      as "[[$_][$_]]"; by [iFrame|iIntros|].
  Qed.

  (** Split a lender *)
  Lemma lend_split {α P} Ql :
    lendd α P -∗ (⟦ P ⟧ =[proph_wsat]=∗ [∗ list] Q ∈ Ql, ⟦ Q ⟧)
      =[borrow_wsatd]=∗ [∗ list] Q ∈ Ql, lendd α Q.
  Proof.
    iIntros "[%P'[P'P l]] →Ql". rewrite !convert_use.
    iMod (lend_tok_split with "l [P'P →Ql]") as "ll"=>/=.
    { setoid_rewrite nintpS_nintp. iIntros "P'".
      iMod ("P'P" with "P'") as "P". by iMod ("→Ql" with "P"). }
    iModIntro. iApply (big_sepL_impl with "ll"). iIntros "!> %% _ l".
    iExists _. iFrame "l". iApply convert_refl.
  Qed.

  (** Retrive from [lend] *)
  Lemma lend_retrieve {α P} :
    [†α] -∗ lendd α P =[proph_wsat ∗ borrow_wsatd]=∗ ⟦ P ⟧.
  Proof.
    iIntros "† [%Q[QP l]]". rewrite convert_use -modw_bupdw.
    iMod (lend_tok_retrieve with "† l") as "Q". rewrite nintpS_nintp.
    iMod ("QP" with "Q") as "$". by iIntros.
  Qed.

  (** Open a closed borrower *)
  Lemma borc_open {α q P} :
    q.[α] -∗ borcd α P =[borrow_wsatd]=∗ obord α q P ∗ ⟦ P ⟧.
  Proof.
    iIntros "α [%Q[PQ[QP c]]]". rewrite (convert_use (P:=Q)).
    iMod (bor_ctok_open with "α c") as "[o Q]". rewrite nintpS_nintp.
    iMod ("QP" with "Q") as "$". iExists _. by iFrame.
  Qed.
  (** Open a borrower *)
  Lemma bor_open {α q P} :
    q.[α] -∗ bord α P =[proph_wsat ∗ borrow_wsatd]=∗ obord α q P ∗ ⟦ P ⟧.
  Proof.
    iIntros "α [%Q[PQ[QP b]]]". rewrite (convert_use (P:=Q)) -modw_bupdw.
    iMod (bor_tok_open with "α b") as "[o Q]". rewrite nintpS_nintp modw_bupdw.
    iMod ("QP" with "Q") as "$". iExists _. by iFrame.
  Qed.

  (** Lemma for [obor_merge_subdiv] *)
  Local Lemma obor_list {αqPl β} :
    ([∗ list] '(α, q, P)' ∈ αqPl, β ⊑□ α ∗ obord α q P) -∗ ∃ αqRl,
      ⌜(λ '(α, q, _)', (α, q)') <$> αqRl = (λ '(α, q, _)', (α, q)') <$> αqPl⌝ ∗
      ([∗ list] '(α, q, R)' ∈ αqRl, β ⊑□ α ∗ obor_tok α q R) ∗
      (([∗ list] '(_, _, P)' ∈ αqPl, ⟦ P ⟧) ==∗
        [∗ list] '(_, _, R)' ∈ αqRl, ⟦ R ⟧).
  Proof.
    elim: αqPl=>/=.
    { iIntros. iExists []=>/=. do 2 (iSplit; [done|]). by iIntros. }
    iIntros ([α[q P]] αqPl IH) "[[⊑[%R[PR o]]] αqPl]". rewrite convert_use.
    iDestruct (IH with "αqPl") as (αqRl ?) "[ol →']".
    iExists ((α, q, R)' :: αqRl)=>/=. iFrame "⊑ o ol". iSplit.
    { iPureIntro. by f_equal. } iIntros "[P Pl]".
    iMod ("PR" with "P") as "$". iApply ("→'" with "Pl").
  Qed.
  (** Merge and subdivide borrowers *)
  Lemma obor_merge_subdiv αqPl Ql β :
    ([∗ list] '(α, q, P)' ∈ αqPl, β ⊑□ α ∗ obord α q P) -∗
    ([∗ list] Q ∈ Ql, ⟦ Q ⟧) -∗
    ([†β] -∗ ([∗ list] Q ∈ Ql, ⟦ Q ⟧)
      =[proph_wsat]=∗ [∗ list] '(_, _, P)' ∈ αqPl, ⟦ P ⟧) =[borrow_wsatd]=∗
      ([∗ list] '(α, q, _)' ∈ αqPl, q.[α]) ∗ ([∗ list] Q ∈ Ql, borcd β Q).
  Proof.
    setoid_rewrite <-nintpS_nintp. iIntros "ol Ql →Pl".
    rewrite -(big_sepL_fmap (λ '(α, q, _)', (α, q)') (λ _ '(α, q)', q.[α])%I).
    iDestruct (obor_list with "ol") as (?<-) "[ol →]".
    rewrite big_sepL_fmap.
    iMod (obor_tok_merge_subdiv _ Ql with "ol Ql [→ →Pl]") as "[$ cl]".
    { iIntros "† Ql". iMod ("→Pl" with "† Ql") as "Pl".
      setoid_rewrite nintpS_nintp. by iMod ("→" with "Pl") as "$". }
    iModIntro. iStopProof; do 3 f_equiv. iIntros "c". iExists _. iFrame "c".
    iSplitL; by iApply convert_refl.
  Qed.
  (** Subdivide borrowers *)
  Lemma obor_subdiv {α q P} Ql β :
    β ⊑□ α -∗ obord α q P -∗ ([∗ list] Q ∈ Ql, ⟦ Q ⟧) -∗
    ([†β] -∗ ([∗ list] Q ∈ Ql, ⟦ Q ⟧) =[proph_wsat]=∗ ⟦ P ⟧) =[borrow_wsatd]=∗
      q.[α] ∗ ([∗ list] Q ∈ Ql, borcd β Q).
  Proof.
    iIntros "⊑ o Ql →P".
    iMod (obor_merge_subdiv [(_,_,_)'] with "[⊑ o] Ql [→P]") as "[[$ _]$]"=>/=;
      by [iFrame|rewrite bi.sep_emp|].
  Qed.
  (** Simply close a borrower *)
  Lemma obor_close {α q P} :
    obord α q P -∗ ⟦ P ⟧ =[borrow_wsatd]=∗ q.[α] ∗ borcd α P.
  Proof.
    iIntros "o P".
    iMod (obor_subdiv [P] with "[] o [P] []") as "[$[$_]]"=>/=;
      by [iApply lft_sincl_refl|iFrame|iIntros "_[$_]"|].
  Qed.

  (** Lemma for [obor_reborrow] *)
  Local Lemma obor_obor_tok {α q P} :
    obord α q P -∗ ⟦ P ⟧ =[borrow_wsatd]=∗ obor_tok α q P ∗ ⟦ P ⟧ˢ.
  Proof.
    iIntros "[%Q[PQ o]] P". rewrite convert_use -!nintpS_nintp.
    iMod (obor_tok_subdiv [_] with "[] o [P] [PQ]") as "[α[c _]]"=>/=.
    { iApply lft_sincl_refl. } { by iFrame. }
    { iIntros "_ [P _]". by iMod ("PQ" with "P"). }
    by iMod (bor_ctok_open with "α c") as "$".
  Qed.
  (** Reborrow a borrower *)
  Lemma obor_reborrow {α q P} β :
    obord α q P -∗ ⟦ P ⟧ =[borrow_wsatd]=∗
      q.[α] ∗ borcd (α ⊓ β) P ∗ ([†β] -∗ bord α P).
  Proof.
    iIntros "o P". iMod (obor_obor_tok with "o P") as "[o P]".
    iMod (obor_tok_reborrow (intp:=λ P, ⟦ P ⟧ˢ) with "o P") as "[$[c →o]]".
    iModIntro. iSplitL "c".
    - iExists _. iFrame "c". iSplitL; iApply convert_refl.
    - iIntros "†". iExists _. iDestruct ("→o" with "†") as "$".
      iSplitL; iApply convert_refl.
  Qed.
  Lemma borc_reborrow {α q P} β :
    q.[α] -∗ borcd α P =[borrow_wsatd]=∗
      q.[α] ∗ borcd (α ⊓ β) P ∗ ([†β] -∗ bord α P).
  Proof.
    iIntros "α c". iMod (borc_open with "α c") as "[o P]".
    by iMod (obor_reborrow with "o P").
  Qed.
  Lemma bor_reborrow {α q P} β :
    q.[α] -∗ bord α P =[borrow_wsatd ∗ proph_wsat]=∗
      q.[α] ∗ borcd (α ⊓ β) P ∗ ([†β] -∗ bord α P).
  Proof.
    iIntros "α b". iMod (bor_open with "α b") as "[o P]".
    by iMod (obor_reborrow with "o P").
  Qed.

  (** Create a fractured borrow *)
  Lemma bor_fbor {α} Φ q : bord α (Φ q) =[sinv_wsatd]=∗ fbord α Φ.
  Proof.
    iIntros "b W".
    iMod (sinv_tok_alloc (∃ q, n_bor' [] α (Φ q))%n with "W") as "[s →W]"=>/=.
    iDestruct ("→W" with "[b]") as "$". { by iExists _. }
    iModIntro. iExists _, _. iFrame "s". iSplit. { iApply lft_sincl_refl. }
    iModIntro. iApply (Deriv_intro (DI:=nderivsi))=>/=.
    iIntros "% _ _"; iSplitL; by iIntros.
  Qed.
  (** Open a fractured borrow *)
  Lemma fbor_open {α r Φ} :
    r.[α] -∗ fbord α Φ -∗
    (∀ q, ⟦ Φ q ⟧ ==∗ ⟦ Φ (q/2)%Qp ⟧ ∗ ⟦ Φ (q/2)%Qp ⟧) -∗
    (∀ q, ⟦ Φ (q/2)%Qp ⟧ -∗ ⟦ Φ (q/2)%Qp ⟧ ==∗ ⟦ Φ q ⟧)
      =[sinv_wsatd ∗ proph_wsat ∗ borrow_wsatd]=∗ ∃ q,
      obord α r (Φ q) ∗ ⟦ Φ q ⟧.
  Proof.
    rewrite [(sinv_wsatd ∗ _)%I]comm -modw_bupdw.
    iIntros "α [%β[%Ψ[#⊑[#ΦΨ s]]]] Φ↓ Φ↑ W".
    iDestruct (sinv_tok_acc with "s W") as "/=[[%q b] →W]".
    iDestruct nderiv_sound as "→". iDestruct ("→" with "ΦΨ") as "/={ΦΨ}[ΦΨ ΨΦ]".
    setoid_rewrite nintp_nlarge.
    iMod (lft_sincl_tok_acc with "⊑ α") as (s) "[β →α]".
    iMod (bor_open with "β b") as "[o Ψ]". iMod ("ΨΦ" with "Ψ") as "Φ".
    iMod ("Φ↓" with "Φ") as "[Φ Φ']". iMod ("ΦΨ" with "Φ'") as "Ψ".
    iMod (obor_subdiv [_;_] with "[] o [$Φ $Ψ//] [Φ↑]") as "[β[c[c' _]]]"=>/=.
    { iApply lft_sincl_refl. }
    { iIntros "_ [Φ[Ψ _]]". iMod ("ΨΦ" with "Ψ") as "Φ'".
      iMod ("Φ↑" with "Φ Φ'") as "Φ". by iMod ("ΦΨ" with "Φ"). }
    iDestruct ("→W" with "[c']") as "$". { iExists _. by iApply borc_bor. }
    iExists _. iDestruct (borc_lft with "⊑ c") as "c".
    iDestruct ("→α" with "β") as "α". by iMod (borc_open with "α c") as "$".
  Qed.
End borrow.
