(** * On the borrowing *)

From nola.examples.logic Require Export deriv.
From nola.iris Require Export list.

Implicit Type (P Q : nPropS (;ᵞ)) (Pl Ql : list (nPropS (;ᵞ))) (X Y : nsynty)
  (Xl Yl : list nsynty).

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
  Local Lemma aconvert_trans {A} {Φ Ψ Ω : A → nPropS (;ᵞ)} :
    ⸨ ∀ a, ↑ˡ Φ a ==∗ ↑ˡ Ψ a ⸩(δ) -∗ ⸨ ∀ a, ↑ˡ Ψ a ==∗ ↑ˡ Ω a ⸩(δ) -∗
    ⸨ ∀ a, ↑ˡ Φ a ==∗ ↑ˡ Ω a ⸩(δ).
  Proof.
    iIntros "ΦΨ ΨΩ". iApply (Deriv_map2 with "[] ΦΨ ΨΩ")=>/=.
    iIntros "% _ _ ΦΨ ΨΩ % Φ". iMod ("ΦΨ" with "Φ"). by iApply "ΨΩ".
  Qed.
  Local Lemma aconvert_refl {A} {Φ : A → nPropS (;ᵞ)} :
    ⊢ ⸨ ∀ a, ↑ˡ Φ a ==∗ ↑ˡ Φ a ⸩(δ).
  Proof. iApply Deriv_intro=>/=. by iIntros. Qed.
  Local Lemma aconvert_use {A} {Φ Ψ : A → nPropS (;ᵞ)} :
    ⸨ ∀ a, ↑ˡ Φ a ==∗ ↑ˡ Ψ a ⸩ ⊢ ∀ a, ⟦ Φ a ⟧ ==∗ ⟦ Ψ a ⟧.
  Proof.
    iIntros "PQ". iDestruct (nderiv_sound with "PQ") as "?"=>/=.
    by setoid_rewrite nintp_nlarge.
  Qed.

  (** Lemmas for introducing tokens *)
  Local Lemma borc_intro {α P} : nbor_ctok α P ⊢ borc δ α P.
  Proof. iIntros "c". iExists _. iFrame "c". iSplitL; iApply convert_refl. Qed.
  Local Lemma bor_intro {α P} : nbor_tok α P ⊢ bor δ α P.
  Proof. iIntros "b". iExists _. iFrame "b". iSplitL; iApply convert_refl. Qed.
  Local Lemma lend_intro {α P} : nlend_tok α P ⊢ lend δ α P.
  Proof. iIntros "l". iExists _. iFrame "l". iApply convert_refl. Qed.
  Local Lemma pborc_intro {X α x ξ Φ} :
    pbor_ctok (X:=X) α x ξ Φ ⊢ pborc δ α x ξ Φ.
  Proof. iIntros "c". iExists _. iFrame "c". iSplitL; iApply aconvert_refl. Qed.
  Local Lemma pbor_intro {X α x ξ Φ} : pbor_tok (X:=X) α x ξ Φ ⊢ pbor δ α x ξ Φ.
  Proof. iIntros "b". iExists _. iFrame "b". iSplitL; iApply aconvert_refl. Qed.
  Local Lemma plend_intro {X α xπ Φ} : plend_tok (X:=X) α xπ Φ ⊢ plend δ α xπ Φ.
  Proof. iIntros "l". iExists _. iFrame "l". iApply aconvert_refl. Qed.

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
    □ ⸨ ∀ q, ↑ˡ Φ q ==∗ ↑ˡ Ψ q ⸩(δ) ∗ □ ⸨ ∀ q, ↑ˡ Ψ q ==∗ ↑ˡ Φ q ⸩(δ) ∗
    fbor δ α Φ -∗ fbor δ α Ψ.
  Proof.
    iIntros "[#ΦΨ[#ΨΦ[%[%Ω[⊑[#ΦΩ[#ΩΦ s]]]]]]]". iExists _, _. iFrame "⊑ s".
    iSplit; iModIntro; by iApply aconvert_trans.
  Qed.
  Lemma pborc_convert {X α x ξ Φ Ψ} :
    ⸨ ∀ x, ↑ˡ Φ x ==∗ ↑ˡ Ψ x ⸩(δ) -∗ ⸨ ∀ x, ↑ˡ Ψ x ==∗ ↑ˡ Φ x ⸩(δ) -∗
    pborc (X:=X) δ α x ξ Φ -∗ pborc δ α x ξ Ψ.
  Proof.
    iIntros "ΦΨ ΨΦ [%Ω[ΦΩ[ΩΦ c]]]". iExists _=>/=. iFrame "c".
    iSplitL "ΨΦ ΦΩ". { iApply (aconvert_trans with "ΨΦ ΦΩ"). }
    { iApply (aconvert_trans with "ΩΦ ΦΨ"). }
  Qed.
  Lemma pbor_convert {X α x ξ Φ Ψ} :
    ⸨ ∀ x, ↑ˡ Φ x ==∗ ↑ˡ Ψ x ⸩(δ) -∗ ⸨ ∀ x, ↑ˡ Ψ x ==∗ ↑ˡ Φ x ⸩(δ) -∗
    pbor (X:=X) δ α x ξ Φ -∗ pbor δ α x ξ Ψ.
  Proof.
    iIntros "ΦΨ ΨΦ [%Ω[ΦΩ[ΩΦ b]]]". iExists _=>/=. iFrame "b".
    iSplitL "ΨΦ ΦΩ". { iApply (aconvert_trans with "ΨΦ ΦΩ"). }
    { iApply (aconvert_trans with "ΩΦ ΦΨ"). }
  Qed.
  Lemma opbor_convert {X α q ξ Φ Ψ} :
    ⸨ ∀ x, ↑ˡ Ψ x ==∗ ↑ˡ Φ x ⸩(δ) -∗ opbor (X:=X) δ α q ξ Φ -∗ opbor δ α q ξ Ψ.
  Proof.
    iIntros "ΨΦ [%Ω[ΦΩ o]]". iExists _. iFrame "o".
    iApply (aconvert_trans with "ΨΦ ΦΩ").
  Qed.
  Lemma plend_convert {X α xπ Φ Ψ} :
    ⸨ ∀ x, ↑ˡ Φ x ==∗ ↑ˡ Ψ x ⸩(δ) -∗ plend (X:=X) δ α xπ Φ -∗ plend δ α xπ Ψ.
  Proof.
    iIntros "ΦΨ [%Ω[ΩΦ l]]". iExists _. iFrame "l".
    iApply (aconvert_trans with "ΩΦ ΦΨ").
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
    iIntros "#? [%[%[⊑ s]]]". iExists _, _. iFrame "s".
    by iApply lft_sincl_trans.
  Qed.
  Lemma pborc_lft {X α β x ξ Φ} :
    β ⊑□ α -∗ pborc (X:=X) δ α x ξ Φ -∗ pborc δ β x ξ Φ.
  Proof.
    iIntros "⊑ [%[?[? c]]]". iDestruct (pbor_ctok_lft with "⊑ c") as "c".
    iExists _. iFrame.
  Qed.
  Lemma pbor_lft {X α β x ξ Φ} :
    β ⊑□ α -∗ pbor (X:=X) δ α x ξ Φ -∗ pbor δ β x ξ Φ.
  Proof.
    iIntros "⊑ [%[?[? b]]]". iDestruct (pbor_tok_lft with "⊑ b") as "b".
    iExists _. iFrame.
  Qed.
  Lemma opbor_lft {X α β q r ξ Φ} :
    β ⊑□ α -∗ (q.[α] -∗ r.[β]) -∗ opbor (X:=X) δ α q ξ Φ -∗ opbor δ β r ξ Φ.
  Proof.
    iIntros "⊑ → [%[? o]]". iDestruct (opbor_tok_lft with "⊑ → o") as "o".
    iExists _. iFrame.
  Qed.
  Lemma plend_lft {X α β xπ Φ} :
    α ⊑□ β -∗ plend (X:=X) δ α xπ Φ -∗ plend δ β xπ Φ.
  Proof.
    iIntros "⊑ [%[? l]]". iDestruct (plend_tok_lft with "⊑ l") as "l".
    iExists _. iFrame.
  Qed.

  (** Other conversions *)
  Lemma borc_bor {α P} : borc δ α P ⊢ bor δ α P.
  Proof. iIntros "[% c]". rewrite /nbor_ctok bor_ctok_tok. by iExists _. Qed.
  Lemma borc_fake {α} P : [†α] ⊢ borc δ α P.
  Proof.
    iIntros "†". iExists _. rewrite bor_ctok_fake. iFrame "†".
    iSplitL; iApply convert_refl.
  Qed.
  Lemma bor_fake {α} P : [†α] ⊢ bor δ α P.
  Proof. by rewrite borc_fake borc_bor. Qed.
  Lemma pborc_pbor {X α x ξ Φ} : pborc (X:=X) δ α x ξ Φ ⊢ pbor δ α x ξ Φ.
  Proof. iIntros "[% c]". rewrite pbor_ctok_tok. by iExists _. Qed.
  Lemma pborc_fake {X α x ξ Φ} : [†α] ⊢ pborc (X:=X) δ α x ξ Φ.
  Proof.
    iIntros "†". iExists _. rewrite/= pbor_ctok_fake. iFrame "†".
    iSplitL; iApply aconvert_refl.
  Qed.
  Lemma pbor_fake {X α x ξ Φ} : [†α] ⊢ pbor (X:=X) δ α x ξ Φ.
  Proof. by rewrite pborc_fake pborc_pbor. Qed.

End borrow.

Section borrow.
  Context `{!nintpGS Σ}.

  (** On non-prophetic borrowing *)

  (** Create borrowers and lenders *)
  Lemma borc_lend_new_list `{!GenUpd M} α Pl Ql :
    ([∗ list] P ∈ Pl, ⟦ P ⟧) -∗
    ([†α] -∗ ([∗ list] P ∈ Pl, ⟦ P ⟧) -∗ M ([∗ list] Q ∈ Ql, ⟦ Q ⟧))
      =[pborrow_wsatd M]=∗
      ([∗ list] P ∈ Pl, borcd α P) ∗ [∗ list] Q ∈ Ql, lendd α Q.
  Proof.
    iIntros "Pl →Ql". setoid_rewrite <-nintpS_nintp.
    setoid_rewrite <-borc_intro. setoid_rewrite <-lend_intro.
    iApply (nbor_nlend_tok_new_list with "Pl [→Ql]"). iIntros "#† ?".
    by iApply "→Ql".
  Qed.
  (** Simply create a borrower and a lender *)
  Lemma borc_lend_new `{!GenUpd M} α (P : nPropS (;ᵞ)) :
    ⟦ P ⟧ =[pborrow_wsatd M]=∗ borcd α P ∗ lendd α P.
  Proof.
    iIntros "P". iMod (borc_lend_new_list α [P] [P] with "[P] []")
      as "[[$_][$_]]"; by [iFrame|iIntros|].
  Qed.

  (** Split a lender *)
  Lemma lend_split `{!GenUpd M} {α P} Ql :
    lendd α P -∗ (⟦ P ⟧ -∗ M ([∗ list] Q ∈ Ql, ⟦ Q ⟧)) =[pborrow_wsatd M]=∗
      [∗ list] Q ∈ Ql, lendd α Q.
  Proof.
    iIntros "[%R[RP l]] →Ql". rewrite !convert_use.
    setoid_rewrite <-nintpS_nintp. setoid_rewrite <-lend_intro.
    iApply (nlend_tok_split with "l [RP →Ql]"). iIntros "R".
    iMod ("RP" with "R") as "P". by iMod ("→Ql" with "P").
  Qed.

  (** Retrive from [lend] *)
  Lemma lend_retrieve `{!GenUpd M} {α P} :
    [†α] -∗ lendd α P -∗ modw M (pborrow_wsatd M) ⟦ P ⟧.
  Proof.
    iIntros "† [%Q[QP l]]". rewrite convert_use.
    iMod (nlend_tok_retrieve with "† l") as "Q". rewrite nintpS_nintp.
    iMod ("QP" with "Q") as "$". by iIntros.
  Qed.

  (** Open a closed borrower *)
  Lemma borc_open `{!GenUpd M} {α q P} :
    q.[α] -∗ borcd α P =[pborrow_wsatd M]=∗ obord α q P ∗ ⟦ P ⟧.
  Proof.
    iIntros "α [%Q[PQ[QP c]]]". rewrite (convert_use (P:=Q)).
    iMod (nbor_ctok_open with "α c") as "[o Q]". rewrite/= nintpS_nintp.
    iMod ("QP" with "Q") as "$". iExists _. by iFrame.
  Qed.
  (** Open a borrower *)
  Lemma bor_open `{!GenUpd M} {α q P} :
    q.[α] -∗ bord α P -∗ modw M (pborrow_wsatd M) (obord α q P ∗ ⟦ P ⟧).
  Proof.
    iIntros "α [%Q[PQ[QP b]]]". rewrite (convert_use (P:=Q)).
    iMod (nbor_tok_open with "α b") as "[o Q]". rewrite/= nintpS_nintp.
    iMod ("QP" with "Q") as "$". iApply modw_fold. iModIntro. iExists _.
    by iFrame.
  Qed.

  (** Lemma for [obor_merge_subdiv] *)
  Local Lemma obor_list {αqPl β} :
    ([∗ list] '(α, q, P)' ∈ αqPl, β ⊑□ α ∗ obord α q P) ⊢
    ∃ αqRl,
      ⌜(λ '(α, q, _)', (α, q)') <$> αqRl = (λ '(α, q, _)', (α, q)') <$> αqPl⌝ ∗
      ([∗ list] '(α, q, R)' ∈ αqRl, β ⊑□ α ∗ onbor_tok α q R) ∗
      (([∗ list] '(_, _, P)' ∈ αqPl, ⟦ P ⟧) ==∗
        [∗ list] '(_, _, R)' ∈ αqRl, ⟦ R ⟧).
  Proof.
    elim: αqPl=>/=.
    { iIntros. iExists []=>/=. do 2 (iSplit; [done|]). by iIntros. }
    iIntros ([α[q P]] αqPl ->) "[[⊑[%R[PR o]]][%αqRl[%[ol →']]]]".
    rewrite convert_use. iExists ((α, q, R)' :: αqRl)=>/=. iFrame "⊑ o ol".
    iSplit. { iPureIntro. by f_equal. }
    iIntros "[P Pl]". iMod ("PR" with "P") as "$". iApply ("→'" with "Pl").
  Qed.
  (** Merge and subdivide borrowers *)
  Lemma obor_merge_subdiv `{!GenUpd M} αqPl Ql β :
    ([∗ list] '(α, q, P)' ∈ αqPl, β ⊑□ α ∗ obord α q P) -∗
    ([∗ list] Q ∈ Ql, ⟦ Q ⟧) -∗
    ([†β] -∗ ([∗ list] Q ∈ Ql, ⟦ Q ⟧) -∗ M
      ([∗ list] '(_, _, P)' ∈ αqPl, ⟦ P ⟧)) =[pborrow_wsatd M]=∗
      ([∗ list] '(α, q, _)' ∈ αqPl, q.[α]) ∗ ([∗ list] Q ∈ Ql, borcd β Q).
  Proof.
    rewrite obor_list /=. setoid_rewrite <-nintpS_nintp.
    rewrite -(big_sepL_fmap (λ '(α, q, _)', (α, q)') (λ _ '(α, q)', q.[α])%I).
    iIntros "[%[<-[ol →]]] Ql →Pl". rewrite big_sepL_fmap.
    setoid_rewrite <-borc_intro.
    iApply (onbor_tok_merge_subdiv with "ol Ql [→ →Pl]"). iIntros "† Ql".
    iMod ("→Pl" with "† Ql") as "Pl". iMod ("→" with "Pl") as "$". by iIntros.
  Qed.
  (** Subdivide borrowers *)
  Lemma obor_subdiv `{!GenUpd M} {α q P} Ql β :
    β ⊑□ α -∗ obord α q P -∗ ([∗ list] Q ∈ Ql, ⟦ Q ⟧) -∗
    ([†β] -∗ ([∗ list] Q ∈ Ql, ⟦ Q ⟧) -∗ M ⟦ P ⟧) =[pborrow_wsatd M]=∗
      q.[α] ∗ ([∗ list] Q ∈ Ql, borcd β Q).
  Proof.
    iIntros "⊑ o Ql →P".
    iMod (obor_merge_subdiv [(_,_,_)'] with "[⊑ o] Ql [→P]") as "[[$ _]$]"=>/=;
      by [iFrame|rewrite bi.sep_emp|].
  Qed.
  (** Simply close a borrower *)
  Lemma obor_close `{!GenUpd M} {α q P} :
    obord α q P -∗ ⟦ P ⟧ =[pborrow_wsatd M]=∗ q.[α] ∗ borcd α P.
  Proof.
    iIntros "o P".
    iMod (obor_subdiv [P] with "[] o [P] []") as "[$[$_]]"=>/=;
      by [iApply lft_sincl_refl|iFrame|iIntros "_[$_]"|].
  Qed.

  (** Lemma for [obor_reborrow] *)
  Local Lemma obor_onbor_tok `{!GenUpd M} {α q P} :
    obord α q P -∗ ⟦ P ⟧ =[pborrow_wsatd M]=∗ onbor_tok α q P ∗ ⟦ P ⟧ˢ.
  Proof.
    iIntros "[%Q[PQ o]] P". rewrite convert_use -!nintpS_nintp.
    iMod (onbor_tok_subdiv [_] with "[] o [P] [PQ]") as "[α[c _]]"=>/=.
    { iApply lft_sincl_refl. } { by iFrame. }
    { iIntros "_ [P _]". iMod ("PQ" with "P") as "$". by iIntros. }
    iApply (bor_ctok_open with "α c").
  Qed.
  (** Reborrow a borrower *)
  Lemma obor_reborrow `{!GenUpd M} {α q P} β :
    obord α q P -∗ ⟦ P ⟧ =[pborrow_wsatd M]=∗
      q.[α] ∗ borcd (α ⊓ β) P ∗ ([†β] -∗ bord α P).
  Proof.
    iIntros "o P". iMod (obor_onbor_tok with "o P") as "[o P]".
    rewrite -borc_intro -bor_intro.
    iApply (onbor_tok_reborrow (intp:=λ P, ⟦ P ⟧ˢ) with "o P").
  Qed.
  Lemma borc_reborrow `{!GenUpd M} {α q P} β :
    q.[α] -∗ borcd α P =[pborrow_wsatd M]=∗
      q.[α] ∗ borcd (α ⊓ β) P ∗ ([†β] -∗ bord α P).
  Proof.
    iIntros "α c". iMod (borc_open with "α c") as "[o P]".
    by iMod (obor_reborrow with "o P").
  Qed.
  Lemma bor_reborrow `{!GenUpd M} {α q P} β :
    q.[α] -∗ bord α P -∗ modw M (pborrow_wsatd M)
      (q.[α] ∗ borcd (α ⊓ β) P ∗ ([†β] -∗ bord α P)).
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
    iSplit; iModIntro; iApply aconvert_refl.
  Qed.
  (** Open a fractured borrow *)
  Lemma fbor_open `{!GenUpd M} {α r Φ} :
    r.[α] -∗ fbord α Φ -∗
    (∀ q, ⟦ Φ q ⟧ ==∗ ⟦ Φ (q/2)%Qp ⟧ ∗ ⟦ Φ (q/2)%Qp ⟧) -∗
    (∀ q, ⟦ Φ (q/2)%Qp ⟧ -∗ ⟦ Φ (q/2)%Qp ⟧ ==∗ ⟦ Φ q ⟧) -∗
      modw M (sinv_wsatd ∗ pborrow_wsatd M) (∃ q, obord α r (Φ q) ∗ ⟦ Φ q ⟧).
  Proof.
    rewrite [(sinv_wsatd ∗ _)%I]comm -modw_modw_sep.
    iIntros "α [%β[%Ψ[#⊑[#ΦΨ[#ΨΦ s]]]]] Φ↓ Φ↑ W". rewrite !aconvert_use.
    iDestruct (sinv_tok_acc with "s W") as "/=[[%q b] →W]".
    iMod (lft_sincl_tok_acc with "⊑ α") as (s) "[β →α]".
    iMod (bor_open with "β b") as "[o Ψ]". iMod ("ΨΦ" with "Ψ") as "Φ".
    iMod ("Φ↓" with "Φ") as "[Φ Φ']". iMod ("ΦΨ" with "Φ'") as "Ψ".
    iMod (obor_subdiv [_;_] with "[] o [$Φ $Ψ//] [Φ↑]") as "[β[c[c' _]]]"=>/=.
    { iApply lft_sincl_refl. }
    { iIntros "_ [Φ[Ψ _]]". iMod ("ΨΦ" with "Ψ") as "Φ'".
      iMod ("Φ↑" with "Φ Φ'") as "Φ". iMod ("ΦΨ" with "Φ") as "$". by iIntros. }
    iDestruct ("→W" with "[c']") as "$". { iExists _. by iApply borc_bor. }
    iApply modw_fold. iExists _. iDestruct (borc_lft with "⊑ c") as "c".
    iDestruct ("→α" with "β") as "α". iMod (borc_open with "α c") as "$".
    by iIntros.
  Qed.

  (** On prophetic borrowing *)

  (** Body of a prophetic lender *)
  Definition plend_bodyd {X} (xπ : proph_asnn → X) (Φ : X → nPropS (;ᵞ))
    : iProp Σ := ∃ y, ⟨π, xπ π = y⟩ ∗ ⟦ Φ y ⟧.
  Definition plend_body_vard {X} (ξ : prvar X) (Φ : X → nPropS (;ᵞ))
    : iProp Σ := plend_bodyd (λ π, π ξ) Φ.
  Local Lemma plend_bodyd_as {X xπ Φ} :
    plend_bodyd (X:=X) xπ Φ ⊣⊢ plend_body (λ P, ⟦ P ⟧ˢ) xπ Φ.
  Proof. unfold plend_body. by setoid_rewrite nintpS_nintp. Qed.
  Local Lemma plend_body_vard_as {X ξ Φ} :
    plend_body_vard (X:=X) ξ Φ ⊣⊢ plend_body_var (λ P, ⟦ P ⟧ˢ) ξ Φ.
  Proof. exact plend_bodyd_as. Qed.

  (** Create new prophetic borrowers and lenders *)
  Lemma pborc_plend_new_list `{!GenUpd M} α Xl (xΦl : plist _ Xl) :
    ⊢ |==> ∃ ξl, ∀ Yl (yπΨl : plist (λ Y, _ *' (Y → _)) Yl),
      let ξxΦl := plist_zip ξl xΦl in
      ([∗ plist] '(x, Φ)' ∈ xΦl, ⟦ Φ x ⟧) -∗
      ([†α] -∗ ([∗ plist] '(ξ, x, Φ)' ∈ ξxΦl, plend_body_vard ξ Φ) -∗ M
        ([∗ plist] '(yπ, Ψ)' ∈ yπΨl, plend_bodyd yπ Ψ)) =[pborrow_wsatd M]=∗
        ([∗ plist] '(ξ, x, Φ)' ∈ ξxΦl, pborcd α x ξ Φ) ∗
        ([∗ plist] '(yπ, Ψ)' ∈ yπΨl, plendd α yπ Ψ).
  Proof.
    iMod (pbor_plend_tok_new_list (intp:=λ P, ⟦ P ⟧ˢ)) as (?) "big".
    iModIntro. iExists _. iIntros "%% Φl →Ψl". setoid_rewrite plend_bodyd_as.
    setoid_rewrite <-nintpS_nintp. setoid_rewrite <-pborc_intro.
    setoid_rewrite <-plend_intro. iApply ("big" with "Φl →Ψl").
  Qed.
  (** Simply create a prophetic borrower and a prophetic lender *)
  Lemma pborc_plend_new `{!GenUpd M} α X (x : X) Φ :
    ⟦ Φ x ⟧ =[pborrow_wsatd M]=∗ ∃ ξ, pborcd α x ξ Φ ∗ plendd α (λ π, π ξ) Φ.
  Proof.
    iIntros "Φ".
    iMod (pborc_plend_new_list α [X] ((x, Φ)',())') as ([ξ[]]) "big". iExists ξ.
    iMod ("big" $! [X] ((_,_)',())' with "[Φ] []") as "[[$ _][$ _]]"=>/=;
      by [iFrame|iIntros|].
  Qed.

  (** Split a prophetic lender *)
  Lemma plend_split `{!GenUpd M} {α X xπ} {Φ : X → _}
    Yl (yπΨl : plist (λ Y, _ *' (Y → _)) Yl) :
    plendd α xπ Φ -∗
    (plend_bodyd xπ Φ -∗ M ([∗ plist] '(yπ, Ψ)' ∈ yπΨl, plend_bodyd yπ Ψ))
      =[pborrow_wsatd M]=∗ [∗ plist] '(yπ, Ψ)' ∈ yπΨl, plendd α yπ Ψ.
  Proof.
    iIntros "[%Ω[ΩΦ l]] →Ψl". rewrite aconvert_use.
    setoid_rewrite <-plend_intro. iApply (plend_tok_split with "l [ΩΦ →Ψl]").
    setoid_rewrite plend_bodyd_as. iIntros "[%[obs Ω]]".
    setoid_rewrite <-nintpS_nintp. iMod ("ΩΦ" with "Ω") as "Φ".
    iApply ("→Ψl" with "[obs Φ]"). iExists _. iFrame.
  Qed.

  (** Retrieve from a prophetic lender *)
  Lemma plend_retrieve `{!GenUpd M} {α X xπ} {Φ : X → _} :
    [†α] -∗ plendd α xπ Φ -∗ modw M (pborrow_wsatd M) (plend_bodyd xπ Φ).
  Proof.
    iIntros "† [%[ΨΦ l]]". rewrite aconvert_use. setoid_rewrite <-nintpS_nintp.
    iMod (plend_tok_retrieve with "† l") as "[%[obs Ψ]]".
    iMod ("ΨΦ" with "Ψ") as "Φ". iApply modw_fold. rewrite plend_bodyd_as.
    iExists _. iFrame. by iIntros.
  Qed.

  (** Open a prophetic borrower *)
  Lemma pborc_open `{!GenUpd M} {α q X x ξ} {Φ : X → _} :
    q.[α] -∗ pborcd α x ξ Φ =[pborrow_wsatd M]=∗ opbord α q ξ Φ ∗ ⟦ Φ x ⟧.
  Proof.
    iIntros "α [%[ΦΨ[ΨΦ c]]]". rewrite (aconvert_use (Φ:=Ψ)) /=.
    iMod (pbor_ctok_open with "α c") as "[o Φ]". rewrite nintpS_nintp.
    iMod ("ΨΦ" with "Φ") as "$". iExists _. by iFrame.
  Qed.
  Lemma pbor_open `{!GenUpd M} {α q X x ξ} {Φ : X → _} :
    q.[α] -∗ pbord α x ξ Φ -∗ modw M (pborrow_wsatd M)
      (opbord α q ξ Φ ∗ ⟦ Φ x ⟧).
  Proof.
    iIntros "α [%[ΦΨ[ΨΦ b]]]". rewrite (aconvert_use (Φ:=Ψ)) /=.
    iMod (pbor_tok_open with "α b") as "[o Φ]". rewrite nintpS_nintp.
    iMod ("ΨΦ" with "Φ") as "$". iApply modw_fold. iExists _. iFrame.
    by iIntros.
  Qed.

  (** Lemma for [opbor_merge_subdiv] *)
  Local Lemma opbor_plist {Xl A β}
    {αqξΦfl : plist (λ X, _ *' _ *' _ *' _ *' (A → X)) Xl} :
    ([∗ plist] '(α, q, ξ, Φ, _)' ∈ αqξΦfl, β ⊑□ α ∗ opbord α q ξ Φ) ⊢
      ∃ αqξΩfl : plist (λ X, _ *' _ *' _ *' _ *' (A → X)) Xl,
      ⌜plist_map (λ _ '(α, q, _)', (α, q)') αqξΦfl =
        plist_map (λ _ '(α, q, _)', (α, q)') αqξΩfl⌝ ∗
      ⌜plist_map (λ _ '(_, _, ξ, _, f)', (ξ, f)') αqξΦfl =
        plist_map (λ _ '(_, _, ξ, _, f)', (ξ, f)') αqξΩfl⌝ ∗
      ([∗ plist] '(α, q, ξ, Ω, _)' ∈ αqξΩfl, β ⊑□ α ∗ opbor_tok α q ξ Ω) ∗
      (∀ a, ([∗ plist] '(_, _, _, Φ, f)' ∈ αqξΦfl, ⟦ Φ (f a) ⟧) ==∗
        [∗ plist] '(_, _, _, Ω, f)' ∈ αqξΩfl, ⟦ Ω (f a) ⟧).
  Proof.
    elim: Xl αqξΦfl=>/=.
    { iIntros. iExists (). do 2 (iSplit; [done|]). by iIntros. }
    move=> X Xl IH [[α[q[ξ[Φ f]]]] αqξΦfl]. rewrite IH.
    iIntros "[[⊑[%Ω[ΦΩ o]]][%αqξΩfl[%[%[ol →']]]]]". rewrite aconvert_use.
    iExists ((α, q, ξ, Ω, f)', αqξΩfl)'=>/=. iFrame "⊑ o ol".
    do 2 (iSplit; [iPureIntro; by f_equal|]). iIntros (a) "[Φ Φl]".
    iMod ("ΦΩ" with "Φ") as "$". iApply ("→'" with "Φl").
  Qed.
  (** Merge and subdivide prophetic borrowers *)
  Lemma opbor_merge_subdiv `{!GenUpd M} Xl Yl
    (αqξΦfl : plist (λ X, _ *' _ *' _ *' _ *' (_ → X)) Xl) (yΨl : plist _ Yl) Rl
    β :
    ([∗ plist] '(α, q, ξ, Φ, _)' ∈ αqξΦfl, β ⊑□ α ∗ opbord α q ξ Φ) -∗
    ([∗ plist] '(y, Ψ)' ∈ yΨl, ⟦ Ψ y ⟧) -∗ ([∗ list] R ∈ Rl, ⟦ R ⟧) -∗
    (∀ yl', [†β] -∗ ([∗ plist] '(y', _, Ψ)' ∈ plist_zip yl' yΨl, ⟦ Ψ y' ⟧) -∗
      ([∗ list] R ∈ Rl, ⟦ R ⟧) -∗ M
        ([∗ plist] '(_, _, _, Φ, f)' ∈ αqξΦfl, ⟦ Φ (f yl') ⟧))
      =[pborrow_wsatd M]=∗ ∃ ηl,
      ([∗ plist] '(α, q, _)' ∈ αqξΦfl, q.[α]) ∗
      ([∗ plist] '(_, _, ξ, _, f)' ∈ αqξΦfl,
        ⟨π, π (Aprvar _ ξ) = f (app_plist_prvar π ηl)⟩) ∗
      ([∗ plist] '(η, y, Ψ)' ∈ plist_zip ηl yΨl, pborcd β y η Ψ) ∗
      [∗ list] R ∈ Rl, borcd β R.
  Proof.
    rewrite opbor_plist /= -bi.sep_exist_l. setoid_rewrite <-nintpS_nintp.
    rewrite -(big_sepPL_map (λ _ '(α, q, _)', (α, q)') (λ _ '(α, q)', q.[α])%I).
    iIntros "[%[->[%eq[ol →]]]] Ψl Rl →Φl". rewrite big_sepPL_map.
    setoid_rewrite <-pborc_intro. setoid_rewrite <-borc_intro.
    iMod (opbor_tok_merge_subdiv (intp:=λ P, ⟦ P ⟧ˢ) with "ol Ψl Rl [→ →Φl]")
      as (?) "[$[obsl[bl $]]]".
    { iIntros "% † Ψl Rl". iMod ("→Φl" with "† Ψl Rl") as "Φl".
      iMod ("→" with "Φl") as "$". by iIntros. }
    iModIntro. iExists _. iFrame "bl".
    by rewrite -(big_sepPL_map (λ _ '(_, _, ξ, _, f)', (ξ, f)')
      (λ _ '(ξ, f)', ⟨π, π (Aprvar _ ξ) = f (app_plist_prvar π ηl)⟩)%I)
      -eq big_sepPL_map.
  Qed.
  (** Subdivide a prophetic borrower *)
  Lemma opbor_subdiv `{!GenUpd M} {X α q ξ Φ} Yl (f : _ → X) (yΨl : plist _ Yl)
    Rl β :
    β ⊑□ α -∗ opbord α q ξ Φ -∗
    ([∗ plist] '(y, Ψ)' ∈ yΨl, ⟦ Ψ y ⟧) -∗ ([∗ list] R ∈ Rl, ⟦ R ⟧) -∗
    (∀ yl', [†β] -∗ ([∗ plist] '(y', _, Ψ)' ∈ plist_zip yl' yΨl, ⟦ Ψ y' ⟧) -∗
      ([∗ list] R ∈ Rl, ⟦ R ⟧) -∗ M ⟦ Φ (f yl') ⟧) =[pborrow_wsatd M]=∗ ∃ ηl,
      q.[α] ∗ ⟨π, π (Aprvar _ ξ) = f (app_plist_prvar π ηl)⟩ ∗
      ([∗ plist] '(η, y, Ψ)' ∈ plist_zip ηl yΨl, pborcd β y η Ψ) ∗
      [∗ list] R ∈ Rl, borcd β R.
  Proof.
    iIntros "⊑ o Ψl Rl →Φ".
    iMod (opbor_merge_subdiv [_] _ ((_,_,_,_,_)',())'
      with "[$⊑ $o //] Ψl Rl [→Φ]") as (ηl) "big"=>/=.
    { iIntros (?). by rewrite bi.sep_emp. }
    iExists ηl. by iDestruct "big" as "/=[[$ _][[$ _]$]]".
  Qed.

  (** Resolve the prophecy of a prophetic borrower *)
  Lemma opbor_resolve `{!GenUpd M} {X α q ξ Φ} (x : X) :
    opbord α q ξ Φ -∗ ⟦ Φ x ⟧ =[pborrow_wsatd M]=∗
      q.[α] ∗ ⟨π, π ξ = x⟩ ∗ borcd α (Φ x).
  Proof.
    iIntros "o Φ".
    iMod (opbor_subdiv [] (λ _, x) () [Φ x] with "[] o [//] [Φ] []")
      as (?) "[$[$[_[$ _]]]]"=>/=;
      by [iApply lft_sincl_refl|iFrame|iIntros "% _ _ [$ _]"|].
  Qed.
  Lemma pborc_resolve `{!GenUpd M} {X α q x ξ} {Φ : X → _} :
    q.[α] -∗ pborcd α x ξ Φ =[pborrow_wsatd M]=∗
      q.[α] ∗ ⟨π, π ξ = x⟩ ∗ borcd α (Φ x).
  Proof.
    iIntros "α c". iMod (pborc_open with "α c") as "[o Φ]".
    iApply (opbor_resolve with "o Φ").
  Qed.
  Lemma pbor_resolve `{!GenUpd M} {X α q x ξ} {Φ : X → _} :
    q.[α] -∗ pbord α x ξ Φ -∗ modw M (pborrow_wsatd M)
      (q.[α] ∗ ⟨π, π ξ = x⟩ ∗ borcd α (Φ x)).
  Proof.
    iIntros "α b". iMod (pbor_open with "α b") as "[o Φ]".
    iMod (opbor_resolve with "o Φ") as "$". by iIntros.
  Qed.

  (** Subdivide a prophetic borrower without changing the prophecy *)
  Lemma opbor_nsubdiv `{!GenUpd M} {X α q ξ Φ} Ψ (x : X) β :
    β ⊑□ α -∗ opbord α q ξ Φ -∗ ⟦ Ψ x ⟧ -∗
    (∀ y, [†β] -∗ ⟦ Ψ y ⟧ -∗ M ⟦ Φ y ⟧) =[pborrow_wsatd M]=∗
      q.[α] ∗ pborcd β x ξ Ψ.
  Proof.
    iIntros "⊑ [%Ω[ΦΩ o]] Ψ →Φ". rewrite aconvert_use -pborc_intro.
    setoid_rewrite <-nintpS_nintp.
    iApply (opbor_tok_nsubdiv (intp:=λ P, ⟦ P ⟧ˢ) with "⊑ o Ψ [ΦΩ →Φ]").
    iIntros "% † Ψ". iMod ("→Φ" with "† Ψ") as "Φ". iMod ("ΦΩ" with "Φ") as "$".
    by iIntros.
  Qed.
  (** Simply close a prophetic borrower *)
  Lemma opbor_close `{!GenUpd M} {X α q ξ Φ} (x : X) :
    opbord α q ξ Φ -∗ ⟦ Φ x ⟧ =[pborrow_wsatd M]=∗ q.[α] ∗ pborcd α x ξ Φ.
  Proof.
    iIntros "o Φ". iApply (opbor_nsubdiv Φ with "[] o Φ"); [|by iIntros].
    iApply lft_sincl_refl.
  Qed.

  (** Lemma for [opbor_opbor_reborrow] *)
  Local Lemma opbor_opbor_tok `{!GenUpd M} {Y β r η Ψ} {y : Y} :
    opbord β r η Ψ -∗ ⟦ Ψ y ⟧ =[pborrow_wsatd M]=∗ opbor_tok β r η Ψ ∗ ⟦ Ψ y ⟧ˢ.
  Proof.
    iIntros "[%Ψ'[ΨΨ' o']] Ψ". rewrite aconvert_use.
    setoid_rewrite <-nintpS_nintp.
    iMod (opbor_tok_nsubdiv (intp:=λ P, ⟦ P ⟧ˢ) with "[] o' Ψ [ΨΨ']")
      as "[β c]". { iApply lft_sincl_refl. }
    { iIntros "% _ Ψ". iMod ("ΨΨ'" with "Ψ") as "$". by iIntros. }
    iApply (pbor_ctok_open with "β c").
  Qed.
  (** Reborrow a nested prophetic borrower *)
  Lemma opbor_opbor_reborrow `{!GenUpd M} {X Y α q ξ Φ β r η Ψ} y (f : X → Y) :
    opbord α q ξ Φ -∗ opbord β r η Ψ -∗ ⟦ Ψ y ⟧ -∗
    (∀ y', [†α] -∗ pbord β y' η Ψ -∗ M ⟦ Φ (f y') ⟧) =[pborrow_wsatd M]=∗ ∃ η',
      q.[α] ∗ r.[β] ∗ ⟨π, π ξ = f (π (Aprvar _ η'))⟩ ∗ pborcd (α ⊓ β) y η' Ψ.
  Proof.
    iIntros "[%Φ'[ΦΦ' o]] o' Ψ →Φ". rewrite aconvert_use.
    iMod (opbor_opbor_tok with "o' Ψ") as "[o' Ψ]".
    iMod (opbor_opbor_tok_reborrow (intp:=λ P, ⟦ P ⟧ˢ) with "o o' Ψ [ΦΦ' →Φ]")
      as (?) "[$[$ ?]]".
    { iIntros "% † b". rewrite pbor_intro nintpS_nintp.
      iMod ("→Φ" with "† b") as "Φ". iMod ("ΦΦ'" with "Φ") as "$". by iIntros. }
    iExists _. by rewrite pborc_intro.
  Qed.
  Lemma opbor_pborc_reborrow `{!GenUpd M} {X Y α q ξ Φ β r y η Ψ} (f : X → Y) :
    opbord α q ξ Φ -∗ r.[β] -∗ pborcd β y η Ψ -∗
    (∀ y', [†α] -∗ pbord β y' η Ψ -∗ M ⟦ Φ (f y') ⟧) =[pborrow_wsatd M]=∗ ∃ η',
      q.[α] ∗ r.[β] ∗ ⟨π, π ξ = f (π (Aprvar _ η'))⟩ ∗ pborcd (α ⊓ β) y η' Ψ.
  Proof.
    iIntros "o r c →Φ". iMod (pborc_open with "r c") as "[o' Ψ]".
    by iMod (opbor_opbor_reborrow with "o o' Ψ →Φ").
  Qed.
  Lemma opbor_pbor_reborrow `{!GenUpd M} {X Y α q ξ Φ β r y η Ψ} (f : X → Y) :
    opbord α q ξ Φ -∗ r.[β] -∗ pbord β y η Ψ -∗
    (∀ y', [†α] -∗ pbord β y' η Ψ -∗ M ⟦ Φ (f y') ⟧) -∗ modw M (pborrow_wsatd M)
      (∃ η', q.[α] ∗ r.[β] ∗ ⟨π, π ξ = f (π (Aprvar _ η'))⟩ ∗
        pborcd (α ⊓ β) y η' Ψ).
  Proof.
    iIntros "o r b →Φ". iMod (pbor_open with "r b") as "[o' Ψ]".
    by iMod (opbor_opbor_reborrow with "o o' Ψ →Φ").
  Qed.
End borrow.
