(** * On the borrowing *)

From nola.examples.logic Require Export deriv.

(** ** On [conv] *)
Section conv.
  Context `{!nintpGS Σ}.

  (** Use [convd] *)
  Lemma convd_use {P Q} : convd P Q ⊢ ∀ E, ⟦ P ⟧ ={E}=∗ ⟦ Q ⟧.
  Proof.
    iIntros "c". iDestruct nderiv_sound as "→". iApply ("→" with "c").
  Qed.

  Context `{!nderivy ih δ}.

  (** Introduce [conv] *)
  Lemma conv_intro P Q : (∀ δ' E, ⟦ P ⟧(δ') ={E}=∗ ⟦ Q ⟧(δ')) ⊢ conv δ P Q.
  Proof.
    iIntros "→". iApply (derivy_intro (δ:=δ))=>/=. iIntros. by iApply "→".
  Qed.
  Lemma conv_refl P : ⊢ conv δ P P.
  Proof. rewrite -conv_intro. by iIntros "%% ?". Qed.

  (** Modify [conv] *)
  Lemma conv_trans P Q R : conv δ P Q -∗ conv δ Q R -∗ conv δ P R.
  Proof.
    iIntros "PQ QR". iApply (derivy_map2 (δ:=δ) with "[] PQ QR")=>/=.
    iIntros "% _ _ PQ QR % P". iMod ("PQ" with "P") as "Q". by iApply "QR".
  Qed.
End conv.

(** ** On borrowing *)

Section borrow.
  Context `{!nintpGS Σ, !nderivy ih δ}.

  (** Modify tokens with [conv] *)
  Lemma borc_conv {α P Q} :
    □ conv δ P Q -∗ □ conv δ Q P -∗ borc δ α P -∗ borc δ α Q.
  Proof.
    iIntros "#? #? [%[#?[#? c]]]". iExists _. iFrame "c".
    iSplit; iModIntro; by iApply conv_trans.
  Qed.
  Lemma bor_conv {α P Q} :
    □ conv δ P Q -∗ □ conv δ Q P -∗ bor δ α P -∗ bor δ α Q.
  Proof.
    iIntros "#? #? [%[#?[#? b]]]". iExists _. iFrame "b".
    iSplit; iModIntro; by iApply conv_trans.
  Qed.
  Lemma boro_conv {α P Q q} :
    □ conv δ P Q -∗ □ conv δ Q P -∗ boro δ α P q -∗ boro δ α Q q.
  Proof.
    iIntros "#? #? [%[#?[#? o]]]". iExists _. iFrame "o".
    iSplit; iModIntro; by iApply conv_trans.
  Qed.
  Lemma lend_conv {α P Q} : □ conv δ P Q -∗ lend δ α P -∗ lend δ α Q.
  Proof.
    iIntros "#? [%[#? l]]". iExists _. iFrame "l". iModIntro.
    by iApply conv_trans.
  Qed.

  (** Modify tokens with lifetime inclusion *)
  Lemma borc_lft {α α' P} : α' ⊑□ α -∗ borc δ α P -∗ borc δ α' P.
  Proof.
    iIntros "⊑ [%[?[? c]]]". iDestruct (bor_ctok_lft with "⊑ c") as "c".
    iExists _. iFrame.
  Qed.
  Lemma bor_lft {α α' P} : α' ⊑□ α -∗ bor δ α P -∗ bor δ α' P.
  Proof.
    iIntros "⊑ [%[?[? b]]]". iDestruct (bor_tok_lft with "⊑ b") as "b".
    iExists _. iFrame.
  Qed.
  Lemma bor_olft {α α' P q r} :
    α' ⊑□ α -∗ (q.[α] -∗ r.[α']) -∗ boro δ α P q -∗ boro δ α' P r.
  Proof.
    iIntros "⊑ → [%[?[? o]]]". iDestruct (bor_otok_lft with "⊑ → o") as "o".
    iExists _. iFrame.
  Qed.
  Lemma lend_lft {α α' P} : α ⊑□ α' -∗ lend δ α P -∗ lend δ α' P.
  Proof.
    iIntros "⊑ [%[? l]]". iDestruct (lend_tok_lft with "⊑ l") as "l".
    iExists _. iFrame.
  Qed.

  (** Other conversion *)
  Lemma borc_bor {α P} : borc δ α P ⊢ bor δ α P.
  Proof. iIntros "[% c]". rewrite bor_ctok_tok. by iExists _. Qed.
  Lemma borc_fake {α} (P : nPropS (;ᵞ)) : [†α] ⊢ borc δ α (↑ˡ P).
  Proof.
    iIntros "†". iExists _. rewrite bor_ctok_fake. iFrame "†".
    iSplitR; iModIntro; iApply conv_refl.
  Qed.
  Lemma bor_fake {α} (P : nPropS (;ᵞ)) : [†α] ⊢ bor δ α (↑ˡ P).
  Proof. by rewrite borc_fake borc_bor. Qed.
End borrow.

Section borrow.
  Context `{!nintpGS Σ}.

  (** Create borrowers and lenders *)
  Lemma borc_lend_new_list α (Pl Ql : list (nPropS (;ᵞ))) :
    ([∗ list] P ∈ Pl, ⟦ P ⟧) -∗
    ([†α] -∗ ([∗ list] P ∈ Pl, ⟦ P ⟧) ={∅}=∗ [∗ list] Q ∈ Ql, ⟦ Q ⟧)
    =[borrow_wsatd]=∗
      ([∗ list] P ∈ Pl, borcd α (↑ˡ P)) ∗ [∗ list] Q ∈ Ql, lendd α (↑ˡ Q).
  Proof.
    iIntros "Pl →Ql". setoid_rewrite <-nintpS_nintp.
    iMod (bor_lend_tok_new_list with "Pl [→Ql]") as "[bl ll]".
    { iIntros "#† ? _". iSplitR; [done|]. by iApply "→Ql". }
    iModIntro. iSplitL "bl"; iStopProof; do 3 f_equiv; iIntros "?"; iExists _.
    - by do 2 (iSplit; [iModIntro; by iApply conv_refl|]).
    - by iSplit; [iModIntro; by iApply conv_refl|].
  Qed.
  (** Simply create a borrower and a lender *)
  Lemma borc_lend_new α (P : nPropS (;ᵞ)) :
    ⟦ P ⟧ -∗ ([†α] -∗ ⟦ P ⟧ ={∅}=∗ ⟦ P ⟧) =[borrow_wsatd]=∗
      borcd α (↑ˡ P) ∗ lendd α (↑ˡ P).
  Proof.
    iIntros "P". iMod (borc_lend_new_list α [P] [P] with "[P] []")
      as "[[$_][$_]]"; by [iFrame|iIntros|].
  Qed.

  (** Extend a lender *)
  Lemma lend_extend {α P} (Ql : list (nPropS (;ᵞ))) :
    lendd α P -∗ (⟦ P ⟧ ={∅}=∗ [∗ list] Q ∈ Ql, ⟦ Q ⟧) =[borrow_wsatd]=∗
      [∗ list] Q ∈ Ql, lendd α (↑ˡ Q).
  Proof.
    iIntros "[%P'[#→P l]] →Ql". rewrite convd_use.
    iMod (lend_tok_extend with "l [→P →Ql]") as "ll"=>/=.
    { rewrite nintpS_nintp_nlarge. setoid_rewrite nintpS_nintp. iIntros "P'".
      iMod ("→P" with "P'") as "P". by iMod ("→Ql" with "P"). }
    iModIntro. iApply (big_sepL_impl with "ll"). iIntros "!> %% _ l".
    iExists _. iFrame "l". iModIntro. iApply conv_refl.
  Qed.

  (** Retrive from [lend] *)
  Lemma lend_retrieve {E α P} :
    [†α] -∗ lendd α P =[borrow_wsatd]{E}=∗ ⟦ P ⟧.
  Proof.
    iIntros "† [%[→ l]]". rewrite convd_use.
    iMod (lend_tok_retrieve with "† l") as "Q"; [set_solver|].
    rewrite nintpS_nintp_nlarge. by iMod ("→" with "Q").
  Qed.

  (** Open a closed borrower *)
  Lemma borc_open {E q α P} :
    q.[α] -∗ borcd α P =[borrow_wsatd]{E}=∗ borod α P q ∗ ⟦ P ⟧.
  Proof.
    iIntros "α [%Q[PQ[#QP c]]]". iMod (bor_ctok_open with "α c") as "[o Q]".
    rewrite nintpS_nintp_nlarge. iMod (convd_use with "QP Q") as "$". iModIntro.
    iExists _. by iFrame.
  Qed.
  (** Open a borrower *)
  Lemma bor_open {E q α P} :
    q.[α] -∗ bord α P =[borrow_wsatd]{E}=∗ borod α P q ∗ ⟦ P ⟧.
  Proof.
    iIntros "α [%Q[PQ[#QP b]]]".
    iMod (bor_tok_open with "α b") as "[o Q]"; [set_solver|].
    rewrite nintpS_nintp_nlarge. iMod (convd_use with "QP Q") as "$". iModIntro.
    iExists _. by iFrame.
  Qed.

  (** Destruct [borod]s *)
  Local Lemma boro_list {α Pql E} :
    ([∗ list] '(P, q)' ∈ Pql, borod α P q) -∗ ∃ Rql, ⌜Rql.*2' = Pql.*2'⌝ ∗
      ([∗ list] '(R, q)' ∈ Rql, bor_otok α R q) ∗
      (([∗ list] P ∈ Pql.*1', ⟦ P ⟧) ={E}=∗ [∗ list] R ∈ Rql.*1', ⟦ ↑ˡ R ⟧).
  Proof.
    elim: Pql=>/=.
    { iIntros. iExists []=>/=. do 2 (iSplit; [done|]). by iIntros. }
    iIntros ([P q] Pql IH) "[[%R[#→[_ o]]] Pql]". rewrite convd_use.
    iDestruct (IH with "Pql") as (Rql ?) "[ol →']".
    iExists ((R, q)' :: Rql)=>/=. iFrame "o ol". iSplit.
    { iPureIntro. by f_equal. } iIntros "[P Pl]".
    iMod ("→" with "P") as "$". iApply ("→'" with "Pl").
  Qed.
  (** Merge and subdivide borrowers *)
  Lemma boro_merge_subdiv {α} Pql (Ql : list (nPropS (;ᵞ))) :
    ([∗ list] '(P, q)' ∈ Pql, borod α P q) -∗ ([∗ list] Q ∈ Ql, ⟦ Q ⟧) -∗
    ([†α] -∗ ([∗ list] Q ∈ Ql, ⟦ Q ⟧) ={∅}=∗ [∗ list] P ∈ Pql.*1', ⟦ P ⟧)
      =[borrow_wsatd]=∗
      ([∗ list] q ∈ Pql.*2', q.[α]) ∗ [∗ list] Q ∈ Ql, borcd α (↑ˡ Q).
  Proof.
    setoid_rewrite <-nintpS_nintp. iIntros "ol Ql →Pl".
    iDestruct (boro_list with "ol") as (?<-) "[ol →]".
    iMod (bor_otok_merge_subdiv with "ol Ql [→ →Pl]") as "[$ ?]".
    { iIntros "† Ql". iMod ("→Pl" with "† Ql") as "Pl".
      iMod ("→" with "Pl"). by setoid_rewrite nintpS_nintp_nlarge. }
    iModIntro. iStopProof. do 3 f_equiv. iIntros "c". iExists _. iFrame "c".
    iSplit; iModIntro; by iApply conv_refl.
  Qed.
  (** Subdivide borrowers *)
  Lemma boro_subdiv {α P q} (Ql : list (nPropS (;ᵞ))) :
    borod α P q -∗ ([∗ list] Q ∈ Ql, ⟦ Q ⟧) -∗
    ([†α] -∗ ([∗ list] Q ∈ Ql, ⟦ Q ⟧) ={∅}=∗ ⟦ P ⟧) =[borrow_wsatd]=∗
      q.[α] ∗ [∗ list] Q ∈ Ql, borcd α (↑ˡ Q).
  Proof.
    iIntros "o Ql →P".
    iMod (boro_merge_subdiv [(_,_)'] with "[o] Ql [→P]") as "[[$ _]$]"=>/=;
      by [iFrame|rewrite bi.sep_emp|].
  Qed.
  (** Simply close a borrower *)
  Lemma bor_close {E q α P} :
    borod α P q -∗ ⟦ P ⟧ =[borrow_wsatd]{E}=∗ q.[α] ∗ borcd α P.
  Proof.
    iIntros "[%Q[#PQ[QP o]]] P". iMod (convd_use with "PQ P") as "Q".
    rewrite -nintpS_nintp_nlarge.
    iMod (bor_tok_close (intp:=λ Q, ⟦ Q ⟧ˢ) with "o Q") as "[$ c]". iModIntro.
    iExists _. by iFrame.
  Qed.

  (** Reborrow a borrower *)
  Lemma boro_reborrow {E α P q} β :
    borod α P q -∗ ⟦ P ⟧ =[borrow_wsatd]{E}=∗
      q.[α] ∗ borcd (α ⊓ β) P ∗ ([†β] -∗ bord α P).
  Proof.
    iIntros "[%Q[#PQ[#QP o]]] P". iMod (convd_use with "PQ P") as "Q".
    rewrite -nintpS_nintp_nlarge.
    iMod (bor_otok_reborrow (intp:=λ Q, ⟦ Q ⟧ˢ) with "o Q") as "[$[c →o]]".
    iModIntro. iSplitL "c".
    - iExists _. iFrame "c". by iSplit.
    - iIntros "†". iExists _. iDestruct ("→o" with "†") as "$". by iSplit.
  Qed.
  Lemma borc_reborrow {E α P q} β :
    q.[α] -∗ borcd α P =[borrow_wsatd]{E}=∗
      q.[α] ∗ borcd (α ⊓ β) P ∗ ([†β] -∗ bord α P).
  Proof.
    iIntros "α c". iMod (borc_open with "α c") as "[o P]".
    by iMod (boro_reborrow with "o P").
  Qed.
  Lemma bor_reborrow {E α P q} β :
    q.[α] -∗ bord α P =[borrow_wsatd]{E}=∗
      q.[α] ∗ borcd (α ⊓ β) P ∗ ([†β] -∗ bord α P).
  Proof.
    iIntros "α b". iMod (bor_open with "α b") as "[o P]".
    by iMod (boro_reborrow with "o P").
  Qed.
End borrow.
