(** * On the invariant *)

From nola.examples.logic Require Export deriv.

Implicit Type P Q : nPropL (;ᵞ).

Section lemmas.
  Context `{!nintpGS Σ}.
  Implicit Type δ : nderiv_ty Σ.

  (** [ninv] is persistent *)
  #[export] Instance ninv_persistent {δ N P} : Persistent (ninv δ N P).
  Proof. rewrite ninv_unseal. exact _. Qed.

  (** Access [ninv] *)
  Lemma ninv_acc {N P E} : ↑N ⊆ E →
    ninvd N P =[inv_wsatd]{E,E∖↑N}=∗
      ⟦ P ⟧ ∗ (⟦ P ⟧ =[inv_wsatd]{E∖↑N,E}=∗ True).
  Proof.
    rewrite ninv_unseal. iIntros (NE) "#∝P". iDestruct nderiv_sound as "→".
    iDestruct ("→" with "∝P") as "/={∝P}∝P". by iApply "∝P".
  Qed.

  Context `{!nDeriv ih δ}.

  (** Turn [inv_tok] into [ninv] *)
  Local Lemma inv_tok_ninv {P : nPropS _} {N} : inv_tok N P ⊢ ninv δ N (↑ˡ P).
  Proof.
    rewrite ninv_unseal. iIntros "#NP !>". iApply (Deriv_intro (δ:=δ))=>/=.
    iIntros (?????). rewrite -nintpS_nintp_nlarge.
    by iApply (inv_tok_acc with "NP").
  Qed.
  (** Allocate [ninv] *)
  Lemma ninv_alloc_rec (P : nPropS _) N :
    (ninv δ N (↑ˡ P) -∗ ⟦ P ⟧(δ)) =[inv_wsat' δ]=∗ ninv δ N (↑ˡ P).
  Proof. rewrite -inv_tok_ninv -nintpS_nintp. exact: inv_tok_alloc_rec. Qed.
  Lemma ninv_alloc (P : nPropS _) N :
    ⟦ P ⟧(δ) =[inv_wsat' δ]=∗ ninv δ N (↑ˡ P).
  Proof. iIntros "P". iApply (ninv_alloc_rec with "[P]"). by iIntros. Qed.

  (** Alter the content of [ninv] *)
  Lemma ninv_alter {N P Q} :
    □ ⸨ P ={∅}=∗ Q ∗ (Q ={∅}=∗ P) ⸩(δ) -∗ ninv δ N P -∗ ninv δ N Q.
  Proof.
    rewrite ninv_unseal. iIntros "#PQP #∝P !>".
    iApply (Deriv_map2 with "[] PQP ∝P")=>/=.
    iIntros (???) "/= {PQP}PQP {∝P}∝P". iIntros (? NE).
    iMod ("∝P" $! _ NE) as "[P P→]".
    iMod (fupd_mask_subseteq ∅) as "→E∖N"; [set_solver|].
    iMod ("PQP" with "P") as "($& QP)". iMod "→E∖N" as "_". iIntros "!> Q".
    iMod (fupd_mask_subseteq ∅) as "→E∖N"; [set_solver|].
    iMod ("QP" with "Q") as "P". iMod "→E∖N" as "_". iApply ("P→" with "P").
  Qed.
  Lemma ninv_split {N P Q} : ninv δ N (P ∗ Q) ⊢ ninv δ N P ∗ ninv δ N Q.
  Proof.
    iIntros "#NPQ".
    iSplit; iApply (ninv_alter with "[] NPQ"); iModIntro;
      iApply (Deriv_intro (δ:=δ)); by iIntros (???) "/=[$$]!>$".
  Qed.
  Lemma ninv_fupd {N P} : ninv δ N (|={∅}=> P) ⊣⊢ ninv δ N P.
  Proof.
    iSplit; iApply ninv_alter; iModIntro; iApply (Deriv_intro (δ:=δ))=>/=;
      iIntros (???); by [iIntros ">$!>$"|iIntros "$!>"; iSplitR; iIntros].
  Qed.
  Lemma ninv_add {N P Q} : □ ⸨ P ⸩(δ) -∗ ninv δ N Q -∗ ninv δ N (P ∗ Q).
  Proof.
    iIntros "#P". iApply ninv_alter. iModIntro. iApply (Deriv_map with "[] P").
    by iIntros (???) "/=$$!>[_$]".
  Qed.

  (** Combine [ninv]s *)
  Lemma ninv_combine {N N' N'' P Q} : N ## N' → ↑N ∪ ↑N' ⊆@{coPset} ↑N'' →
    ninv δ N P -∗ ninv δ N' Q -∗ ninv δ N'' (P ∗ Q).
  Proof.
    rewrite ninv_unseal. iIntros (??) "#NP #N'Q !>".
    iApply (Deriv_map2 (ih:=ih) with "[] NP N'Q")=>/=.
    iIntros (???) "{NP}NP {N'Q}N'Q". iIntros (??).
    iMod ("NP" with "[%]") as "[$ P→]"; [set_solver|].
    iMod ("N'Q" with "[%]") as "[$ Q→]"; [set_solver|].
    iApply fupdw_mask_intro; [set_solver|]. iIntros "cl [P Q]".
    iMod "cl" as "_". iMod ("Q→" with "Q") as "_". iApply ("P→" with "P").
  Qed.
End lemmas.
