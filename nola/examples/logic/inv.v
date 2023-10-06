(** * On the invariant *)

From nola.examples.logic Require Export deriv.

Implicit Type P Q : nPropL (;ᵞ).

Section lemmas.
  Context `{!nintpGS Σ}.

  (** Access [nninv] *)
  Lemma nninv_acc {N P E} : ↑N ⊆ E →
    nninvd N P =[nninv_wsatd]{E,E∖↑N}=∗
      ⟦ P ⟧ ∗ (⟦ P ⟧ =[nninv_wsatd]{E∖↑N,E}=∗ True).
  Proof.
    rewrite nninv_unseal. iIntros (NE) "#∝P". iDestruct nderiv_sound as "→".
    iDestruct ("→" with "∝P") as "/={∝P}∝P". by iApply "∝P".
  Qed.

  Context `{!nderivy ih δ}.

  (** Turn [ninv] into [nninv] *)
  Lemma ninv_nninv (P : nPropS _) {N} :
    ninv N (nInvd_u P) -∗ nninv (Σ:=Σ) δ N (↑ˡ P).
  Proof.
    rewrite nninv_unseal. iIntros "#NP !>". iApply (derivy_intro (δ:=δ))=>/=.
    iIntros (?????). rewrite -nintpS_nintp_nlarge.
    by iApply (ninv_acc with "NP").
  Qed.

  (** Allocate [nninv] *)
  Lemma nninv_alloc_rec (P : nPropS _) {N} :
    (nninv δ N (↑ˡ P) -∗ ⟦ P ⟧(δ)) =[nninv_wsat δ]=∗ nninv δ N (↑ˡ P).
  Proof.
    iIntros "→P".
    iMod (ninv_alloc_rec (P:=nInvd_u P) with "[→P]") as "NP".
    - iIntros "/=NP". rewrite nintpS_nintp. iApply "→P". by iApply ninv_nninv.
    - iModIntro. by iApply ninv_nninv.
  Qed.
  Lemma nninv_alloc (P : nPropS _) {N} :
    ⟦ P ⟧(δ) =[nninv_wsat δ]=∗ nninv δ N (↑ˡ P).
  Proof. iIntros "P". iApply (nninv_alloc_rec with "[P]"). by iIntros. Qed.

  (** Transform [nninv] *)
  Lemma nninv_convert {N P Q} :
    □ ⸨ P ={∅}=∗ Q ∗ (Q ={∅}=∗ P) ⸩(δ) -∗ nninv δ N P -∗ nninv δ N Q.
  Proof.
    rewrite nninv_unseal. iIntros "#PQP #∝P !>".
    iApply (derivy_map2 with "[] PQP ∝P")=>/=.
    iIntros (???) "/= {PQP}PQP {∝P}∝P". iIntros (? NE).
    iMod ("∝P" $! _ NE) as "[P P→]".
    iMod (fupd_mask_subseteq ∅) as "→E∖N"; [set_solver|].
    iMod ("PQP" with "P") as "($& QP)". iMod "→E∖N" as "_". iIntros "!> Q".
    iMod (fupd_mask_subseteq ∅) as "→E∖N"; [set_solver|].
    iMod ("QP" with "Q") as "P". iMod "→E∖N" as "_". iApply ("P→" with "P").
  Qed.
  Lemma nninv_split {N P Q} :
    nninv δ N (P ∗ Q) ⊢ nninv δ N P ∗ nninv δ N Q.
  Proof.
    iIntros "#NPQ". iSplit; iApply (nninv_convert with "[] NPQ"); iModIntro;
    iApply (derivy_intro (δ:=δ)); by iIntros (???) "/=[$$]!>$".
  Qed.
  Lemma nninv_fupd {N P} :
    nninv δ N (|={∅}=> P) ⊣⊢ nninv δ N P.
  Proof.
    iSplit; iApply nninv_convert; iModIntro; iApply (derivy_intro (δ:=δ))=>/=;
      iIntros (???); by [iIntros ">$!>$"|iIntros "$!>"; iSplitR; iIntros].
  Qed.
  Lemma nninv_add {N P Q} :
    □ ⸨ P ⸩(δ) -∗ nninv δ N Q -∗ nninv δ N (P ∗ Q).
  Proof.
    iIntros "#P". iApply nninv_convert. iModIntro.
    iApply (derivy_map with "[] P"). by iIntros (???) "/=$$!>[_$]".
  Qed.

  (** Combine [nninv]s *)
  Lemma nninv_combine {N N' N'' P Q} : N ## N' → ↑N ∪ ↑N' ⊆@{coPset} ↑N'' →
    nninv δ N P -∗ nninv δ N' Q -∗ nninv δ N'' (P ∗ Q).
  Proof.
    rewrite nninv_unseal. iIntros (??) "#NP #N'Q !>".
    iApply (derivy_map2 (δ:=δ) with "[] NP N'Q")=>/=.
    iIntros (???) "{NP}NP {N'Q}N'Q". iIntros (??).
    iMod ("NP" with "[%]") as "[$ P→]"; [set_solver|].
    iMod ("N'Q" with "[%]") as "[$ Q→]"; [set_solver|].
    iApply fupdw_mask_intro; [set_solver|]. iIntros "cl [P Q]".
    iMod "cl" as "_". iMod ("Q→" with "Q") as "_". iApply ("P→" with "P").
  Qed.
End lemmas.
