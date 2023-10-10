(** * On the invariant *)

From nola.examples.logic Require Export deriv.

Implicit Type P Q : nPropL (;ᵞ).

Section lemmas.
  Context `{!nintpGS Σ}.

  (** Access [na_ninv] *)
  Lemma na_ninv_acc {p N P E F} : ↑N ⊆ E → ↑N ⊆ F →
    na_ninvd p N P -∗ na_own p F =[inv_wsatd]{E}=∗
      ⟦ P ⟧ ∗ na_own p (F∖↑N) ∗
      (⟦ P ⟧ -∗ na_own p (F∖↑N) =[inv_wsatd]{E}=∗ na_own p F).
  Proof.
    rewrite na_ninv_unseal. iIntros (NE NF) "#∝P F".
    iDestruct nderiv_sound as "→".
    iDestruct ("→" with "∝P") as "/={∝P}∝P".
    iApply ("∝P" $! _ _ NE NF with "F").
  Qed.

  Context `{!nderivy ih δ}.

  (** Turn [na_ninv] into [na_ninv] *)
  Local Lemma na_inv_tok_ninv {P : nPropS _} {i p N} : i ∈ (↑N:coPset) →
    inv_tok N (nInvd_na p i P) ⊢ na_ninv (Σ:=Σ) δ p N (↑ˡ P).
  Proof.
    rewrite na_ninv_unseal. iIntros (jN) "#NP !>".
    iApply (derivy_intro (δ:=δ))=>/=.
    iIntros (??? E F NE NF) "F". rewrite -nintpS_nintp_nlarge.
    iMod (inv_tok_acc NE with "NP") as "/=[bd bd→]".
    iDestruct (na_body_acc with "bd F") as "(bd &$&$& P→)"; [done..|].
    iMod ("bd→" with "bd") as "_". iIntros "!> P F∖N".
    iMod (inv_tok_acc NE with "NP") as "/=[bd bd→]".
    iDestruct ("P→" with "bd P F∖N") as "[bd $]".
    by iMod ("bd→" with "bd") as "_".
  Qed.
  (** Allocate [na_ninv] *)
  Lemma na_ninv_alloc_rec (P : nPropS _) p N :
    (na_ninv δ p N (↑ˡ P) -∗ ⟦ P ⟧(δ)) =[inv_wsat' δ]=∗
      na_ninv δ p N (↑ˡ P).
  Proof.
    iIntros "→P". iMod na_lock_alloc as (i) "[% lock]".
    rewrite -na_inv_tok_ninv; [|done].
    iApply (inv_tok_alloc_rec (nInvd_na p i P) with "[→P lock]").
    iIntros "/=NP". iLeft. iFrame "lock". rewrite nintpS_nintp. by iApply "→P".
  Qed.
  Lemma na_ninv_alloc (P : nPropS _) p N :
    ⟦ P ⟧(δ) =[inv_wsat' δ]=∗ na_ninv δ p N (↑ˡ P).
  Proof.
    iIntros "P". iApply (na_ninv_alloc_rec with "[P]"). by iIntros.
  Qed.

  (** Transform [na_ninv] *)
  Lemma na_ninv_convert {p N P Q} :
    □ ⸨ P ={∅}=∗ Q ∗ (Q ={∅}=∗ P) ⸩(δ) -∗ na_ninv δ p N P -∗ na_ninv δ p N Q.
  Proof.
    rewrite na_ninv_unseal. iIntros "#PQP #∝P !>".
    iApply (derivy_map2 with "[] PQP ∝P")=>/=.
    iIntros (???) "/= {PQP}PQP {∝P}∝P". iIntros (E F NE NF) "F".
    iMod ("∝P" $! E F NE NF with "F") as "(P &$& P→)".
    iMod (fupd_mask_subseteq ∅) as "→E∖N"; [set_solver|].
    iMod ("PQP" with "P") as "($& QP)". iMod "→E∖N" as "_". iIntros "!> Q".
    iMod (fupd_mask_subseteq ∅) as "→E∖N"; [set_solver|].
    iMod ("QP" with "Q") as "P". iMod "→E∖N" as "_". iApply ("P→" with "P").
  Qed.
  Lemma na_ninv_split {p N P Q} :
    na_ninv δ p N (P ∗ Q) ⊢ na_ninv δ p N P ∗ na_ninv δ p N Q.
  Proof.
    iIntros "#NPQ". iSplit; iApply (na_ninv_convert with "[] NPQ"); iModIntro;
    iApply (derivy_intro (δ:=δ)); by iIntros (???) "/=[$$]!>$".
  Qed.
  Lemma na_ninv_fupd {p N P} :
    na_ninv δ p N (|={∅}=> P) ⊣⊢ na_ninv δ p N P.
  Proof.
    iSplit; iApply na_ninv_convert; iModIntro;
      iApply (derivy_intro (δ:=δ))=>/=; iIntros (???);
      by [iIntros ">$!>$"|iIntros "$!>"; iSplitR; iIntros].
  Qed.
  Lemma na_ninv_add {p N P Q} :
    □ ⸨ P ⸩(δ) -∗ na_ninv δ p N Q -∗ na_ninv δ p N (P ∗ Q).
  Proof.
    iIntros "#P". iApply na_ninv_convert. iModIntro.
    iApply (derivy_map with "[] P"). by iIntros (???) "/=$$!>[_$]".
  Qed.

  (** Combine [na_ninv]s *)
  Lemma ninv_combine {p N N' N'' P Q} : N ## N' → ↑N ∪ ↑N' ⊆@{coPset} ↑N'' →
    na_ninv δ p N P -∗ na_ninv δ p N' Q -∗ na_ninv δ p N'' (P ∗ Q).
  Proof.
    rewrite na_ninv_unseal. iIntros (??) "#NP #N'Q !>".
    iApply (derivy_map2 (δ:=δ) with "[] NP N'Q")=>/=.
    iIntros (???) "{NP}NP {N'Q}N'Q". iIntros (? F ??) "F".
    iMod ("NP" with "[%] [%] F") as "($& F∖N & P→)"; [set_solver..|].
    iMod ("N'Q" with "[%] [%] F∖N") as "($& F∖NN' & Q→)"; [set_solver..|].
    iDestruct (na_own_acc with "F∖NN'") as "[$ F∖N''→]"; [set_solver|].
    iApply fupdw_mask_intro; [set_solver|]. iIntros "cl [P Q] F∖N''".
    iMod "cl" as "_". iDestruct ("F∖N''→" with "F∖N''") as "F∖NN'".
    iMod ("Q→" with "Q F∖NN'") as "F∖N". iApply ("P→" with "P F∖N").
  Qed.
End lemmas.
