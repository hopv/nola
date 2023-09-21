(** * On the invariant *)

From nola.examples.logic Require Export deriv.

Implicit Type (i : nat) (P Q : nPropL (;ᵞ)).

Section lemmas.
  Context `{!nintpGS Σ}.

  (** Access [na_nninv] *)
  Lemma na_nninv_acc {d i p N P E F} : ↑N ⊆ E → ↑N ⊆ F →
    ndsound d i -∗ na_nninv d i p N P -∗ na_own p F =[nninv_wsat d]{E}=∗
      ⟦ P ⟧(d) ∗ na_own p (F∖↑N) ∗
      (⟦ P ⟧(d) -∗ na_own p (F∖↑N) =[nninv_wsat d]{E}=∗ na_own p F).
  Proof.
    rewrite na_nninv_unseal. iIntros (NE NF) "to #accP F".
    iDestruct ("to" with "accP") as "/={accP}accP".
    iApply ("accP" $! _ _ NE NF with "F").
  Qed.
  Lemma na_nninvd_acc {i p N P E F} : ↑N ⊆ E → ↑N ⊆ F →
    na_nninvd i p N P -∗ na_own p F =[nninv_wsatd]{E}=∗
      ⟦ P ⟧ ∗ na_own p (F∖↑N) ∗
      (⟦ P ⟧ -∗ na_own p (F∖↑N) =[nninv_wsatd]{E}=∗ na_own p F).
  Proof. move=> ??. iApply na_nninv_acc; [done..|iApply nderiv_sound]. Qed.

  Context `{!nderivy Σ ih d}.

  (** Turn [na_ninv] into [na_nninv] *)
  Lemma na_ninv_nninv (P : nPropS _) {i j p N} : j ∈ (↑N:coPset) →
    ninv N (nInvd_na p j P) -∗ na_nninv (Σ:=Σ) d i p N (↑ˡ P).
  Proof.
    rewrite na_nninv_unseal. iIntros (jN) "#NP !>".
    iApply (derivy_intro (d:=d))=>/=.
    iIntros (??? E F NE NF) "F". rewrite -nintpS_nintp_nlarge.
    iMod (ninv_acc NE with "NP") as "/=[bd bdto]".
    iDestruct (na_body_acc with "bd F") as "(bd &$&$& Pto)"; [done..|].
    iMod ("bdto" with "bd") as "_". iIntros "!> P F∖N".
    iMod (ninv_acc NE with "NP") as "/=[bd bdto]".
    iDestruct ("Pto" with "bd P F∖N") as "[bd $]".
    by iMod ("bdto" with "bd") as "_".
  Qed.

  (** Allocate [na_nninv] *)
  Lemma na_nninv_alloc_rec (P : nPropS _) {i p N} :
    (na_nninv d i p N (↑ˡ P) -∗ ⟦ P ⟧(d)) =[nninv_wsat d]=∗
      na_nninv d i p N (↑ˡ P).
  Proof.
    iIntros "toP". iMod na_lock_alloc as (j) "[% lock]".
    iMod (ninv_alloc_rec (P:=nInvd_na p j P) with "[toP lock]") as "NP".
    - iIntros "/=NP". iLeft. iFrame "lock". rewrite nintpS_nintp.
      iApply "toP". by iApply na_ninv_nninv.
    - iModIntro. by iApply na_ninv_nninv.
  Qed.
  Lemma na_nninv_alloc (P : nPropS _) {i p N} :
    ⟦ P ⟧(d) =[nninv_wsat d]=∗ na_nninv d i p N (↑ˡ P).
  Proof.
    iIntros "P". iApply (na_nninv_alloc_rec with "[P]"). by iIntros.
  Qed.

  (** [na_nninv] is monotone over the level *)
  Lemma na_nninv_mono_lev {i j p N P} :
    i ≤ j → na_nninv d i p N P -∗ na_nninv d j p N P.
  Proof.
    rewrite na_nninv_unseal. iIntros (ij) "#iP !>". by iApply derivy_mono_lev.
  Qed.

  (** Transform [na_nninv] *)
  Lemma na_nninv_convert {i p N P Q} :
    □ ⸨ P ={∅}=∗ Q ∗ (Q ={∅}=∗ P) ⸩(d, i) -∗
      na_nninv d i p N P -∗ na_nninv d i p N Q.
  Proof.
    rewrite na_nninv_unseal. iIntros "#PQP #accP !>".
    iApply (derivy_map2 with "[] PQP accP")=>/=.
    iIntros (???) "/= {PQP}PQP {accP}accP". iIntros (E F NE NF) "F".
    iMod ("accP" $! E F NE NF with "F") as "(P &$& Pto)".
    iMod (fupd_mask_subseteq ∅) as "toE∖N"; [set_solver|].
    iMod ("PQP" with "P") as "($& QP)". iMod "toE∖N" as "_". iIntros "!> Q".
    iMod (fupd_mask_subseteq ∅) as "toE∖N"; [set_solver|].
    iMod ("QP" with "Q") as "P". iMod "toE∖N" as "_". iApply ("Pto" with "P").
  Qed.
  Lemma na_nninv_split {i p N P Q} :
    na_nninv d i p N (P ∗ Q) ⊢ na_nninv d i p N P ∗ na_nninv d i p N Q.
  Proof.
    iIntros "#NPQ". iSplit; iApply (na_nninv_convert with "[] NPQ"); iModIntro;
    iApply (derivy_intro (d:=d)); by iIntros (???) "/=[$$]!>$".
  Qed.
  Lemma na_nninv_fupd {i p N P} :
    na_nninv d i p N (|={∅}=> P) ⊣⊢ na_nninv d i p N P.
  Proof.
    iSplit; iApply na_nninv_convert; iModIntro;
      iApply (derivy_intro (d:=d))=>/=; iIntros (???);
      by [iIntros ">$!>$"|iIntros "$!>"; iSplitR; iIntros].
  Qed.
  Lemma na_nninv_add {i p N P Q} :
    □ ⸨ P ⸩(d, i) -∗ na_nninv d i p N Q -∗ na_nninv d i p N (P ∗ Q).
  Proof.
    iIntros "#P". iApply na_nninv_convert. iModIntro.
    iApply (derivy_map with "[] P"). by iIntros (???) "/=$$!>[_$]".
  Qed.

  (** Combine [na_nninv]s *)
  Lemma nninv_combine {i p N N' N'' P Q} : N ## N' → ↑N ∪ ↑N' ⊆@{coPset} ↑N'' →
    na_nninv d i p N P -∗ na_nninv d i p N' Q -∗ na_nninv d i p N'' (P ∗ Q).
  Proof.
    rewrite na_nninv_unseal. iIntros (??) "#NP #N'Q !>".
    iApply (derivy_map2 (d:=d) with "[] NP N'Q")=>/=.
    iIntros (???) "{NP}NP {N'Q}N'Q". iIntros (? F ??) "F".
    iMod ("NP" with "[%] [%] F") as "($& F∖N & Pto)"; [set_solver..|].
    iMod ("N'Q" with "[%] [%] F∖N") as "($& F∖NN' & Qto)"; [set_solver..|].
    iDestruct (na_own_acc with "F∖NN'") as "[$ F∖N''to]"; [set_solver|].
    iApply fupdw_mask_intro; [set_solver|]. iIntros "cl [P Q] F∖N''".
    iMod "cl" as "_". iDestruct ("F∖N''to" with "F∖N''") as "F∖NN'".
    iMod ("Qto" with "Q F∖NN'") as "F∖N". iApply ("Pto" with "P F∖N").
  Qed.
End lemmas.
