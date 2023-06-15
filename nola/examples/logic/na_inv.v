(** * On the invariant *)

From nola.examples.logic Require Export sintp.

Implicit Type (i : nat) (P Q : nPropL (;ᵞ)).

Section lemmas.
  Context `{!nintpGS Σ}.

  (** Access [na_nninv] *)
  Lemma na_nninv_acc {s i p N P E F} : ↑N ⊆ E → ↑N ⊆ F →
    nssound s i -∗ na_nninv s i p N P -∗ na_own p F =[nninv_wsat s]{E}=∗
      ⟦ P ⟧(s) ∗ na_own p (F∖↑N) ∗
      (⟦ P ⟧(s) -∗ na_own p (F∖↑N) =[nninv_wsat s]{E}=∗ na_own p F).
  Proof.
    rewrite na_nninv_unseal. iIntros (NE NF) "to #accP F".
    iDestruct ("to" with "accP") as "/={accP}accP".
    iApply ("accP" $! _ _ NE NF with "F").
  Qed.
  Lemma na_nninvs_acc {i p N P E F} : ↑N ⊆ E → ↑N ⊆ F →
    na_nninvs i p N P -∗ na_own p F =[nninv_wsats]{E}=∗
      ⟦ P ⟧ ∗ na_own p (F∖↑N) ∗
      (⟦ P ⟧ -∗ na_own p (F∖↑N) =[nninv_wsats]{E}=∗ na_own p F).
  Proof. move=> ??. iApply na_nninv_acc; [done..|iApply nsintp_sound]. Qed.

  Context `{!nsintpy Σ σ}.

  (** Turn [na_ninv] into [na_nninv] *)
  Lemma na_ninv_nninv {s i j p N} {P : nPropS _} : j ∈ (↑N:coPset) →
    ninv N (nid_na p j P) -∗ na_nninv (Σ:=Σ) (σ s) i p N (↑ˡ P).
  Proof.
    rewrite na_nninv_unseal. iIntros (jN) "#NP !>".
    iApply (sintpy_intro (σ:=σ))=>/=.
    iIntros (?? E F NE NF) "F". rewrite -nintpS_nintp_nlarge.
    iMod (ninv_acc NE with "NP") as "/=[bd bdto]".
    iDestruct (na_body_acc with "bd F") as "(bd &$&$& Pto)"; [done..|].
    iMod ("bdto" with "bd") as "_". iIntros "!> P F∖N".
    iMod (ninv_acc NE with "NP") as "/=[bd bdto]".
    iDestruct ("Pto" with "bd P F∖N") as "[bd $]".
    by iMod ("bdto" with "bd") as "_".
  Qed.

  (** Allocate [na_nninv] *)
  Lemma na_nninv_alloc_rec {s i p N} {P : nPropS (;ᵞ)} :
    (na_nninv (σ s) i p N (↑ˡ P) -∗ ⟦ P ⟧(σ s)) =[nninv_wsat (σ s)]=∗
      na_nninv (σ s) i p N (↑ˡ P).
  Proof.
    iIntros "toP". iMod na_lock_alloc as (j) "[% lock]".
    iMod (ninv_alloc_rec (P:=nid_na p j P) with "[toP lock]") as "NP".
    - iIntros "/=NP". iLeft. iFrame "lock". rewrite nintpS_nintp.
      iApply "toP". by iApply na_ninv_nninv.
    - iModIntro. by iApply na_ninv_nninv.
  Qed.
  Lemma nninv_alloc {s i p N} {P : nPropS (;ᵞ)} :
    ⟦ P ⟧(σ s) =[nninv_wsat (σ s)]=∗ na_nninv (σ s) i p N (↑ˡ P).
  Proof.
    iIntros "P". iApply (na_nninv_alloc_rec with "[P]"). by iIntros.
  Qed.

  (** [na_nninv] is monotone over the level *)
  Lemma na_nninv_mono_lev {s i j p N P} :
    i ≤ j → na_nninv (σ s) i p N P -∗ na_nninv (σ s) j p N P.
  Proof.
    rewrite na_nninv_unseal. iIntros (ij) "#iP !>". by iApply sintpy_mono_lev.
  Qed.

  (** Transform [na_nninv] *)
  Lemma na_nninv_convert {s i p N P Q} :
    □ ⸨ P ={∅}=∗ Q ∗ (Q ={∅}=∗ P) ⸩(σ s, i) -∗
      na_nninv (σ s) i p N P -∗ na_nninv (σ s) i p N Q.
  Proof.
    rewrite na_nninv_unseal. iIntros "#PQP #accP !>".
    iApply (sintpy_map2 with "[] PQP accP")=>/=.
    iIntros (??) "/= {PQP}PQP {accP}accP". iIntros (E F NE NF) "F".
    iMod ("accP" $! E F NE NF with "F") as "(P &$& Pto)".
    iMod (fupd_mask_subseteq ∅) as "toE∖N"; [set_solver|].
    iMod ("PQP" with "P") as "($& QP)". iMod "toE∖N" as "_". iIntros "!> Q".
    iMod (fupd_mask_subseteq ∅) as "toE∖N"; [set_solver|].
    iMod ("QP" with "Q") as "P". iMod "toE∖N" as "_". iApply ("Pto" with "P").
  Qed.
  Lemma na_nninv_split {s i p N P Q} :
    na_nninv (σ s) i p N (P ∗ Q) ⊢
      na_nninv (σ s) i p N P ∗ na_nninv (σ s) i p N Q.
  Proof.
    iIntros "#NPQ". iSplit; iApply (na_nninv_convert with "[] NPQ"); iModIntro;
    iApply (sintpy_intro (σ:=σ)); by iIntros (??) "/=[$$]!>$".
  Qed.
  Lemma na_nninv_fupd {s i p N P} :
    na_nninv (σ s) i p N (|={∅}=> P) ⊣⊢ na_nninv (σ s) i p N P.
  Proof.
    iSplit; iApply na_nninv_convert; iModIntro;
      iApply (sintpy_intro (σ:=σ))=>/=; iIntros (??);
      by [iIntros ">$!>$"|iIntros "$!>"; iSplitR; iIntros].
  Qed.
  Lemma na_nninv_add {s i p N P Q} :
    □ ⸨ P ⸩(σ s, i) -∗ na_nninv (σ s) i p N Q -∗ na_nninv (σ s) i p N (P ∗ Q).
  Proof.
    iIntros "#P". iApply na_nninv_convert. iModIntro.
    iApply (sintpy_map with "[] P"). by iIntros (??) "/=$$!>[_$]".
  Qed.

  (** Combine [na_nninv]s *)
  Lemma nninv_combine {s i p N N' N'' P Q} :
    N ## N' → ↑N ∪ ↑N' ⊆@{coPset} ↑N'' →
    na_nninv (σ s) i p N P -∗ na_nninv (σ s) i p N' Q -∗
    na_nninv (σ s) i p N'' (P ∗ Q).
  Proof.
    rewrite na_nninv_unseal. iIntros (??) "#NP #N'Q !>".
    iApply (sintpy_map2 (σ:=σ) with "[] NP N'Q")=>/=.
    iIntros (??) "{NP}NP {N'Q}N'Q". iIntros (? F ??) "F".
    iMod ("NP" with "[%] [%] F") as "($& F∖N & Pto)"; [set_solver..|].
    iMod ("N'Q" with "[%] [%] F∖N") as "($& F∖NN' & Qto)"; [set_solver..|].
    iDestruct (na_own_acc with "F∖NN'") as "[$ F∖N''to]"; [set_solver|].
    iApply fupdw_mask_intro; [set_solver|]. iIntros "cl [P Q] F∖N''".
    iMod "cl" as "_". iDestruct ("F∖N''to" with "F∖N''") as "F∖NN'".
    iMod ("Qto" with "Q F∖NN'") as "F∖N". iApply ("Pto" with "P F∖N").
  Qed.
End lemmas.
