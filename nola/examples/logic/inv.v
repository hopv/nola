(** * On the invariant *)

From nola.examples.logic Require Export deriv.

Implicit Type (i : nat) (P Q : nPropL (;ᵞ)).

Section lemmas.
  Context `{!nintpGS Σ}.

  (** Access [nninv] *)
  Lemma nninv_acc {d i N P E} : ↑N ⊆ E →
    ndsound d i -∗ nninv d i N P =[nninv_wsat d]{E,E∖↑N}=∗
      ⟦ P ⟧(d) ∗ (⟦ P ⟧(d) =[nninv_wsat d]{E∖↑N,E}=∗ True).
  Proof.
    rewrite nninv_unseal. iIntros (NE) "to #accP".
    iDestruct ("to" with "accP") as "/={accP}accP". by iApply "accP".
  Qed.
  Lemma nninvd_acc {i N P E} : ↑N ⊆ E →
    nninvd i N P =[nninv_wsatd]{E,E∖↑N}=∗
      ⟦ P ⟧ ∗ (⟦ P ⟧ =[nninv_wsatd]{E∖↑N,E}=∗ True).
  Proof. move=> ?. iApply nninv_acc; [done|iApply nderiv_sound]. Qed.

  Context `{!nderivy Σ ih d}.

  (** Turn [ninv] into [nninv] *)
  Lemma ninv_nninv (P : nPropS _) {i N} :
    ninv N (nInvd_u P) -∗ nninv (Σ:=Σ) d i N (↑ˡ P).
  Proof.
    rewrite nninv_unseal. iIntros "#NP !>". iApply (derivy_intro (d:=d))=>/=.
    iIntros (?????). rewrite -nintpS_nintp_nlarge.
    by iApply (ninv_acc with "NP").
  Qed.

  (** Allocate [nninv] *)
  Lemma nninv_alloc_rec (P : nPropS _) {i N} :
    (nninv d i N (↑ˡ P) -∗ ⟦ P ⟧(d)) =[nninv_wsat d]=∗
      nninv d i N (↑ˡ P).
  Proof.
    iIntros "toP".
    iMod (ninv_alloc_rec (P:=nInvd_u P) with "[toP]") as "NP".
    - iIntros "/=NP". rewrite nintpS_nintp. iApply "toP". by iApply ninv_nninv.
    - iModIntro. by iApply ninv_nninv.
  Qed.
  Lemma nninv_alloc (P : nPropS _) {i N} :
    ⟦ P ⟧(d) =[nninv_wsat d]=∗ nninv d i N (↑ˡ P).
  Proof. iIntros "P". iApply (nninv_alloc_rec with "[P]"). by iIntros. Qed.

  (** [nninv] is monotone over the level *)
  Lemma nninv_mono_lev {i j N P} :
    i ≤ j → nninv d i N P -∗ nninv d j N P.
  Proof.
    rewrite nninv_unseal. iIntros (ij) "#iP !>". by iApply derivy_mono_lev.
  Qed.

  (** Transform [nninv] *)
  Lemma nninv_convert {i N P Q} :
    □ ⸨ P ={∅}=∗ Q ∗ (Q ={∅}=∗ P) ⸩(d, i) -∗ nninv d i N P -∗ nninv d i N Q.
  Proof.
    rewrite nninv_unseal. iIntros "#PQP #accP !>".
    iApply (derivy_map2 with "[] PQP accP")=>/=.
    iIntros (???) "/= {PQP}PQP {accP}accP". iIntros (? NE).
    iMod ("accP" $! _ NE) as "[P Pto]".
    iMod (fupd_mask_subseteq ∅) as "toE∖N"; [set_solver|].
    iMod ("PQP" with "P") as "($& QP)". iMod "toE∖N" as "_". iIntros "!> Q".
    iMod (fupd_mask_subseteq ∅) as "toE∖N"; [set_solver|].
    iMod ("QP" with "Q") as "P". iMod "toE∖N" as "_". iApply ("Pto" with "P").
  Qed.
  Lemma nninv_split {i N P Q} :
    nninv d i N (P ∗ Q) ⊢ nninv d i N P ∗ nninv d i N Q.
  Proof.
    iIntros "#NPQ". iSplit; iApply (nninv_convert with "[] NPQ"); iModIntro;
    iApply (derivy_intro (d:=d)); by iIntros (???) "/=[$$]!>$".
  Qed.
  Lemma nninv_fupd {i N P} :
    nninv d i N (|={∅}=> P) ⊣⊢ nninv d i N P.
  Proof.
    iSplit; iApply nninv_convert; iModIntro; iApply (derivy_intro (d:=d))=>/=;
      iIntros (???); by [iIntros ">$!>$"|iIntros "$!>"; iSplitR; iIntros].
  Qed.
  Lemma nninv_add {i N P Q} :
    □ ⸨ P ⸩(d, i) -∗ nninv d i N Q -∗ nninv d i N (P ∗ Q).
  Proof.
    iIntros "#P". iApply nninv_convert. iModIntro.
    iApply (derivy_map with "[] P"). by iIntros (???) "/=$$!>[_$]".
  Qed.

  (** Combine [nninv]s *)
  Lemma nninv_combine {i N N' N'' P Q} : N ## N' → ↑N ∪ ↑N' ⊆@{coPset} ↑N'' →
    nninv d i N P -∗ nninv d i N' Q -∗ nninv d i N'' (P ∗ Q).
  Proof.
    rewrite nninv_unseal. iIntros (??) "#NP #N'Q !>".
    iApply (derivy_map2 (d:=d) with "[] NP N'Q")=>/=.
    iIntros (???) "{NP}NP {N'Q}N'Q". iIntros (??).
    iMod ("NP" with "[%]") as "[$ Pto]"; [set_solver|].
    iMod ("N'Q" with "[%]") as "[$ Qto]"; [set_solver|].
    iApply fupdw_mask_intro; [set_solver|]. iIntros "cl [P Q]".
    iMod "cl" as "_". iMod ("Qto" with "Q") as "_". iApply ("Pto" with "P").
  Qed.
End lemmas.
