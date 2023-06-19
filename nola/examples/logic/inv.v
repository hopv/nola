(** * On the invariant *)

From nola.examples.logic Require Export sintp.

Implicit Type (i : nat) (P Q : nPropL (;ᵞ)).

Section lemmas.
  Context `{!nintpGS Σ}.

  (** Access [nninv] *)
  Lemma nninv_acc {s i N P E} : ↑N ⊆ E →
    nssound s i -∗ nninv s i N P =[nninv_wsat s]{E,E∖↑N}=∗
      ⟦ P ⟧(s) ∗ (⟦ P ⟧(s) =[nninv_wsat s]{E∖↑N,E}=∗ True).
  Proof.
    rewrite nninv_unseal. iIntros (NE) "to #accP".
    iDestruct ("to" with "accP") as "/={accP}accP". by iApply "accP".
  Qed.
  Lemma nninvs_acc {i N P E} : ↑N ⊆ E →
    nninvs i N P =[nninv_wsats]{E,E∖↑N}=∗
      ⟦ P ⟧ ∗ (⟦ P ⟧ =[nninv_wsats]{E∖↑N,E}=∗ True).
  Proof. move=> ?. iApply nninv_acc; [done|iApply nsintp_sound]. Qed.

  Context `{!nsintpy Σ ih s}.

  (** Turn [ninv] into [nninv] *)
  Lemma ninv_nninv (P : nPropS _) {i N} :
    ninv N (nid_u P) -∗ nninv (Σ:=Σ) s i N (↑ˡ P).
  Proof.
    rewrite nninv_unseal. iIntros "#NP !>". iApply (sintpy_intro (s:=s))=>/=.
    iIntros (?????). rewrite -nintpS_nintp_nlarge.
    by iApply (ninv_acc with "NP").
  Qed.

  (** Allocate [nninv] *)
  Lemma nninv_alloc_rec (P : nPropS _) {i N} :
    (nninv s i N (↑ˡ P) -∗ ⟦ P ⟧(s)) =[nninv_wsat s]=∗
      nninv s i N (↑ˡ P).
  Proof.
    iIntros "toP".
    iMod (ninv_alloc_rec (P:=nid_u P) with "[toP]") as "NP".
    - iIntros "/=NP". rewrite nintpS_nintp. iApply "toP". by iApply ninv_nninv.
    - iModIntro. by iApply ninv_nninv.
  Qed.
  Lemma nninv_alloc (P : nPropS _) {i N} :
    ⟦ P ⟧(s) =[nninv_wsat s]=∗ nninv s i N (↑ˡ P).
  Proof. iIntros "P". iApply (nninv_alloc_rec with "[P]"). by iIntros. Qed.

  (** [nninv] is monotone over the level *)
  Lemma nninv_mono_lev {i j N P} :
    i ≤ j → nninv s i N P -∗ nninv s j N P.
  Proof.
    rewrite nninv_unseal. iIntros (ij) "#iP !>". by iApply sintpy_mono_lev.
  Qed.

  (** Transform [nninv] *)
  Lemma nninv_convert {i N P Q} :
    □ ⸨ P ={∅}=∗ Q ∗ (Q ={∅}=∗ P) ⸩(s, i) -∗ nninv s i N P -∗ nninv s i N Q.
  Proof.
    rewrite nninv_unseal. iIntros "#PQP #accP !>".
    iApply (sintpy_map2 with "[] PQP accP")=>/=.
    iIntros (???) "/= {PQP}PQP {accP}accP". iIntros (? NE).
    iMod ("accP" $! _ NE) as "[P Pto]".
    iMod (fupd_mask_subseteq ∅) as "toE∖N"; [set_solver|].
    iMod ("PQP" with "P") as "($& QP)". iMod "toE∖N" as "_". iIntros "!> Q".
    iMod (fupd_mask_subseteq ∅) as "toE∖N"; [set_solver|].
    iMod ("QP" with "Q") as "P". iMod "toE∖N" as "_". iApply ("Pto" with "P").
  Qed.
  Lemma nninv_split {i N P Q} :
    nninv s i N (P ∗ Q) ⊢ nninv s i N P ∗ nninv s i N Q.
  Proof.
    iIntros "#NPQ". iSplit; iApply (nninv_convert with "[] NPQ"); iModIntro;
    iApply (sintpy_intro (s:=s)); by iIntros (???) "/=[$$]!>$".
  Qed.
  Lemma nninv_fupd {i N P} :
    nninv s i N (|={∅}=> P) ⊣⊢ nninv s i N P.
  Proof.
    iSplit; iApply nninv_convert; iModIntro; iApply (sintpy_intro (s:=s))=>/=;
      iIntros (???); by [iIntros ">$!>$"|iIntros "$!>"; iSplitR; iIntros].
  Qed.
  Lemma nninv_add {i N P Q} :
    □ ⸨ P ⸩(s, i) -∗ nninv s i N Q -∗ nninv s i N (P ∗ Q).
  Proof.
    iIntros "#P". iApply nninv_convert. iModIntro.
    iApply (sintpy_map with "[] P"). by iIntros (???) "/=$$!>[_$]".
  Qed.

  (** Combine [nninv]s *)
  Lemma nninv_combine {i N N' N'' P Q} : N ## N' → ↑N ∪ ↑N' ⊆@{coPset} ↑N'' →
    nninv s i N P -∗ nninv s i N' Q -∗ nninv s i N'' (P ∗ Q).
  Proof.
    rewrite nninv_unseal. iIntros (??) "#NP #N'Q !>".
    iApply (sintpy_map2 (s:=s) with "[] NP N'Q")=>/=.
    iIntros (???) "{NP}NP {N'Q}N'Q". iIntros (??).
    iMod ("NP" with "[%]") as "[$ Pto]"; [set_solver|].
    iMod ("N'Q" with "[%]") as "[$ Qto]"; [set_solver|].
    iApply fupdw_mask_intro; [set_solver|]. iIntros "cl [P Q]".
    iMod "cl" as "_". iMod ("Qto" with "Q") as "_". iApply ("Pto" with "P").
  Qed.
End lemmas.
