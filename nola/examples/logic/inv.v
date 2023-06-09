(** * On the invariant *)

From nola.examples.logic Require Export sintp.
From iris.proofmode Require Import proofmode.
From nola Require Import fupd.

Implicit Type (i : nat) (P Q : nPropL (;ᵞ)).

Section lemmas.
  Context `{!nintpGS Σ}.

  (** Access [nninv] *)
  Lemma nninv_acc {s i N P E} : ↑N ⊆ E →
    ssound (ITI:=nintpsi _) s i -∗ nninv s i N P =[nninv_wsat s]{E,E∖↑N}=∗
      ⟦ P ⟧(s) ∗ (⟦ P ⟧(s) =[nninv_wsat s]{E∖↑N,E}=∗ True).
  Proof.
    rewrite nninv_unseal. iIntros (NE) "to #accP W".
    iDestruct ("to" with "accP") as "/={accP}accP".
    iApply ("accP" $! _ NE with "W").
  Qed.

  Context `{!nsintpy Σ σ}.

  (** Access [n_inv] *)
  Lemma n_inv_acc {s i j N P E} : ↑N ⊆ E → i < j → ⊢
    ⸨ n_inv' [] i N P =[n_inv_wsat]{E,E∖↑N}=∗
        P ∗ (P =[n_inv_wsat]{E∖↑N,E}=∗ True) ⸩(σ s, j).
  Proof.
    move=> NE ij. iApply sintpy_byintp. iIntros (??) "/= _ _ #to".
    iApply (nninv_acc NE). by iApply "to".
  Qed.

  (** Turn [ninv] into [nninv] *)
  Lemma ninv_nninv {s i N} {P : nPropS _} :
    ninv N (nid_u P) -∗ nninv (Σ:=Σ) (σ s) i N (↑ˡ P).
  Proof.
    rewrite nninv_unseal. iIntros "#NP !#". iApply (sintpy_intro (σ:=σ))=>/=.
    iIntros (?? E NE) "W". rewrite -nintpS_nintp_nlarge.
    iApply (ninv_acc NE with "NP W").
  Qed.

  (** Allocate [nninv] *)
  Lemma nninv_alloc_rec {s i N} {P : nPropS (;ᵞ)} :
    (nninv (σ s) i N (↑ˡ P) -∗ ⟦ P ⟧(σ s)) =[nninv_wsat (σ s)]=∗
      nninv (σ s) i N (↑ˡ P).
  Proof.
    iIntros "toP W".
    iMod (ninv_alloc_rec (P:=nid_u P) with "[toP] W") as "[$ NP]".
    - iIntros "/=NP". rewrite nintpS_nintp. iApply "toP". by iApply ninv_nninv.
    - iModIntro. by iApply ninv_nninv.
  Qed.
  Lemma nninv_alloc {s i N} {P : nPropS (;ᵞ)} :
    ⟦ P ⟧(σ s) =[nninv_wsat (σ s)]=∗ nninv (σ s) i N (↑ˡ P).
  Proof. iIntros "P W". iApply (nninv_alloc_rec with "[P] W"). by iIntros. Qed.

  (** [nninv] is monotone over the level *)
  Lemma nninv_mono_lev {s i j N P} :
    i ≤ j → nninv (σ s) i N P -∗ nninv (σ s) j N P.
  Proof.
    rewrite nninv_unseal. iIntros (ij) "#iP !#". by iApply sintpy_mono_lev.
  Qed.

  (** Transform [nninv] *)
  Lemma nninv_convert {s i N P Q} :
    □ ⸨ P ={∅}=∗ Q ∗ (Q ={∅}=∗ P) ⸩(σ s, i) -∗ nninv (σ s) i N P -∗
    nninv (σ s) i N Q.
  Proof.
    rewrite nninv_unseal. iIntros "#PQP #accP !>".
    iApply (sintpy_map2 with "[] PQP accP")=>/=.
    iIntros (??) "/= {PQP}PQP {accP}accP". iIntros (E NE) "W".
    iMod ("accP" $! E NE with "W") as "($& P & Pto)".
    iMod (fupd_mask_subseteq ∅) as "toE∖N"; [set_solver|].
    iMod ("PQP" with "P") as "($& QP)". iMod "toE∖N" as "_". iIntros "!> Q W".
    iMod (fupd_mask_subseteq ∅) as "toE∖N"; [set_solver|].
    iMod ("QP" with "Q") as "P". iMod "toE∖N" as "_". iApply ("Pto" with "P W").
  Qed.
  Lemma nninv_split {s i N P Q} :
    nninv (σ s) i N (P ∗ Q) -∗ nninv (σ s) i N P ∗ nninv (σ s) i N Q.
  Proof.
    iIntros "#NPQ". iSplit; iApply (nninv_convert with "[] NPQ"); iModIntro;
    iApply (sintpy_intro (σ:=σ)); by iIntros (??) "/=[$$]!>$".
  Qed.
  Lemma nninv_fupd {s i N P} :
    nninv (σ s) i N (|={∅}=> P) ⊣⊢ nninv (σ s) i N P.
  Proof.
    iSplit; iApply nninv_convert; iModIntro; iApply (sintpy_intro (σ:=σ))=>/=;
      iIntros (??); by [iIntros ">$!>$"|iIntros "$!>"; iSplitR; iIntros].
  Qed.
  Lemma nninv_add {s i N P Q} :
    □ ⸨ P ⸩(σ s, i) -∗ nninv (σ s) i N Q -∗ nninv (σ s) i N (P ∗ Q).
  Proof.
    iIntros "#P". iApply nninv_convert. iModIntro.
    iApply (sintpy_map with "[] P"). by iIntros (??) "/=$$!>[_$]".
  Qed.

  (** Combine [nninv]s *)
  Lemma nninv_combine {s i N N' N'' P Q} :
    N ## N' → ↑N ∪ ↑N' ⊆@{coPset} ↑N'' →
    nninv (σ s) i N P -∗ nninv (σ s) i N' Q -∗ nninv (σ s) i N'' (P ∗ Q).
  Proof.
    rewrite nninv_unseal. iIntros (??) "#NP #N'Q !>".
    iApply (sintpy_map2 (σ:=σ) with "[] NP N'Q")=>/=.
    iIntros (??) "{NP}NP {N'Q}N'Q". iIntros (E NE) "W".
    iMod ("NP" with "[%] W") as "(W &$& Pto)"; [set_solver|].
    iMod ("N'Q" with "[%] W") as "($&$& Qto)"; [set_solver|].
    iApply fupd_mask_intro; [set_solver|]. iIntros "Cl [P Q] W". iMod "Cl".
    iMod ("Qto" with "Q W") as "[W _]". iApply ("Pto" with "P W").
  Qed.
End lemmas.
