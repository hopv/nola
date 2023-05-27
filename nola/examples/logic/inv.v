(** * On the invariant *)

From nola.examples.logic Require Export sintp.
From iris.proofmode Require Import proofmode.
From nola Require Import fupd.

Implicit Type (i : nat) (P Q : nPropL (;ᵞ)).

Section lemmas.
  Context `{!nintpGS Σ, !nsintpy Σ σ}.

  (** Access [n_inv] *)
  Lemma n_inv_acc {s i j N P E} : ↑N ⊆ E → i < j → ⊢
    ⸨ n_inv' [] i N P =[n_inv_wsat]{E,E∖↑N}=∗
        P ∗ (P =[n_inv_wsat]{E∖↑N,E}=∗ True) ⸩(σ s, j).
  Proof.
    move=> NE ij. iApply sintpy_byintp. iIntros (??) "/= _ _ #to".
    rewrite nninv_unseal. iIntros "(%Q & #QPQ & NQ) W".
    iMod (ninv_acc with "NQ W") as "(W & Q & toW)"; [done|].
    iDestruct ("to" $! _ ij with "QPQ") as "/={QPQ}QPQ".
    rewrite nintpS_nintp_nlarge.
    iMod (fupd_mask_subseteq ∅) as "∅to"; [set_solver|].
    iMod ("QPQ" with "Q W") as "($&$& PQ)". iMod "∅to" as "_". iIntros "!> P W".
    iMod (fupd_mask_subseteq ∅) as "∅to"; [set_solver|].
    iMod ("PQ" with "P W") as "[W Q]". iMod "∅to" as "_".
    iApply ("toW" with "Q W").
  Qed.

  (** Turn [ninv] into [nninv] *)
  Lemma ninv_nninv {s i N} {P : nPropS _} :
    ninv N P -∗ nninv (Σ:=Σ) (σ s) i N (↑ˡ P).
  Proof.
    rewrite nninv_unseal. iIntros "NP". iExists P. iFrame "NP". iModIntro.
    iApply (sintpy_intro (σ:=σ)). by iIntros (??) "/= $$!>$$".
  Qed.

  (** Allocate [nninv] *)
  Lemma nninv_alloc_rec {s i N} {P : nPropS (;ᵞ)} :
    (nninv (σ s) i N (↑ˡ P) -∗ ⟦ P ⟧(σ s)) =[nninv_wsat (σ s)]=∗
      nninv (σ s) i N (↑ˡ P).
  Proof.
    iIntros "toP W". iMod (ninv_alloc_rec with "[toP] W") as "[$ NP]".
    - iIntros "NP". rewrite nintpS_nintp. iApply "toP". by iApply ninv_nninv.
    - iModIntro. by iApply ninv_nninv.
  Qed.
  Lemma nninv_alloc {s i N} {P : nPropS (;ᵞ)} :
    ⟦ P ⟧(σ s) =[nninv_wsat (σ s)]=∗ nninv (σ s) i N (↑ˡ P).
  Proof. iIntros "P W". iApply (nninv_alloc_rec with "[P] W"). by iIntros. Qed.

  (** Transform [nninv] *)
  Lemma nninv_convert {s i N P Q} :
    □ ⸨ P =[n_inv_wsat]{∅}=∗ Q ∗ (Q =[n_inv_wsat]{∅}=∗ P) ⸩(σ s, i) -∗
    nninv (σ s) i N P -∗ nninv (σ s) i N Q.
  Proof.
    rewrite nninv_unseal. iIntros "#PQP (%R & #RPR & #NR)". iExists R.
    iFrame "NR". iModIntro. iApply (sintpy_map2 with "[] PQP RPR").
    iIntros (??) "/= {PQP}PQP {RPR}RPR R W".
    iMod ("RPR" with "R W") as "(W & P & PR)".
    iMod ("PQP" with "P W") as "($&$& QP)". iIntros "!> Q W".
    iMod ("QP" with "Q W") as "[W P]". iApply ("PR" with "P W").
  Qed.
  Lemma nninv_split_l {s i N P Q} :
    nninv (σ s) i N (P ∗ Q) -∗ nninv (σ s) i N P.
  Proof.
    iApply nninv_convert. iModIntro. iApply (sintpy_intro (σ:=σ)).
    by iIntros (??) "/=[$$]$!>$$".
  Qed.
  Lemma nninv_split_r {s i N P Q} :
    nninv (σ s) i N (P ∗ Q) -∗ nninv (σ s) i N Q.
  Proof.
    iApply nninv_convert. iModIntro. iApply (sintpy_intro (σ:=σ)).
    by iIntros (??) "/=[$$]$!>$$".
  Qed.
  Lemma nninv_split {s i N P Q} :
    nninv (σ s) i N (P ∗ Q) -∗ nninv (σ s) i N P ∗ nninv (σ s) i N Q.
  Proof.
    iIntros "#?". iSplit; by [iApply nninv_split_l|iApply nninv_split_r].
  Qed.
  Lemma nninv_fupd {s i N P} :
    nninv (σ s) i N (|={∅}=> P) ⊣⊢ nninv (σ s) i N P.
  Proof.
    iSplit; iApply nninv_convert; iModIntro; iApply (sintpy_intro (σ:=σ))=>/=;
      by [iIntros (??) ">$$!>$$"|iIntros (??) "$$!>"; iSplitR; iIntros; iFrame].
  Qed.
  Lemma nninv_add {s i N P Q} :
    □ ⸨ P ⸩(σ s, i) -∗ nninv (σ s) i N Q -∗ nninv (σ s) i N (P ∗ Q).
  Proof.
    iIntros "#P". iApply nninv_convert. iModIntro.
    iApply (sintpy_map with "[] P"). by iIntros (??) "/=$$$!>[_$]$".
  Qed.
End lemmas.
