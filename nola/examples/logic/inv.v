(** * On the invariant *)

From nola.examples.logic Require Export sintp.
From iris.proofmode Require Import proofmode.

Implicit Type (i : nat) (P Q : nPropL (;ᵞ)).

Section lemmas.
  Context `{!nintpGS Σ, !nsintpy Σ σ}.

  (** Access [n_inv] *)
  Lemma n_inv_acc {s i j N P E} : ↑N ⊆ E → i < j → ⊢
    ⸨ n_inv_wsat ∗ n_inv' [] i N P ={E,E∖↑N}=∗
        n_inv_wsat ∗ P ∗ (n_inv_wsat -∗ P ={E∖↑N,E}=∗ n_inv_wsat) ⸩(σ s, j).
  Proof.
    move=> NE ij. iApply sintpy_byintp. iIntros (??) "/= _ _ #to".
    rewrite nninv_unseal. iIntros "[W (%Q & #QPQ & NQ)]".
    iMod (ninv_acc with "W NQ") as "($ & Q & toW)"; [done|].
    iDestruct ("to" $! _ ij with "QPQ") as "/={QPQ}QPQ".
    rewrite nintpS_nintp_nlarge.
    iMod (fupd_mask_subseteq ∅) as "∅to"; [set_solver|].
    iMod ("QPQ" with "Q") as "[$ PQ]". iMod "∅to" as "_". iIntros "!> W P".
    iMod (fupd_mask_subseteq ∅) as "∅to"; [set_solver|].
    iMod ("PQ" with "P") as "Q". iMod "∅to" as "_". iApply ("toW" with "W Q").
  Qed.

  (** Turn [ninv] into [nninv] *)
  Lemma ninv_nninv {s i N} {P : nPropS _} :
    ninv N P -∗ nninv (Σ:=Σ) (σ s) i N (nlarge P).
  Proof.
    rewrite nninv_unseal. iIntros "NP". iExists P. iFrame "NP". iModIntro.
    iApply (sintpy_intro (σ:=σ)). by iIntros (??) "/= $ !> $".
  Qed.

  (** Allocate [nninv] *)
  Lemma nninv_alloc_rec {s i N} {P : nPropS (;ᵞ)} :
    nninv_wsat (σ s) -∗ (nninv (σ s) i N (nlarge P) -∗ ⟦ P ⟧(σ s)) ==∗
      nninv_wsat (σ s) ∗ nninv (σ s) i N (nlarge P).
  Proof.
    iIntros "W toP". iMod (ninv_alloc_rec with "W [toP]") as "[$ NP]".
    - iIntros "NP". rewrite nintpS_nintp. iApply "toP". by iApply ninv_nninv.
    - iModIntro. by iApply ninv_nninv.
  Qed.
  Lemma nninv_alloc {s i N} {P : nPropS (;ᵞ)} :
    nninv_wsat (σ s) -∗ ⟦ P ⟧(σ s) ==∗
      nninv_wsat (σ s) ∗ nninv (σ s) i N (nlarge P).
  Proof. iIntros "W P". iApply (nninv_alloc_rec with "W"). by iIntros. Qed.

  (** Transform [nninv] *)
  Lemma nninv_convert {s i N P Q} :
    □ ⸨ P ={∅}=∗ Q ∗ (Q ={∅}=∗ P) ⸩(σ s, i) -∗ nninv (σ s) i N P -∗
    nninv (σ s) i N Q.
  Proof.
    rewrite nninv_unseal. iIntros "#PQP (%R & #RPR & #NR)". iExists R.
    iFrame "NR". iModIntro. iApply (sintpy_map2 with "[] PQP RPR").
    iIntros (??) "/= {PQP}PQP {RPR}RPR R". iMod ("RPR" with "R") as "[P PR]".
    iMod ("PQP" with "P") as "[$ QP]". iIntros "!> Q".
    iMod ("QP" with "Q") as "P". by iApply "PR".
  Qed.
  Lemma nninv_split_l {s i N P Q} :
    nninv (σ s) i N (P ∗ Q) -∗ nninv (σ s) i N P.
  Proof.
    iApply nninv_convert. iModIntro. iApply (sintpy_intro (σ:=σ)).
    by iIntros (??) "/=[$$]!>$".
  Qed.
  Lemma nninv_split_r {s i N P Q} :
    nninv (σ s) i N (P ∗ Q) -∗ nninv (σ s) i N Q.
  Proof.
    iApply nninv_convert. iModIntro. iApply (sintpy_intro (σ:=σ)).
    by iIntros (??) "/=[$$]!>$".
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
      iIntros (??); by [iIntros ">$!>$"|iIntros "$!>"; iSplitR; iIntros].
  Qed.
  Lemma nninv_add {s i N P Q} :
    □ ⸨ P ⸩(σ s, i) -∗ nninv (σ s) i N Q -∗ nninv (σ s) i N (P ∗ Q).
  Proof.
    iIntros "#P". iApply nninv_convert. iModIntro.
    iApply (sintpy_map with "[] P"). by iIntros (??) "/=$$!>[_$]".
  Qed.
End lemmas.
