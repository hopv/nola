(** * On the invariant *)

From nola.examples.logic Require Export sintp.

Implicit Type (i : nat) (P Q : nPropL (;ᵞ)).

Section lemmas.
  Context `{!nintpGS Σ}.

  (** Access [na_nninv] *)
  Lemma na_nninv_acc {s i p N P E F} : ↑N ⊆ E → ↑N ⊆ F →
    ssound (ITI:=nintpsi _) s i -∗
    na_nninv s i p N P -∗ na_own p F =[nninv_wsat s]{E,E∖↑N}=∗
      ⟦ P ⟧(s) ∗ na_own p (F∖↑N) ∗
      (⟦ P ⟧(s) -∗ na_own p (F∖↑N) =[nninv_wsat s]{E∖↑N,E}=∗ na_own p F).
  Proof.
    rewrite na_nninv_unseal. iIntros (NE NF) "to #accP F W".
    iDestruct ("to" with "accP") as "/={accP}accP".
    iApply ("accP" $! _ _ NE NF with "F W").
  Qed.

  Context `{!nsintpy Σ σ}.

  (** Access [n_na_inv] *)
  Lemma n_na_inv_acc {s i j p N P E F} : ↑N ⊆ E → ↑N ⊆ F → i < j → ⊢
    ⸨ n_na_inv' [] i p N P -∗ n_na_own p F =[n_inv_wsat]{E,E∖↑N}=∗
        P ∗ n_na_own p (F∖↑N) ∗
        (P -∗ n_na_own p (F∖↑N) =[n_inv_wsat]{E∖↑N,E}=∗ n_na_own p F) ⸩(σ s, j).
  Proof.
    move=> NE NF ij. iApply sintpy_byintp. iIntros (??) "/= _ _ #to".
    iApply (na_nninv_acc NE NF). by iApply "to".
  Qed.

  (** Turn [na_ninv] into [na_nninv] *)
  Lemma na_ninv_nninv {s i j p N} {P : nPropS _} : j ∈ (↑N:coPset) →
    ninv N (nid_na p j P) -∗ na_nninv (Σ:=Σ) (σ s) i p N (↑ˡ P).
  Proof.
    rewrite na_nninv_unseal. iIntros (jN) "#NP !#".
    iApply (sintpy_intro (σ:=σ))=>/=.
    iIntros (?? E F NE NF) "F W". rewrite -nintpS_nintp_nlarge.
    iMod (ninv_acc NE with "NP W") as "/=($& nP & nPto)".
    iDestruct (na_body_acc with "nP F") as "($&$& Pto)"; [done..|].
    iIntros "!> P F∖N W". iDestruct ("Pto" with "P F∖N") as "[nP $]".
    by iMod ("nPto" with "nP W") as "[$ _]".
  Qed.

  (** Allocate [na_nninv] *)
  Lemma na_nninv_alloc_rec {s i p N} {P : nPropS (;ᵞ)} :
    (na_nninv (σ s) i p N (↑ˡ P) -∗ ⟦ P ⟧(σ s)) =[nninv_wsat (σ s)]=∗
      na_nninv (σ s) i p N (↑ˡ P).
  Proof.
    iIntros "toP W". iMod na_lock_alloc as (j) "[% lock]".
    iMod (ninv_alloc_rec (P:=nid_na p j P) with "[toP lock] W") as "[$ NP]".
    - iIntros "/=NP". iLeft. iFrame "lock". rewrite nintpS_nintp.
      iApply "toP". by iApply na_ninv_nninv.
    - iModIntro. by iApply na_ninv_nninv.
  Qed.
  Lemma nninv_alloc {s i p N} {P : nPropS (;ᵞ)} :
    ⟦ P ⟧(σ s) =[nninv_wsat (σ s)]=∗ na_nninv (σ s) i p N (↑ˡ P).
  Proof.
    iIntros "P W". iApply (na_nninv_alloc_rec with "[P] W"). by iIntros.
  Qed.

  (** [na_nninv] is monotone over the level *)
  Lemma na_nninv_mono_lev {s i j p N P} :
    i ≤ j → na_nninv (σ s) i p N P -∗ na_nninv (σ s) j p N P.
  Proof.
    rewrite na_nninv_unseal. iIntros (ij) "#iP !#". by iApply sintpy_mono_lev.
  Qed.

  (** Transform [na_nninv] *)
  Lemma na_nninv_convert {s i p N P Q} :
    □ ⸨ P ={∅}=∗ Q ∗ (Q ={∅}=∗ P) ⸩(σ s, i) -∗ na_nninv (σ s) i p N P -∗
    na_nninv (σ s) i p N Q.
  Proof.
    rewrite na_nninv_unseal. iIntros "#PQP #accP !>".
    iApply (sintpy_map2 with "[] PQP accP")=>/=.
    iIntros (??) "/= {PQP}PQP {accP}accP". iIntros (E F NE NF) "F W".
    iMod ("accP" $! E F NE NF with "F W") as "($& P &$& Pto)".
    iMod (fupd_mask_subseteq ∅) as "toE∖N"; [set_solver|].
    iMod ("PQP" with "P") as "($& QP)". iMod "toE∖N" as "_". iIntros "!> Q W".
    iMod (fupd_mask_subseteq ∅) as "toE∖N"; [set_solver|].
    iMod ("QP" with "Q") as "P". iMod "toE∖N" as "_". iApply ("Pto" with "P W").
  Qed.
  Lemma na_nninv_split {s i p N P Q} :
    na_nninv (σ s) i p N (P ∗ Q) -∗
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
    iIntros (??) "{NP}NP {N'Q}N'Q". iIntros (E F NE NF) "F W".
    iMod ("NP" with "[%] [%] F W") as "(W &$& F∖N & Pto)"; [set_solver..|].
    iMod ("N'Q" with "[%] [%] F∖N W") as "($&$& F∖NN' & Qto)"; [set_solver..|].
    iApply fupd_mask_intro; [set_solver|].
    iDestruct (na_own_acc (F ∖ ↑N'') with "F∖NN'") as "[$ F∖N''to]";
      [set_solver|].
    iIntros "Cl [P Q] F∖N'' W". iMod "Cl".
    iDestruct ("F∖N''to" with "F∖N''") as "F∖NN'".
    iMod ("Qto" with "Q F∖NN' W") as "[W F∖N]". iApply ("Pto" with "P F∖N W").
  Qed.
End lemmas.
