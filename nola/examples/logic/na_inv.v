(** * On the invariant *)

From nola.examples.logic Require Export deriv.

Implicit Type P Q : nPropL (;ᵞ).

Section lemmas.
  Context `{!nintpGS Σ}.
  Implicit Type δ : nderiv_ty Σ.

  (** [na_ninv] is persistent *)
  #[export] Instance na_ninv_persistent {δ p N P} :
    Persistent (na_ninv δ p N P).
  Proof. rewrite na_ninv_unseal. exact _. Qed.

  (** Access [na_ninv] *)
  Lemma na_ninv_acc {p N P E F} : ↑N ⊆ E → ↑N ⊆ F →
    na_own p F -∗ na_ninvd p N P =[na_inv_wsatd]{E}=∗
      na_own p (F∖↑N) ∗ ⟦ P ⟧ ∗
      (na_own p (F∖↑N) -∗ ⟦ P ⟧ =[na_inv_wsatd]{E}=∗ na_own p F).
  Proof.
    rewrite na_ninv_unseal. iIntros (NE NF) "F #∝P".
    iDestruct nderiv_sound as "→".
    iDestruct ("→" with "∝P") as "/={∝P}∝P".
    iApply ("∝P" $! _ _ NE NF with "F").
  Qed.

  Context `{!nDeriv ih δ}.

  (** Turn [na_ninv] into [na_ninv] *)
  Local Lemma na_inv_tok_ninv {P : nPropS _} {p N} :
    na_inv_tok p N P ⊢ na_ninv (Σ:=Σ) δ p N (↑ˡ P).
  Proof.
    rewrite na_ninv_unseal. iIntros "#NP !>". iApply (Deriv_intro (δ:=δ))=>/=.
    iIntros (???????) "F". rewrite -nintpS_nintp_nlarge.
    by iApply (na_inv_tok_acc with "F NP").
  Qed.
  (** Allocate [na_ninv] *)
  Lemma na_ninv_alloc_rec (P : nPropS _) p N :
    (na_ninv δ p N (↑ˡ P) -∗ ⟦ P ⟧(δ)) =[na_inv_wsat' δ]=∗
      na_ninv δ p N (↑ˡ P).
  Proof.
    rewrite -na_inv_tok_ninv -nintpS_nintp. exact: na_inv_tok_alloc_rec.
  Qed.
  Lemma na_ninv_alloc (P : nPropS _) p N :
    ⟦ P ⟧(δ) =[na_inv_wsat' δ]=∗ na_ninv δ p N (↑ˡ P).
  Proof.
    iIntros "P". iApply (na_ninv_alloc_rec with "[P]"). by iIntros.
  Qed.

  (** Transform [na_ninv] *)
  Lemma na_ninv_convert {p N P Q} :
    □ ⸨ P ={∅}=∗ Q ∗ (Q ={∅}=∗ P) ⸩(δ) -∗ na_ninv δ p N P -∗ na_ninv δ p N Q.
  Proof.
    rewrite na_ninv_unseal. iIntros "#PQP #∝P !>".
    iApply (Deriv_map2 with "[] PQP ∝P")=>/=.
    iIntros (???) "/= {PQP}PQP {∝P}∝P". iIntros (E F NE NF) "F".
    iMod ("∝P" $! E F NE NF with "F") as "[$[P P→]]".
    iMod (fupd_mask_subseteq ∅) as "→E∖N"; [set_solver|].
    iMod ("PQP" with "P") as "[$ QP]". iMod "→E∖N" as "_". iIntros "!> F∖N Q".
    iMod (fupd_mask_subseteq ∅) as "→E∖N"; [set_solver|].
    iMod ("QP" with "Q") as "P". iMod "→E∖N" as "_". iApply ("P→" with "F∖N P").
  Qed.
  Lemma na_ninv_split {p N P Q} :
    na_ninv δ p N (P ∗ Q) ⊢ na_ninv δ p N P ∗ na_ninv δ p N Q.
  Proof.
    iIntros "#NPQ".
    iSplit; iApply (na_ninv_convert with "[] NPQ"); iModIntro;
      iApply (Deriv_intro (δ:=δ)); by iIntros (???) "/=[$$]!>$".
  Qed.
  Lemma na_ninv_fupd {p N P} : na_ninv δ p N (|={∅}=> P) ⊣⊢ na_ninv δ p N P.
  Proof.
    iSplit; iApply na_ninv_convert; iModIntro;
      iApply (Deriv_intro (δ:=δ))=>/=; iIntros (???);
      by [iIntros ">$!>$"|iIntros "$!>"; iSplitR; iIntros].
  Qed.
  Lemma na_ninv_add {p N P Q} :
    □ ⸨ P ⸩(δ) -∗ na_ninv δ p N Q -∗ na_ninv δ p N (P ∗ Q).
  Proof.
    iIntros "#P". iApply na_ninv_convert. iModIntro.
    iApply (Deriv_map with "[] P"). by iIntros (???) "/=$$!>[_$]".
  Qed.

  (** Combine [na_ninv]s *)
  Lemma ninv_combine {p N N' N'' P Q} : N ## N' → ↑N ∪ ↑N' ⊆@{coPset} ↑N'' →
    na_ninv δ p N P -∗ na_ninv δ p N' Q -∗ na_ninv δ p N'' (P ∗ Q).
  Proof.
    rewrite na_ninv_unseal. iIntros (??) "#NP #N'Q !>".
    iApply (Deriv_map2 (ih:=ih) with "[] NP N'Q")=>/=.
    iIntros (???) "{NP}NP {N'Q}N'Q". iIntros (? F ??) "F".
    iMod ("NP" with "[%] [%] F") as "[F∖N[$ P→]]"; [set_solver..|].
    iMod ("N'Q" with "[%] [%] F∖N") as "[F∖NN'[$ Q→]]"; [set_solver..|].
    iDestruct (na_own_acc with "F∖NN'") as "[$ F∖N''→]"; [set_solver|].
    iApply fupdw_mask_intro; [set_solver|]. iIntros "cl F∖N'' [P Q]".
    iMod "cl" as "_". iDestruct ("F∖N''→" with "F∖N''") as "F∖NN'".
    iMod ("Q→" with "F∖NN' Q") as "F∖N". iApply ("P→" with "F∖N P").
  Qed.
End lemmas.
