(** * On the simple invariant *)

From nola.examples.logic Require Export deriv.

Section lemmas.
  Context `{!nintpGS Σ}.
  Implicit Type δ : nderiv_ty Σ.

  (** [sinv] is persistent *)
  #[export] Instance sinv_persistent {δ P} : Persistent (sinv δ P).
  Proof. rewrite sinv_unseal. exact _. Qed.

  (** Access [sinv] *)
  Lemma sinv_acc {P} :
    sinvd P -∗ sinv_wsatd -∗ ⟦ P ⟧ ∗ (⟦ P ⟧ -∗ sinv_wsatd).
  Proof.
    rewrite sinv_unseal. iIntros "#∝P". iDestruct nderiv_sound as "→".
    iApply ("→" with "∝P").
  Qed.

  Context `{!nDeriv ih δ}.

  (** Turn [sinv_tok] into [sinv] *)
  Local Lemma sinv_tok_sinv {P : nPropS _} : sinv_tok P ⊢ sinv δ (↑ˡ P).
  Proof.
    rewrite sinv_unseal. iIntros "#∝P !>". iApply (Deriv_intro (δ:=δ))=>/=.
    iIntros (???). rewrite -nintpS_nintp_nlarge.
    iApply (sinv_tok_acc (intp:=λ _, ⟦_⟧ˢ(_)) with "∝P").
  Qed.
  (** Allocate [sinv] *)
  Lemma sinv_alloc (P : nPropS _) :
    sinv_wsat' δ ==∗ sinv δ (↑ˡ P) ∗ (⟦ P ⟧(δ) -∗ sinv_wsat' δ).
  Proof. rewrite -sinv_tok_sinv -nintpS_nintp. exact: sinv_tok_alloc. Qed.

  (** Transform [sinv] *)
  Lemma sinv_alter {P Q} : □ ⸨ P -∗ Q ∗ (Q -∗ P) ⸩(δ) -∗ sinv δ P -∗ sinv δ Q.
  Proof.
    rewrite sinv_unseal. iIntros "#PQP #∝P !>".
    iApply (Deriv_map2 with "[] PQP ∝P")=>/=.
    iIntros (???) "/= {PQP}PQP {∝P}∝P W". iDestruct ("∝P" with "W") as "[P P→]".
    iDestruct ("PQP" with "P") as "[$ Q→]". iIntros "Q". iApply "P→".
    by iApply "Q→".
  Qed.
  Lemma sinv_split {P Q} :
    sinv δ (P ∗ Q) ⊢ sinv δ P ∗ sinv δ Q.
  Proof.
    iIntros "#∝PQ".
    iSplit; iApply (sinv_alter with "[] ∝PQ"); iModIntro;
      iApply (Deriv_intro (δ:=δ)); iIntros (???) "/=[$$]$".
  Qed.
  Lemma sinv_add {P Q} : □ ⸨ P ⸩(δ) -∗ sinv δ Q -∗ sinv δ (P ∗ Q).
  Proof.
    iIntros "#P". iApply sinv_alter. iModIntro.
    iApply (Deriv_map with "[] P"). iIntros (???) "/=$$[_$]".
  Qed.
End lemmas.
