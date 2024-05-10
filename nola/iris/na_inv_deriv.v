(** * Relaxed [na_inv] with [der] *)

From nola.iris Require Export util deriv na_inv.
From iris.proofmode Require Import proofmode.
Import IntpNotation DerivNotation.

Section na_inv_deriv.
  Context `{!na_inv'GS PROP Σ, !invGS_gen hlc Σ, !na_invG Σ}.

  (** Accessor *)
  Definition na_inv_acsr' intp p N P : iProp Σ :=
    ∀ E F, ⌜↑N ⊆ E⌝ → ⌜↑N ⊆ F⌝ → na_own p F =[na_inv_wsat intp]{E}=∗
      na_own p (F∖↑N) ∗ P ∗
      (na_own p (F∖↑N) -∗ P =[na_inv_wsat intp]{E}=∗ na_own p F) .

  (** Derivability data for [na_inv] *)
  Class DerivNaInv (DER : derivst (iProp Σ)) := DERIV_NA_INV {
    deriv_na_inv_intp : deriv_ty DER (iProp Σ) → PROP $o iProp Σ → iProp Σ;
    deriv_na_inv_ne {δ} :: NonExpansive (deriv_na_inv_intp δ);
    deriv_na_inv_acsr : na_inv_pool_name → namespace → PROP $o iProp Σ → DER;
    deriv_na_inv_acsr_intp {δ p N P} :
      ⟦ deriv_na_inv_acsr p N P ⟧(δ) ≡
        na_inv_acsr' (deriv_na_inv_intp δ) p N (deriv_na_inv_intp δ P);
  }.
End na_inv_deriv.
Notation na_inv_ascr δ p N P := (na_inv_acsr' (deriv_na_inv_intp δ) p N P).

Section na_inv_deriv.
  Local Notation "⟦ P ⟧' ( δ )" := (deriv_na_inv_intp δ P)
    (format "'[' ⟦  P  ⟧' '/  ' ( δ ) ']'") : nola_scope.
  Local Notation "⟦ P ⟧'" := (⟦ P ⟧'(der)).

  Context `{!na_inv'GS PROP Σ, !invGS_gen hlc Σ, !na_invG Σ, !DerivNaInv DER}.

  (** [na_inv']: Relaxed na_invariant *)
  Definition na_inv' δ p N P : iProp Σ := □ ⸨ deriv_na_inv_acsr p N P ⸩(δ).

  (** [na_inv'] is persistent *)
  Fact na_inv'_persistent {δ p N P} : Persistent (na_inv' δ p N P).
  Proof. exact _. Qed.

  (** World satisfaction *)
  Definition na_inv_wsatd δ := na_inv_wsat (deriv_na_inv_intp δ).

  (** Access [na_inv'] *)
  Lemma na_inv'_acc {p N P E F} : ↑N ⊆ E → ↑N ⊆ F →
    na_own p F -∗ na_inv' der p N P =[na_inv_wsatd der]{E}=∗
      na_own p (F∖↑N) ∗ ⟦ P ⟧' ∗
      (na_own p (F∖↑N) -∗ ⟦ P ⟧' =[na_inv_wsatd der]{E}=∗ na_own p F).
  Proof.
    iIntros (NE NF) "F accP". iDestruct (der_sound with "accP") as "accP".
    rewrite deriv_na_inv_acsr_intp. iApply ("accP" $! _ _ NE NF with "F").
  Qed.

  Context `{!Deriv (DER:=DER) ih δ}.

  (** Turn [na_inv_tok] into [na_inv'] *)
  Lemma na_inv_tok_na_inv' {p N P} : na_inv_tok p N P ⊢ na_inv' δ p N P.
  Proof.
    iIntros "#i !>". iApply Deriv_intro. iIntros (? _ _).
    rewrite deriv_na_inv_acsr_intp. iIntros (????) "F".
    by iApply (na_inv_tok_acc with "F i").
  Qed.

  (** Allocate [na_inv'] *)
  Lemma na_inv'_alloc_rec p P N :
    (na_inv' δ p N P -∗ ⟦ P ⟧'(δ)) =[na_inv_wsatd δ]=∗ na_inv' δ p N P.
  Proof. rewrite -na_inv_tok_na_inv'. exact: na_inv_tok_alloc_rec. Qed.
  Lemma na_inv'_alloc p P N : ⟦ P ⟧'(δ) =[na_inv_wsatd δ]=∗ na_inv' δ p N P.
  Proof. rewrite -na_inv_tok_na_inv'. exact: na_inv_tok_alloc. Qed.

  (** Convert [na_inv'] with [acsr] *)
  Lemma na_inv'_acsr {p N P Q} :
    □ (∀ δ, acsr (fupd ∅ ∅) ⟦ P ⟧'(δ) ⟦ Q ⟧'(δ)) -∗
    na_inv' δ p N Q -∗ na_inv' δ p N P.
  Proof.
    iIntros "#QPQ #accQ !>". iApply Deriv_byintp. iIntros (? _ _) "#→ _".
    iDestruct ("→" with "accQ") as "{accQ}accQ".
    rewrite !deriv_na_inv_acsr_intp. iIntros (?? NE NF) "F".
    iMod ("accQ" $! _ _ NE NF with "F") as "($ & Q & cl)".
    iMod (fupd_mask_subseteq ∅) as "→E∖N"; [set_solver|].
    iMod ("QPQ" with "Q") as "[$ PQ]". iMod "→E∖N" as "_". iIntros "!>".
    iMod (fupd_mask_subseteq ∅) as "→E∖N"; [set_solver|]. iIntros "F∖N P".
    iMod ("PQ" with "P") as "Q". iMod "→E∖N" as "_". iApply ("cl" with "F∖N Q").
  Qed.

  (** Split [na_inv'] over [∗] *)
  Local Lemma na_inv'_sep' {p N PQ P Q} :
    (∀ δ, ⟦ PQ ⟧'(δ) ≡ (⟦ P ⟧'(δ) ∗ ⟦ Q ⟧'(δ))%I) →
    na_inv' δ p N PQ ⊢ na_inv' δ p N P.
  Proof.
    iIntros (eq). iApply (na_inv'_acsr with "[]"). iIntros "!>" (?).
    unfold acsr. rewrite eq. iApply (acsr_sep_l (M:=fupd _ _)).
  Qed.
  Lemma na_inv'_sep {p N PQ P Q} :
    (∀ δ, ⟦ PQ ⟧'(δ) ≡ (⟦ P ⟧'(δ) ∗ ⟦ Q ⟧'(δ))%I) →
    na_inv' δ p N PQ ⊢ na_inv' δ p N P ∗ na_inv' δ p N Q.
  Proof.
    iIntros (eq) "#i". iSplit; [by iApply na_inv'_sep'|].
    iApply (na_inv'_sep' with "i"). iIntros (?). by rewrite eq comm.
  Qed.

  (** Merge [na_inv']s with [∗] *)
  Lemma na_inv'_merge {p N1 N2 N P Q PQ} : N1 ## N2 → ↑N1 ∪ ↑N2 ⊆@{coPset} ↑N →
    (∀ δ, ⟦ PQ ⟧'(δ) ≡ (⟦ P ⟧'(δ) ∗ ⟦ Q ⟧'(δ))%I) →
    na_inv' δ p N1 P -∗ na_inv' δ p N2 Q -∗ na_inv' δ p N PQ.
  Proof.
    iIntros (?? eq) "#i #i' !>". iApply (Deriv_map2 with "[] i i'").
    iIntros (? _ _) "{i}i {i'}i'". rewrite !deriv_na_inv_acsr_intp.
    iIntros (????) "F". rewrite eq.
    iMod ("i" with "[%] [%] F") as "(F∖N1 & $ & P→)"; [set_solver..|].
    iMod ("i'" with "[%] [%] F∖N1") as "(F∖N12 & $ & Q→)"; [set_solver..|].
    iDestruct (na_own_acc with "F∖N12") as "[$ F∖N→]"; [set_solver|].
    iApply fupdw_mask_intro; [set_solver|]. iIntros "cl F∖N [P Q]".
    iMod "cl" as "_". iDestruct ("F∖N→" with "F∖N") as "F∖N12".
    iMod ("Q→" with "F∖N12 Q") as "F∖N". iApply ("P→" with "F∖N P").
  Qed.
End na_inv_deriv.
