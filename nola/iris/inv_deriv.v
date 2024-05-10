(** * Relaxed [inv] with [der] *)

From nola.iris Require Export util deriv inv.
From iris.proofmode Require Import proofmode.
Import DerivIntpNotation DerivNotation.

Section inv_deriv.
  Context `{!inv'GS PROP Σ, !invGS_gen hlc Σ}.

  (** Accessor *)
  Definition inv_acsr' intp N P : iProp Σ :=
    ∀ E, ⌜↑N ⊆ E⌝ → |=[inv_wsat intp]{E,E∖↑N}=>
      P ∗ (P =[inv_wsat intp]{E∖↑N,E}=∗ True).

  (** Derivability data for [inv] *)
  Class DerivInv (DER : derivst (iProp Σ)) := DERIV_INV {
    deriv_inv_intp : deriv_ty DER (iProp Σ) → PROP $o iProp Σ → iProp Σ;
    deriv_inv_ne {δ} :: NonExpansive (deriv_inv_intp δ);
    deriv_inv_acsr : namespace → PROP $o iProp Σ → DER;
    deriv_inv_acsr_intp {δ N P} :
      ⟦ deriv_inv_acsr N P ⟧(δ) ≡
        inv_acsr' (deriv_inv_intp δ) N (deriv_inv_intp δ P);
  }.
End inv_deriv.
Notation inv_ascr δ N P := (inv_acsr' (deriv_inv_intp δ) N P).

Section inv_deriv.
  Local Notation "⟦ P ⟧' ( δ )" := (deriv_inv_intp δ P)
    (format "'[' ⟦  P  ⟧' '/  ' ( δ ) ']'") : nola_scope.
  Local Notation "⟦ P ⟧'" := (⟦ P ⟧'(der)).

  Context `{!inv'GS PROP Σ, !invGS_gen hlc Σ, !DerivInv DER}.

  (** [inv']: Relaxed invariant *)
  Definition inv' δ N P : iProp Σ := □ ⸨ deriv_inv_acsr N P ⸩(δ).

  (** [inv'] is persistent *)
  Fact inv'_persistent {δ N P} : Persistent (inv' δ N P).
  Proof. exact _. Qed.

  (** World satisfaction *)
  Definition inv_wsatd δ := inv_wsat (deriv_inv_intp δ).

  (** Access [inv'] *)
  Lemma inv'_acc {N P E} : ↑N ⊆ E →
    inv' der N P =[inv_wsatd der]{E,E∖↑N}=∗
      ⟦ P ⟧' ∗ (⟦ P ⟧' =[inv_wsatd der]{E∖↑N,E}=∗ True).
  Proof.
    iIntros (?) "accP". iDestruct (der_sound with "accP") as "accP".
    rewrite deriv_inv_acsr_intp. by iApply "accP".
  Qed.

  Context `{!Deriv (DER:=DER) ih δ}.

  (** Turn [inv_tok] into [inv'] *)
  Lemma inv_tok_inv' {N P} : inv_tok N P ⊢ inv' δ N P.
  Proof.
    iIntros "#i !>". iApply Deriv_intro. iIntros (? _ _).
    rewrite deriv_inv_acsr_intp. iIntros (??). by iApply (inv_tok_acc with "i").
  Qed.

  (** Allocate [inv'] *)
  Lemma inv'_alloc_rec P N :
    (inv' δ N P -∗ ⟦ P ⟧'(δ)) =[inv_wsatd δ]=∗ inv' δ N P.
  Proof. rewrite -inv_tok_inv'. exact: inv_tok_alloc_rec. Qed.
  Lemma inv'_alloc P N : ⟦ P ⟧'(δ) =[inv_wsatd δ]=∗ inv' δ N P.
  Proof. rewrite -inv_tok_inv'. exact: inv_tok_alloc. Qed.

  (** Convert [inv'] with [acsr] *)
  Lemma inv'_acsr {N P Q} :
    □ (∀ δ, acsr (fupd ∅ ∅) ⟦ P ⟧'(δ) ⟦ Q ⟧'(δ)) -∗
    inv' δ N Q -∗ inv' δ N P.
  Proof.
    iIntros "#QPQ #accQ !>". iApply Deriv_byintp. iIntros (? _ _) "#→ _".
    iDestruct ("→" with "accQ") as "{accQ}accQ". rewrite !deriv_inv_acsr_intp.
    iIntros (? NE). iMod ("accQ" $! _ NE) as "[Q cl]".
    iMod (fupd_mask_subseteq ∅) as "→E∖N"; [set_solver|].
    iMod ("QPQ" with "Q") as "($& PQ)". iMod "→E∖N" as "_". iIntros "!> P".
    iMod (fupd_mask_subseteq ∅) as "→E∖N"; [set_solver|].
    iMod ("PQ" with "P") as "Q". iMod "→E∖N" as "_". iApply ("cl" with "Q").
  Qed.

  (** Split [inv'] over [∗] *)
  Local Lemma inv'_sep' {N PQ P Q} :
    (∀ δ, ⟦ PQ ⟧'(δ) ≡ (⟦ P ⟧'(δ) ∗ ⟦ Q ⟧'(δ))%I) → inv' δ N PQ ⊢ inv' δ N P.
  Proof.
    iIntros (eq). iApply (inv'_acsr with "[]"). iIntros "!>" (?).
    unfold acsr. rewrite eq. iApply (acsr_sep_l (M:=fupd _ _)).
  Qed.
  Lemma inv'_sep {N PQ P Q} : (∀ δ, ⟦ PQ ⟧'(δ) ≡ (⟦ P ⟧'(δ) ∗ ⟦ Q ⟧'(δ))%I) →
    inv' δ N PQ ⊢ inv' δ N P ∗ inv' δ N Q.
  Proof.
    iIntros (eq) "#i". iSplit; [by iApply inv'_sep'|].
    iApply (inv'_sep' with "i"). iIntros (?). by rewrite eq comm.
  Qed.

  (** Merge [inv']s with [∗] *)
  Lemma inv'_merge {N1 N2 N P Q PQ} : N1 ## N2 → ↑N1 ∪ ↑N2 ⊆@{coPset} ↑N →
    (∀ δ, ⟦ PQ ⟧'(δ) ≡ (⟦ P ⟧'(δ) ∗ ⟦ Q ⟧'(δ))%I) →
    inv' δ N1 P -∗ inv' δ N2 Q -∗ inv' δ N PQ.
  Proof.
    iIntros (?? eq) "#i #i' !>". iApply (Deriv_map2 with "[] i i'").
    iIntros (? _ _) "{i}i {i'}i'". rewrite !deriv_inv_acsr_intp. iIntros (??).
    rewrite eq. iMod ("i" with "[%]") as "[$ P→]"; [set_solver|].
    iMod ("i'" with "[%]") as "[$ Q→]"; [set_solver|].
    iApply fupdw_mask_intro; [set_solver|]. iIntros "cl [P Q]".
    iMod "cl" as "_". iMod ("Q→" with "Q") as "_". iApply ("P→" with "P").
  Qed.
End inv_deriv.
