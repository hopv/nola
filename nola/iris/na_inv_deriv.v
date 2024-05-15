(** * Relaxed [na_inv] with [der] *)

From nola.iris Require Export util deriv na_inv.
From iris.proofmode Require Import proofmode.
Import OfeNotation PintpNotation UpdwNotation.

(** Notation *)
Notation na_inv_wsatd δ := (na_inv_wsat ⟦⟧(δ)).

(** Derivability pre-data for [na_inv] *)
Class NaInvPreDeriv PRO JUD :=
  na_inv_jacsr : na_inv_pool_name → namespace → PRO → JUD.
Hint Mode NaInvPreDeriv ! - : typeclass_instances.

Section na_inv_deriv.
  Context `{!NaInvPreDeriv PRO JUD} {Σ : gFunctors}.

  (** [na_inv']: Relaxed na_invariant *)
  Definition na_inv' δ p N (P : PRO) : iProp Σ := □ δ (na_inv_jacsr p N P).

  (** [na_inv'] is persistent *)
  Fact na_inv'_persistent {δ p N P} : Persistent (na_inv' δ p N P).
  Proof. exact _. Qed.
End na_inv_deriv.

Section na_inv_deriv.
  Context `{!na_inv'GS PROP Σ, !invGS_gen hlc Σ, !na_invG Σ}.
  Implicit Type P Q PQ : PROP $o Σ.

  (** Accessor *)
  Definition na_inv_acsr intp p N Pi : iProp Σ :=
    ∀ E F, ⌜↑N ⊆ E⌝ → ⌜↑N ⊆ F⌝ → na_own p F =[na_inv_wsat intp]{E}=∗
      na_own p (F∖↑N) ∗ Pi ∗
      (na_own p (F∖↑N) -∗ Pi =[na_inv_wsat intp]{E}=∗ na_own p F) .

  Context `{!NaInvPreDeriv (PROP $o Σ) (JUDG : judg (iProp Σ)),
    !Dintp JUDG (PROP $o Σ) (iProp Σ)}.

  (** Derivability data for [na_inv] *)
  Class NaInvDeriv :=
    na_inv_jacsr_intp : ∀{δ p N P},
      ⟦ na_inv_jacsr p N P ⟧(δ) ≡ na_inv_acsr ⟦⟧(δ) p N (⟦ P ⟧(δ)).

  Context `{!NaInvDeriv}.

  (** Access [na_inv'] *)
  Lemma na_inv'_acc {p N P E F} : ↑N ⊆ E → ↑N ⊆ F →
    na_own p F -∗ na_inv' der p N P =[na_inv_wsatd der]{E}=∗
      na_own p (F∖↑N) ∗ ⟦ P ⟧(der) ∗
      (na_own p (F∖↑N) -∗ ⟦ P ⟧(der) =[na_inv_wsatd der]{E}=∗ na_own p F).
  Proof.
    iIntros (NE NF) "F accP". iDestruct (der_sound with "accP") as "accP".
    rewrite na_inv_jacsr_intp. iApply ("accP" $! _ _ NE NF with "F").
  Qed.

  Context `{!Deriv (JUDG:=JUDG) ih δ}.

  (** Turn [na_inv_tok] into [na_inv'] *)
  Lemma na_inv_tok_na_inv' {p N P} : na_inv_tok p N P ⊢ na_inv' δ p N P.
  Proof.
    iIntros "#i !>". iApply Deriv_to. iIntros (? _ _ _).
    rewrite na_inv_jacsr_intp. iIntros (????) "F".
    by iApply (na_inv_tok_acc (intp:=⟦⟧(_)) with "F i").
  Qed.

  (** Allocate [na_inv'] *)
  Lemma na_inv'_alloc_rec p P N :
    (na_inv' δ p N P -∗ ⟦ P ⟧(δ)) =[na_inv_wsatd δ]=∗ na_inv' δ p N P.
  Proof. rewrite -na_inv_tok_na_inv'. exact: na_inv_tok_alloc_rec. Qed.
  Lemma na_inv'_alloc p P N : ⟦ P ⟧(δ) =[na_inv_wsatd δ]=∗ na_inv' δ p N P.
  Proof. rewrite -na_inv_tok_na_inv'. exact: na_inv_tok_alloc. Qed.
  Lemma na_inv'_alloc_open p N E F P :
    ↑N ⊆ E → ↑N ⊆ F →
    na_own p F =[na_inv_wsatd δ]{E}=∗
      na_own p (F∖↑N) ∗ na_inv' δ p N P ∗
      (na_own p (F∖↑N) -∗ ⟦ P ⟧(δ) =[na_inv_wsatd δ]{E}=∗ na_own p F).
  Proof. rewrite -na_inv_tok_na_inv'. exact: na_inv_tok_alloc_open. Qed.

  (** Convert [na_inv'] with [acsr] *)
  Lemma na_inv'_acsr {p N P Q} :
    □ (∀ δ, acsr (fupd ∅ ∅) ⟦ P ⟧(δ) ⟦ Q ⟧(δ)) -∗
    na_inv' δ p N Q -∗ na_inv' δ p N P.
  Proof.
    iIntros "#QPQ #accQ !>". iApply Deriv_to. iIntros (? _ _ ->).
    rewrite !na_inv_jacsr_intp. iIntros (?? NE NF) "F".
    iMod ("accQ" $! _ _ NE NF with "F") as "($ & Q & cl)".
    iMod (fupd_mask_subseteq ∅) as "→E∖N"; [set_solver|].
    iMod ("QPQ" with "Q") as "[$ PQ]". iMod "→E∖N" as "_". iIntros "!>".
    iMod (fupd_mask_subseteq ∅) as "→E∖N"; [set_solver|]. iIntros "F∖N P".
    iMod ("PQ" with "P") as "Q". iMod "→E∖N" as "_". iApply ("cl" with "F∖N Q").
  Qed.

  (** Split [na_inv'] over [∗] *)
  Local Lemma na_inv'_sep' {p N PQ P Q} :
    (∀ δ, ⟦ PQ ⟧(δ) ≡ (⟦ P ⟧(δ) ∗ ⟦ Q ⟧(δ))%I) →
    na_inv' δ p N PQ ⊢ na_inv' δ p N P.
  Proof.
    iIntros (eq). iApply (na_inv'_acsr with "[]"). iIntros "!>" (?).
    unfold acsr. rewrite eq. iApply (acsr_sep_l (M:=fupd _ _)).
  Qed.
  Lemma na_inv'_sep {p N PQ P Q} :
    (∀ δ, ⟦ PQ ⟧(δ) ≡ (⟦ P ⟧(δ) ∗ ⟦ Q ⟧(δ))%I) →
    na_inv' δ p N PQ ⊢ na_inv' δ p N P ∗ na_inv' δ p N Q.
  Proof.
    iIntros (eq) "#i". iSplit; [by iApply na_inv'_sep'|].
    iApply (na_inv'_sep' with "i"). iIntros (?). by rewrite eq comm.
  Qed.

  (** Merge [na_inv']s with [∗] *)
  Lemma na_inv'_merge {p N1 N2 N P Q PQ} : N1 ## N2 → ↑N1 ∪ ↑N2 ⊆@{coPset} ↑N →
    (∀ δ, ⟦ PQ ⟧(δ) ≡ (⟦ P ⟧(δ) ∗ ⟦ Q ⟧(δ))%I) →
    na_inv' δ p N1 P -∗ na_inv' δ p N2 Q -∗ na_inv' δ p N PQ.
  Proof.
    iIntros (?? eq) "#i #i' !>". iApply (Deriv_map2 with "[] i i'").
    iIntros (? _ _) "{i}i {i'}i'". rewrite !na_inv_jacsr_intp.
    iIntros (????) "F". rewrite eq.
    iMod ("i" with "[%] [%] F") as "(F∖N1 & $ & P→)"; [set_solver..|].
    iMod ("i'" with "[%] [%] F∖N1") as "(F∖N12 & $ & Q→)"; [set_solver..|].
    iDestruct (na_own_acc with "F∖N12") as "[$ F∖N→]"; [set_solver|].
    iApply fupdw_mask_intro; [set_solver|]. iIntros "cl F∖N [P Q]".
    iMod "cl" as "_". iDestruct ("F∖N→" with "F∖N") as "F∖N12".
    iMod ("Q→" with "F∖N12 Q") as "F∖N". iApply ("P→" with "F∖N P").
  Qed.
End na_inv_deriv.
Arguments NaInvDeriv PROP Σ {_ _ _ _} JUDG {_ _}.
Hint Mode NaInvDeriv ! - - - - - - - - : typeclass_instances.
