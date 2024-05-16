(** * Relaxed [inv] with [der] *)

From nola.bi Require Export util deriv.
From nola.iris Require Export inv.
From iris.proofmode Require Import proofmode.
Import iPropAppNotation PintpNotation UpdwNotation.

(** Notation *)
Notation inv_wsatd δ := (inv_wsat ⟦⟧(δ)).

(** Derivability pre-data for [inv] *)
Class InvPreDeriv PRO JUD := inv_jacsr : namespace → PRO → JUD.
Hint Mode InvPreDeriv ! - : typeclass_instances.

Section inv_deriv.
  Context `{!InvPreDeriv PRO JUD} {Σ : gFunctors}.

  (** [inv']: Relaxed invariant *)
  Definition inv' δ N (P : PRO) : iProp Σ := □ δ (inv_jacsr N P).

  (** [inv'] is persistent *)
  Fact inv'_persistent {δ N P} : Persistent (inv' δ N P).
  Proof. exact _. Qed.
End inv_deriv.

Section inv_deriv.
  Context `{!inv'GS PROP Σ, !invGS_gen hlc Σ}.
  Implicit Type P Q PQ : PROP $oi Σ.

  (** Accessor *)
  Definition inv_acsr intp N Pi : iProp Σ :=
    ∀ E, ⌜↑N ⊆ E⌝ → |=[inv_wsat intp]{E,E∖↑N}=>
      Pi ∗ (Pi =[inv_wsat intp]{E∖↑N,E}=∗ True).

  Context `{!InvPreDeriv (PROP $oi Σ) (JUDG : judg (iProp Σ)),
    !Dintp JUDG (PROP $oi Σ) (iProp Σ)}.

  (** Derivability data for [inv] *)
  Class InvDeriv :=
    inv_jacsr_intp : ∀{δ N P}, ⟦ inv_jacsr N P ⟧(δ) ≡ inv_acsr ⟦⟧(δ) N ⟦ P ⟧(δ).

  Context `{!InvDeriv}.

  (** Access [inv'] *)
  Lemma inv'_acc {N P E} : ↑N ⊆ E →
    inv' der N P =[inv_wsatd der]{E,E∖↑N}=∗
      ⟦ P ⟧(der) ∗ (⟦ P ⟧(der) =[inv_wsatd der]{E∖↑N,E}=∗ True).
  Proof.
    iIntros (?) "accP". iDestruct (der_sound with "accP") as "accP".
    rewrite inv_jacsr_intp. by iApply "accP".
  Qed.

  Context `{!Deriv (JUDG:=JUDG) ih δ}.

  (** Turn [inv_tok] into [inv'] *)
  Lemma inv_tok_inv' {N P} : inv_tok N P ⊢ inv' δ N P.
  Proof.
    iIntros "#i !>". iApply Deriv_to. iIntros (? _ _ _).
    rewrite inv_jacsr_intp. iIntros (??).
    by iApply (inv_tok_acc (intp:=⟦⟧(_)) with "i").
  Qed.

  (** Allocate [inv'] *)
  Lemma inv'_alloc_rec P N :
    (inv' δ N P -∗ ⟦ P ⟧(δ)) =[inv_wsatd δ]=∗ inv' δ N P.
  Proof. rewrite -inv_tok_inv'. exact: inv_tok_alloc_rec. Qed.
  Lemma inv'_alloc P N : ⟦ P ⟧(δ) =[inv_wsatd δ]=∗ inv' δ N P.
  Proof. rewrite -inv_tok_inv'. exact: inv_tok_alloc. Qed.
  Lemma inv'_alloc_open P N E : ↑N ⊆ E →
    ⊢ |=[inv_wsatd δ]{E, E∖↑N}=> inv' δ N P ∗
      (⟦ P ⟧(δ) =[inv_wsatd δ]{E∖↑N, E}=∗ True).
  Proof. rewrite -inv_tok_inv'. exact: inv_tok_alloc_open. Qed.

  (** Convert [inv'] with [acsr] *)
  Lemma inv'_acsr {N P Q} :
    □ (∀ δ, acsr (fupd ∅ ∅) ⟦ P ⟧(δ) ⟦ Q ⟧(δ)) -∗
      inv' δ N Q -∗ inv' δ N P.
  Proof.
    iIntros "#QPQ #accQ !>". iApply Deriv_to. iIntros (? _ _ ->).
    rewrite !inv_jacsr_intp. iIntros (? NE). iMod ("accQ" $! _ NE) as "[Q cl]".
    iMod (fupd_mask_subseteq ∅) as "→E∖N"; [set_solver|].
    iMod ("QPQ" with "Q") as "($& PQ)". iMod "→E∖N" as "_". iIntros "!> P".
    iMod (fupd_mask_subseteq ∅) as "→E∖N"; [set_solver|].
    iMod ("PQ" with "P") as "Q". iMod "→E∖N" as "_". iApply ("cl" with "Q").
  Qed.

  (** Split [inv'] over [∗] *)
  Local Lemma inv'_sep' {N PQ P Q} :
    (∀ δ, ⟦ PQ ⟧(δ) ≡ (⟦ P ⟧(δ) ∗ ⟦ Q ⟧(δ))%I) → inv' δ N PQ ⊢ inv' δ N P.
  Proof.
    iIntros (eq). iApply (inv'_acsr with "[]"). iIntros "!>" (?).
    unfold acsr. rewrite eq. iApply (acsr_sep_l (M:=fupd _ _)).
  Qed.
  Lemma inv'_sep {N PQ P Q} : (∀ δ, ⟦ PQ ⟧(δ) ≡ (⟦ P ⟧(δ) ∗ ⟦ Q ⟧(δ))%I) →
    inv' δ N PQ ⊢ inv' δ N P ∗ inv' δ N Q.
  Proof.
    iIntros (eq) "#i". iSplit; [by iApply inv'_sep'|].
    iApply (inv'_sep' with "i"). iIntros (?). by rewrite eq comm.
  Qed.

  (** Merge [inv']s with [∗] *)
  Lemma inv'_merge {N1 N2 N P Q PQ} : N1 ## N2 → ↑N1 ∪ ↑N2 ⊆@{coPset} ↑N →
    (∀ δ, ⟦ PQ ⟧(δ) ≡ (⟦ P ⟧(δ) ∗ ⟦ Q ⟧(δ))%I) →
    inv' δ N1 P -∗ inv' δ N2 Q -∗ inv' δ N PQ.
  Proof.
    iIntros (?? eq) "#i #i' !>". iApply (Deriv_map2 with "[] i i'").
    iIntros (? _ _) "{i}i {i'}i'". rewrite !inv_jacsr_intp. iIntros (??).
    rewrite eq. iMod ("i" with "[%]") as "[$ P→]"; [set_solver|].
    iMod ("i'" with "[%]") as "[$ Q→]"; [set_solver|].
    iApply fupdw_mask_intro; [set_solver|]. iIntros "cl [P Q]".
    iMod "cl" as "_". iMod ("Q→" with "Q") as "_". iApply ("P→" with "P").
  Qed.
End inv_deriv.
Arguments InvDeriv PROP Σ {_ _ _} JUDG {_ _}.
Hint Mode InvDeriv ! - - - - - - - : typeclass_instances.
