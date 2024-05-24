(** * Relaxed [inv] with [der] *)

From nola.bi Require Export deriv.
From nola.iris Require Export inv.
From iris.proofmode Require Import proofmode.
Import iPropAppNotation PintpNotation IntpNotation UpdwNotation.

(** Notation *)
Notation inv_wsati δ := (inv_wsat ⟦⟧(δ)).
Notation inv_wsatid := (inv_wsati der).

(** Derivability pre-data for [inv] *)
Class InvPreDeriv (PRO JUDG : ofe) := INV_PRE_DERIV {
  inv_jacsr : namespace → PRO → JUDG;
  inv_jacsr_ne {N} :: NonExpansive (inv_jacsr N);
}.
Hint Mode InvPreDeriv ! - : typeclass_instances.
Arguments INV_PRE_DERIV {_ _} _ {_}.

Section inv_deriv.
  Context `{!InvPreDeriv PRO JUDG} {Σ : gFunctors}.
  Implicit Type δ : JUDG → iProp Σ.

  (** [inv']: Relaxed invariant *)
  Local Definition inv'_def δ N (P : PRO) : iProp Σ := □ δ (inv_jacsr N P).
  Local Lemma inv'_aux : seal inv'_def. Proof. by eexists. Qed.
  Definition inv' := inv'_aux.(unseal).
  Local Lemma inv'_unseal : inv' = inv'_def. Proof. exact: seal_eq. Qed.

  (** [inv'] is persistent *)
  #[export] Instance inv'_persistent {δ N P} : Persistent (inv' δ N P).
  Proof. rewrite inv'_unseal. exact _. Qed.

  (** [inv'] is non-expansive *)
  #[export] Instance inv'_ne `{!NonExpansive δ} {N} : NonExpansive (inv' δ N).
  Proof. rewrite inv'_unseal. solve_proper. Qed.
End inv_deriv.
Notation invd := (inv' der).

Section inv_deriv.
  Context `{!inv'GS PROP Σ, !invGS_gen hlc Σ}.
  Implicit Type P Q PQ : PROP $oi Σ.

  (** Accessor *)
  Definition inv_acsr ip N Pi : iProp Σ :=
    ∀ E, ⌜↑N ⊆ E⌝ → |=[inv_wsat ip]{E,E∖↑N}=>
      Pi ∗ (Pi =[inv_wsat ip]{E∖↑N,E}=∗ True).

  Context `{!InvPreDeriv (PROP $oi Σ) (JUDGI : judgi (iProp Σ)),
    !Dintp JUDGI (PROP $oi Σ) (iProp Σ)}.
  Implicit Type δ : JUDGI → iProp Σ.

  (** Derivability data for [inv] *)
  Class InvDeriv :=
    inv_jacsr_intp : ∀{δ N P}, ⟦ inv_jacsr N P ⟧(δ) ≡ inv_acsr ⟦⟧(δ) N ⟦ P ⟧(δ).

  Context `{!InvDeriv}.

  (** Access [inv'] *)
  Lemma invd_acc {N P E} : ↑N ⊆ E →
    invd N P =[inv_wsatid]{E,E∖↑N}=∗
      ⟦ P ⟧ ∗ (⟦ P ⟧ =[inv_wsatid]{E∖↑N,E}=∗ True).
  Proof.
    rewrite inv'_unseal. iIntros (?) "accP".
    iDestruct (der_sound with "accP") as "accP". rewrite inv_jacsr_intp.
    by iApply "accP".
  Qed.

  Context `{!Deriv (JUDGI:=JUDGI) ih δ}.

  (** Turn [inv_acsr] into [inv'] *)
  Lemma inv_acsr_inv' {N P} :
    □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      inv_acsr ⟦⟧(δ') N ⟦ P ⟧(δ')) ⊢ inv' δ N P.
  Proof.
    rewrite inv'_unseal. iIntros "#big !>". iApply Deriv_to. iIntros (????).
    rewrite inv_jacsr_intp. by iApply "big".
  Qed.

  (** Turn [inv_tok] into [inv'] *)
  Lemma inv_tok_inv' {N P} : inv_tok N P ⊢ inv' δ N P.
  Proof.
    rewrite -inv_acsr_inv'. iIntros "#i !>" (δ' ?????).
    by iApply (inv_tok_acc (ip:=⟦⟧(δ')) with "i").
  Qed.

  (** Allocate [inv'] *)
  Lemma inv'_alloc_rec P N :
    (inv' δ N P -∗ ⟦ P ⟧(δ)) =[inv_wsati δ]=∗ inv' δ N P.
  Proof. rewrite -inv_tok_inv'. exact: inv_tok_alloc_rec. Qed.
  Lemma inv'_alloc P N : ⟦ P ⟧(δ) =[inv_wsati δ]=∗ inv' δ N P.
  Proof. rewrite -inv_tok_inv'. exact: inv_tok_alloc. Qed.
  Lemma inv'_alloc_open P N E : ↑N ⊆ E →
    ⊢ |=[inv_wsati δ]{E, E∖↑N}=> inv' δ N P ∗
      (⟦ P ⟧(δ) =[inv_wsati δ]{E∖↑N, E}=∗ True).
  Proof. rewrite -inv_tok_inv'. exact: inv_tok_alloc_open. Qed.

  (** Convert [inv'] with [acsr] *)
  Lemma inv'_acsr {N P Q} :
    □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      acsr (fupd ∅ ∅) ⟦ P ⟧(δ') ⟦ Q ⟧(δ')) -∗
      inv' δ N P -∗ inv' δ N Q.
  Proof.
    rewrite inv'_unseal. iIntros "#PQP #accP !>". iApply Deriv_to.
    iIntros (??? to). rewrite to !inv_jacsr_intp. iIntros (? NE).
    iMod ("accP" $! _ NE) as "[P cl]".
    iMod (fupd_mask_subseteq ∅) as "→E∖N"; [set_solver|].
    iMod ("PQP" with "[//] [//] [//] P") as "($& QP)". iMod "→E∖N" as "_".
    iIntros "!> Q". iMod (fupd_mask_subseteq ∅) as "→E∖N"; [set_solver|].
    iMod ("QP" with "Q") as "P". iMod "→E∖N" as "_". iApply ("cl" with "P").
  Qed.

  (** Split [inv'] over [∗] *)
  Local Lemma inv'_sep' {N PQ P Q} :
    (∀ δ', ⟦ PQ ⟧(δ') ≡ (⟦ P ⟧(δ') ∗ ⟦ Q ⟧(δ'))%I) → inv' δ N PQ ⊢ inv' δ N P.
  Proof.
    iIntros (eq). iApply (inv'_acsr with "[]"). iIntros "!>" (????).
    unfold acsr. rewrite eq. iApply (acsr_sep_l (M:=fupd _ _)).
  Qed.
  Lemma inv'_sep {N PQ P Q} : (∀ δ', ⟦ PQ ⟧(δ') ≡ (⟦ P ⟧(δ') ∗ ⟦ Q ⟧(δ'))%I) →
    inv' δ N PQ ⊢ inv' δ N P ∗ inv' δ N Q.
  Proof.
    iIntros (eq) "#i". iSplit; [by iApply inv'_sep'|].
    iApply (inv'_sep' with "i"). iIntros (?). by rewrite eq comm.
  Qed.

  (** Merge [inv']s with [∗] *)
  Lemma inv'_merge {N1 N2 N P Q PQ} : N1 ## N2 → ↑N1 ∪ ↑N2 ⊆@{coPset} ↑N →
    (∀ δ', ⟦ PQ ⟧(δ') ≡ (⟦ P ⟧(δ') ∗ ⟦ Q ⟧(δ'))%I) →
    inv' δ N1 P -∗ inv' δ N2 Q -∗ inv' δ N PQ.
  Proof.
    rewrite inv'_unseal. iIntros (?? eq) "#i #i' !>".
    iApply (Deriv_map2 with "[] i i'"). iIntros (????) "{i}i {i'}i'".
    rewrite !inv_jacsr_intp. iIntros (??). rewrite eq.
    iMod ("i" with "[%]") as "[$ P→]"; [set_solver|].
    iMod ("i'" with "[%]") as "[$ Q→]"; [set_solver|].
    iApply fupdw_mask_intro; [set_solver|]. iIntros "cl [P Q]".
    iMod "cl" as "_". iMod ("Q→" with "Q") as "_". iApply ("P→" with "P").
  Qed.
End inv_deriv.
Arguments InvDeriv PROP Σ {_ _ _} JUDGI {_ _}.
Hint Mode InvDeriv ! - - - - - - - : typeclass_instances.
