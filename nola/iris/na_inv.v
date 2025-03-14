(** * Non-atomic invariants *)

From nola.iris Require Export inv cif.
From iris.base_logic.lib Require Export na_invariants.
From iris.algebra Require Import gset coPset.
From iris.proofmode Require Import proofmode.
Import iPropAppNotation ModwNotation DsemNotation.

Implicit Type (FML : oFunctor) (p : na_inv_pool_name) (i : positive).

Section na_inv.
  Context `{!inv'GS (cifOF CON) Σ, !invGS_gen hlc Σ, !na_invG Σ,
    !Csem CON JUDG Σ}.
  Local Existing Instance na_inv_inG.
  Implicit Type (Px : cif CON Σ) (δ : JUDG -n> iProp Σ).

  (** Access lock of an non-atomic invariant *)
  Local Definition na_lock p i : iProp Σ := own p (ε, GSet {[i]}).

  (** Allocate [na_lock] *)
  Local Lemma na_lock_alloc p N : ⊢ |==> ∃ i, ⌜i ∈ (↑N:coPset)⌝ ∧ na_lock p i.
  Proof.
    iMod (own_unit (prodUR coPset_disjUR (gset_disjUR positive)) p) as "ε".
    iMod (own_updateP with "ε") as ([m1 m2]) "[%cond l]".
    { apply prod_updateP'.
      - apply cmra_updateP_id, (reflexivity (R:=eq)).
      - apply (gset_disj_alloc_empty_updateP_strong' (.∈ (↑N:coPset)))=> ?.
        apply fresh_inv_name. }
    move: cond=>/=[<-[i[->?]]]. iModIntro. iExists i. by iSplit.
  Qed.

  (** Access [na_own] *)
  Lemma na_own_subset {p E F} : F ⊆ E →
    na_own p E ⊣⊢ na_own p F ∗ na_own p (E∖F).
  Proof.
    move=> ?. rewrite {1}(union_difference_L F E); [|done].
    by rewrite na_own_union; [|set_solver].
  Qed.
  Lemma na_own_in {p i E} : i ∈ E →
    na_own p E ⊣⊢ na_own p {[i]} ∗ na_own p (E∖{[i]}).
  Proof. move=> ?. apply na_own_subset. set_solver. Qed.

  (** [na_lock] is exclusive *)
  Local Lemma na_lock_2_no {p i} : na_lock p i -∗ na_lock p i -∗ False.
  Proof.
    iIntros "l l'". iCombine "l l'" gives %[_ Hval%gset_disj_valid_op].
    set_solver.
  Qed.

  (** What to be put in a non-atomic invariant *)
  Local Definition na_body p i P : iProp Σ :=
    P ∗ ▷ na_lock p i ∨ ▷ na_own p {[i]}.
  Local Definition cif_na_body p i Px : cif CON Σ :=
    as_cif (λ δ, na_body p i ⟦ Px ⟧(δ)).

  (** Token for a non-atomic invariant *)
  Local Definition na_inv_tok_def p N Px : iProp Σ :=
    ∃ i, ⌜i ∈ (↑N:coPset)⌝ ∧ inv_tok N (cif_na_body p i Px).
  Local Lemma na_inv_tok_aux : seal na_inv_tok_def. Proof. by eexists. Qed.
  Definition na_inv_tok := na_inv_tok_aux.(unseal).
  Local Lemma na_inv_tok_unseal : na_inv_tok = na_inv_tok_def.
  Proof. exact: seal_eq. Qed.

  (** [na_inv_tok] is non-expansive *)
  #[export] Instance na_inv_tok_ne {p N} : NonExpansive (na_inv_tok p N).
  Proof.
    rewrite na_inv_tok_unseal /na_inv_tok_def /cif_na_body /=. solve_proper.
  Qed.
  #[export] Instance na_inv_tok_proper {p N} :
    Proper ((≡) ==> (⊣⊢)) (na_inv_tok p N).
  Proof. apply ne_proper, _. Qed.
  (** [na_inv_tok] is persistent *)
  #[export] Instance na_inv_tok_persistent {p N Px} :
    Persistent (na_inv_tok p N Px).
  Proof. rewrite na_inv_tok_unseal. exact _. Qed.

  (** Weaken the namespace of [na_inv_tok] *)
  Lemma na_inv_tok_subset {p N N' Px} : ↑N ⊆@{coPset} ↑N' →
    na_inv_tok p N Px ⊢ na_inv_tok p N' Px.
  Proof.
    rewrite na_inv_tok_unseal=> ?. iIntros "[%[% i]]".
    rewrite inv_tok_subset //. iFrame. iPureIntro. set_solver.
  Qed.

  (** Allocate [na_inv_tok] suspending the world satisfaction *)
  Lemma na_inv_tok_alloc_suspend {δ} Px p N :
    inv_wsat ⟦⟧(δ) ==∗ na_inv_tok p N Px ∗ (⟦Px⟧(δ) -∗ inv_wsat ⟦⟧(δ)).
  Proof.
    rewrite na_inv_tok_unseal. iIntros "I".
    iMod (na_lock_alloc p N) as (i ?) "l".
    iMod (inv_tok_alloc_suspend with "I") as "[$ →W]"=>/=. iModIntro.
    iSplit; [done|]. iIntros "Px". iApply "→W". iLeft. iFrame.
  Qed.
  (** Allocate [na_inv_tok] *)
  Lemma na_inv_tok_alloc {δ} Px p N :
    ⟦ Px ⟧(δ) =[inv_wsat ⟦⟧(δ)]=∗ na_inv_tok p N Px.
  Proof.
    iIntros "? W". iMod (na_inv_tok_alloc_suspend with "W") as "[$ →W]".
    iModIntro. by iApply "→W".
  Qed.

  (** Allocate [inv_tok] before storing the content *)
  Lemma na_inv_tok_alloc_open {δ p N E F Px} : ↑N ⊆ E → ↑N ⊆ F →
    na_own p F =[inv_wsat ⟦⟧(δ)]{E}=∗
      na_own p (F∖↑N) ∗ na_inv_tok p N Px ∗
      (na_own p (F∖↑N) -∗ ⟦ Px ⟧(δ) =[inv_wsat ⟦⟧(δ)]{E}=∗ na_own p F).
  Proof.
    rewrite na_inv_tok_unseal=> NE NF. iMod (na_lock_alloc p N) as (i iN) "l".
    rewrite (na_own_subset NF) (na_own_in iN). iIntros "[[i $]$] W".
    iMod (inv_tok_alloc_open (FML:=cifOF _) (cif_na_body p i Px) N NE with "W")
      as "[W[inv cl]]".
    iMod ("cl" with "[$i//] W") as "[$ _]". iModIntro.
    iSplit; [iExists _; by iFrame|]. iIntros "$ Px W".
    iMod (inv_tok_acc NE with "inv W") as "/=[W[[[_ >l']|>$]cl]]".
    { iDestruct (na_lock_2_no with "l l'") as %[]. }
    iMod ("cl" with "[l Px] W") as "[$ _]"; [|done]. iLeft. iFrame.
  Qed.

  (** Access [Px] from [na_body] *)
  Local Lemma na_body_acc {p i N P} : i ∈ (↑N:coPset) →
    na_own p (↑N) -∗ na_body p i P -∗ ◇
      (na_body p i P ∗ P ∗
        (na_body p i P -∗ P -∗ ◇ (na_own p (↑N) ∗ na_body p i P))).
  Proof.
    move=> iN. rewrite (na_own_in iN). iIntros "[i $][[$ >l]|>i']"; last first.
    { iDestruct (na_own_disjoint with "i i'") as %?. set_solver. }
    iSplitL "i"; [by iRight|]. iIntros "!> [[_ >l']|>$] P !>".
    { iDestruct (na_lock_2_no with "l l'") as %[]. } { iLeft. iFrame. }
  Qed.

  (** Access via [na_inv_tok] *)
  Lemma na_inv_tok_acc {δ p N E F Px} : ↑N ⊆ E → ↑N ⊆ F →
    na_own p F -∗ na_inv_tok p N Px =[inv_wsat ⟦⟧(δ)]{E}=∗
      na_own p (F∖↑N) ∗ ⟦ Px ⟧(δ) ∗
      (na_own p (F∖↑N) -∗ ⟦ Px ⟧(δ) =[inv_wsat ⟦⟧(δ)]{E}=∗ na_own p F).
  Proof.
    rewrite na_inv_tok_unseal=> NE NF. rewrite (na_own_subset NF).
    iIntros "[N $] [%i[%iN #inv]] W".
    iMod (inv_tok_acc NE with "inv W") as "/=[W[bd cl]]".
    iMod (na_body_acc iN with "N bd") as "[bd[$ →bd]]".
    iMod ("cl" with "bd W") as "[$ _]". iIntros "!> F∖N Px W".
    iMod (inv_tok_acc NE with "inv W") as "[W[bd cl]]".
    iMod ("→bd" with "bd Px") as "[$ bd]".
    by iMod ("cl" with "bd W") as "[$ _]".
  Qed.
End na_inv.
