(** * Expression rules for references *)

From nola.examples.type Require Export deriv.
From nola.examples.heap_lang Require Export proofmode.

Section eref.
  Context `{!tintpGS L Σ}.

  (** Allocate [ref[ ]] *)
  Lemma ninv_tref `{!tderivy Σ ih d, ! i <ⁿ L} {l T} :
    ninv trefN (tinvd_ref l T) ⊢ tref d (i:=i) l T.
  Proof.
    iIntros "#inv !>". iApply (derivy_intro (d:=d))=>/=. iIntros (???).
    iMod (ninv_acc with "inv") as "/=[(%& ↦ & T) cl]"; [done|].
    iModIntro. iExists _. iFrame "↦ T". iIntros (?) "↦ T".
    iApply fupdw_incl; [apply wsat_incl_tinv_tninv|]. iApply "cl". iExists _.
    iFrame.
  Qed.
  Lemma texpr_ref_ref `{! i <ⁿ j} {e k T} :
    e :ᵉ(j) T ⊢ ref e :ᵉ{k}(j) ref{i,nil}: T.
  Proof.
    iIntros "?". unfold texpr. wp_bind e. iApply (twp_wand with "[$]").
    iIntros (?) ">#?". wp_alloc l as "↦". iModIntro. iApply fupdw_tinv_wsat_le.
    iIntros (?). have ?: i <ⁿ L by apply (nlt_nle_trans _ _).
    iApply fupdw_incl; [apply (wsat_incl_tinv_tninv (M:=j))|].
    iMod (ninv_alloc (P:=tinvd_ref l T) with "[↦]") as "?";
      [iExists _; by iFrame|].
    iModIntro=>/=. iExists _. iSplit; [done|]. iApply ninv_tref.
    by rewrite Loc.add_0.
  Qed.

  (** Offset on [ref[ ]] *)
  Lemma texpr_ref_off' `{! i <ⁿ j} {e o k T} {o' : Z} :
    e :ᵉ{k}(j) ref{i,_}[o] T ⊢ e +ₗ #o' :ᵉ{k}(j) ref{i,_}[o - o'] T.
  Proof.
    iIntros "?". unfold texpr. wp_bind e. iApply (twp_wand with "[$]").
    iIntros (?) "/= >(%&->& ref)". wp_pure. do 2 iModIntro. iExists _.
    iSplit; [done|]. iStopProof. rewrite Loc.add_assoc. do 2 f_equiv. lia.
  Qed.
  Lemma texpr_ref_off `{! i <ⁿ j} {e o k T} :
    e :ᵉ{k}(j) ref{i,_}[o] T ⊢ e +ₗ #o :ᵉ{k}(j) ref{i,_}: T.
  Proof.
    rewrite texpr_ref_off'. unfold texpr. do 3 f_equiv. by rewrite Z.sub_diag.
  Qed.

  (** Load from [ref[ ]] *)
  Lemma texpr_ref_load `{! i <ⁿ j} {e k} {T : _ i (;ᵞ)} :
    e :ᵉ{k}(j) ref: T ⊢ ! e :ᵉ(j) T.
  Proof.
    iIntros "?". unfold texpr. wp_bind e. iApply (twp_wand with "[$]").
    iIntros (?) "/= >(%&->& ref)". rewrite Loc.add_0.
    iApply (twpw_atomic (e:=! _)); [done|]. iApply fupdw_tinv_wsat_le.
    iIntros (?). have ? : i <ⁿ L by exact (nlt_nle_trans _ _).
    iDestruct tderiv_sound as "→". have ? : S i ≤ⁿ j by done.
    iMod ("→" with "ref") as (?) "(↦ & #T & cl)". iModIntro. wp_load.
    iModIntro. by iMod ("cl" with "↦ T") as "_".
  Qed.

  (** Store to [ref[ ]] *)
  Lemma texpr_ref_store `{! i <ⁿ j} {e e' k} {T : _ i (;ᵞ)} :
    e :ᵉ{k}(j) ref: T -∗ e' :ᵉ(j) T -∗ (e <- e') :ᵉ{0}(j) 𝟙.
  Proof.
    iIntros "??". unfold texpr. wp_bind e'. iApply (twp_wand with "[$]").
    iIntros (?) "/= >#T". wp_bind e. iApply (twp_wand with "[$]").
    iIntros (?) "/= >(%&->& ref)". rewrite Loc.add_0.
    iApply (twpw_atomic (e:=_ <- _)); [done|]. iApply fupdw_tinv_wsat_le.
    iIntros (?). have ? : i <ⁿ L by exact (nlt_nle_trans _ _).
    iDestruct tderiv_sound as "→". have ? : S i ≤ⁿ j by done.
    iMod ("→" with "ref") as (?) "(↦ &_& cl)". iModIntro. wp_store.
    iModIntro. by iMod ("cl" with "↦ T") as "_".
  Qed.

  (** Exchange on [ref[ ]] *)
  Lemma texpr_ref_xchg `{! i <ⁿ j} {e e' k} {T : _ i (;ᵞ)} :
    e :ᵉ{k}(j) ref: T -∗ e' :ᵉ(j) T -∗ Xchg e e' :ᵉ(j) T.
  Proof.
    iIntros "??". unfold texpr. wp_bind e'. iApply (twp_wand with "[$]").
    iIntros (?) "/= >#T". wp_bind e. iApply (twp_wand with "[$]").
    iIntros (?) "/= >(%&->& ref)". rewrite Loc.add_0.
    iApply (twpw_atomic (e:=Xchg _ _)); [done|]. iApply fupdw_tinv_wsat_le.
    iIntros (?). have ? : i <ⁿ L by exact (nlt_nle_trans _ _).
    iDestruct tderiv_sound as "→". have ? : S i ≤ⁿ j by done.
    iMod ("→" with "ref") as (?) "(↦ & ? & cl)". iModIntro. wp_xchg.
    iModIntro. iMod ("cl" with "↦ T") as "_". by iFrame.
  Qed.

  (** Compare-exchange on [ref[ ]] *)
  Lemma texpr_ref_cmpxchg `{! i <ⁿ j} {e e' e'' k} :
    e :ᵉ{k}(j) ref{i,_}: ℕ -∗ e' :ᵉ{0}(j) ℕ -∗ e'' :ᵉ{0}(j) ℕ -∗
    CmpXchg e e' e'' :ᵉ{0}(j) ℕ × 𝔹.
  Proof.
    iIntros "???". unfold texpr. wp_bind e''. iApply (twp_wand with "[$]").
    iIntros (?) ">[%n ->]". wp_bind e'. iApply (twp_wand with "[$]").
    iIntros (?) ">[%m ->]". wp_bind e. iApply (twp_wand with "[$]").
    iIntros (?) "/= >(%&->& ref)". rewrite Loc.add_0.
    iApply (twpw_atomic (e:=CmpXchg _ _ _)); [done|]. iApply fupdw_tinv_wsat_le.
    iIntros (?). have ? : i <ⁿ L by exact (nlt_nle_trans _ _).
    iDestruct tderiv_sound as "→". have ? : S i ≤ⁿ j by done.
    iMod ("→" with "ref") as (?) "(↦ &[%m' ->]& cl)". iModIntro.
    case (decide (m' = m)%Z)=> [->|?];
      [wp_apply (twp_cmpxchg_suc with "↦"); [done|solve_vals_compare_safe|]|
        wp_apply (twp_cmpxchg_fail with "↦");
          [case; lia|solve_vals_compare_safe|]];
      iIntros "↦";  iMod ("cl" with "↦ []") as "_"; try (by iExists _);
      iPureIntro; eexists _, _; split=>//; split; by eexists.
  Qed.

  (** Fetch-and-add on [ref[ ]] *)
  Lemma texpr_ref_faa `{! i <ⁿ j} {e e' k} :
    e :ᵉ{k}(j) ref{i,_}: ℕ -∗ e' :ᵉ{0}(j) ℕ -∗ FAA e e' :ᵉ{0}(j) ℕ.
  Proof.
    iIntros "??". unfold texpr. wp_bind e'. iApply (twp_wand with "[$]").
    iIntros (?) ">[%->]". wp_bind e. iApply (twp_wand with "[$]").
    iIntros (?) "/= >(%&->& ref)". rewrite Loc.add_0.
    iApply (twpw_atomic (e:=FAA _ _)); [done|]. iApply fupdw_tinv_wsat_le.
    iIntros (?). have ? : i <ⁿ L by exact (nlt_nle_trans _ _).
    iDestruct tderiv_sound as "→". have ? : S i ≤ⁿ j by done.
    iMod ("→" with "ref") as (?) "(↦ &(%m &->)& cl)". iModIntro. wp_faa.
    iModIntro. rewrite -Nat2Z.inj_add.
    iMod ("cl" with "↦ []") as "_"; [|do 2 iModIntro]; by iExists _.
  Qed.
End eref.
