(** * Verification on non-atomic shared mutable singly linked infinite lists *)

From nola.examples.logic Require Export na_inv verify.ilist_base.
From nola.iris Require Export wp.
From nola.examples.heap_lang Require Export proofmode notation.

(** Infinite list whose elements satisfy the condition [Φ] *)
Definition na_ilist {κ Γᵘ Γᵍ} (p : na_inv_pool_name) (N : namespace)
  (Φ : loc → nPropL (;ᵞ Γᵘ ++ Γᵍ)) : loc → nProp κ (Γᵘ;ᵞ Γᵍ) :=
  (rec:ˢ l, n_na_inv' (_::_) p N (¢ᵍ Φ l) ∗
    n_na_inv' (_::_) p N (∃ l' : loc, (l +ₗ 1) ↦ # l' ∗ %ᵍˢ 0@ l'))%n.

(** Substitution over [na_ilist] *)
Fact na_ilist_nsubst {κ p N V Φ Ψ l} :
  na_ilist (κ:=κ) (Γᵘ:=[V]) p N Φ l /: Ψ =
    na_ilist (Γᵘ:=[]) p N (λ l, Φ l /:ᵍ Ψ) l.
Proof. done. Qed.

(** Interpreted [ilist] *)
Definition na_ilisttl {κ} p N (Φ : _ → _ (;ᵞ)) l : nProp κ (;ᵞ) :=
  ∃ l' : loc, (l +ₗ 1) ↦ # l' ∗ na_ilist (Γᵘ:=[]) p N Φ l'.
Definition na_ilisti `{!nintpGS Σ} δ p N Φ l : iProp Σ :=
  na_ninv δ p N (Φ l) ∗ na_ninv δ p N (na_ilisttl p N Φ l).
Notation na_ilistis := (na_ilisti nderiv).

Section verify.
  Context `{!nintpGS Σ}.

  (** [na_ilist] is interpreted into [na_ilisti] *)
  Fact na_ilist_ilisti {κ p N Φ l δ} :
    ⟦ na_ilist p N Φ l ⟧{κ}(δ) ⊣⊢ na_ilisti δ p N Φ l.
  Proof. by rewrite/= rew_eq_hwf /=. Qed.

  (** Convert the predicate of [na_ilisti] *)
  Lemma na_ilisti_convert `{!nDeriv ih δ} {p N Φ Ψ l} :
    □ ⸨ ∀ l, (Φ l ={∅}=∗ Ψ l) ∗ (Ψ l ={∅}=∗ Φ l) ⸩(δ) -∗
    na_ilisti δ p N Φ l -∗ na_ilisti δ p N Ψ l.
  Proof.
    move: δ nDeriv0 Φ Ψ l. apply (Deriv_acc (λ _, ∀ Φ Ψ l, _ -∗ _)).
    move=> δ ? Φ Ψ l. iIntros "#sΦ↔Ψ #[ihd itl]".
    iSplit; iApply na_ninv_convert; [|iApply "ihd"| |iApply "itl"]; iModIntro.
    { iApply Deriv_map; [|done]=>/=. iIntros (δ' sys' _) "Φ↔Ψ Φ".
      iDestruct ("Φ↔Ψ" $! _) as "[ΦΨ ΨΦ]". iMod ("ΦΨ" with "Φ") as "$".
      iIntros "!> Ψ". by iApply "ΨΦ". }
    iApply Deriv_byintp=>/=. iIntros (δ' sys' [IH _]) "_ #→ (%l' & ↦ & i)".
    iModIntro. rewrite rew_eq_hwf /=. iDestruct "i" as "#i".
    iDestruct ("→" with "[//]") as "?". iSplitL.
    { iExists _. iFrame "↦". rewrite rew_eq_hwf /=. by iApply IH. }
    iIntros "(%l'' & ↦ & i') !>". iExists _. iFrame "↦".
    rewrite !rew_eq_hwf /=. iApply IH; [|done]. iModIntro.
    iApply (Deriv_map (Deriv0:=sys')); [|done]=>/=.
    iIntros (? _ _) "Φ↔'Ψ %". iApply bi.sep_comm. iApply "Φ↔'Ψ".
  Qed.

  (** [na_ilisti] by cons *)
  Lemma na_ilisti_cons `{!nDeriv ih δ} {p N Φ l l'} :
    na_ninv δ p N (Φ l) -∗ na_ilisti δ p N Φ l' -∗ (l +ₗ 1) ↦ #l'
      =[na_inv_wsat' δ]=∗ na_ilisti δ p N Φ l.
  Proof.
    iIntros "$ #i ↦".
    iMod (na_ninv_alloc (na_ilisttl _ _ _ _) with "[↦]") as "$"; [|done].
    simpl. iExists _. iFrame "↦". by rewrite rew_eq_hwf /=.
  Qed.

  (** [na_ilisti] from a one-node loop *)
  Lemma na_ilisti_loop_1 `{!nDeriv ih δ} {p N Φ l} :
    na_ninv δ p N (Φ l) -∗ (l +ₗ 1) ↦ #l =[na_inv_wsat' δ]=∗
      na_ilisti δ p N Φ l.
  Proof.
    iIntros "#Φ ↦". iFrame "Φ".
    iMod (na_ninv_alloc_rec (na_ilisttl _ _ _ _) with "[↦]") as "$"; [|done].
    iIntros "/= #?". iExists _. rewrite rew_eq_hwf /=. by iFrame "↦ Φ".
  Qed.

  (** [na_ilisti] from a two-node loop *)
  Lemma na_ilisti_loop_2 `{!nDeriv ih δ} {p N Φ l l'} :
    na_ninv δ p N (Φ l) -∗ na_ninv δ p N (Φ l') -∗
    (l +ₗ 1) ↦ #l' -∗ (l' +ₗ 1) ↦ #l =[na_inv_wsat' δ]=∗
      na_ilisti δ p N Φ l ∗ na_ilisti δ p N Φ l'.
  Proof.
    iIntros "#Φ #Φ' ↦ ↦'". iFrame "Φ Φ'".
    iMod (na_ninv_alloc_rec (na_ilisttl _ _ _ _ ∗ na_ilisttl _ _ _ _)
      with "[↦ ↦']") as "inv"; last first.
    { simpl. by iDestruct (na_ninv_split with "inv") as "[$ $]". }
    iIntros "/= itls". iDestruct (na_ninv_split with "itls") as "[#? #?]".
    iSplitL "↦"; iExists _; rewrite rew_eq_hwf /=; iFrame; by iSplit.
  Qed.

  (** [siter] terminates under [na_ilistis] *)
  Lemma twp_siter_na {p N Φ E F ln l} {f : val} {n : nat} : ↑N ⊆ E → ↑N ⊆ F →
    (∀ l, [[{ na_ninvd p N (Φ l) ∗ na_own p F }]][na_inv_wsatd]
            f #l @ E
          [[{ RET #(); na_own p F }]]) -∗
    [[{ ln ↦ #n ∗ na_ilistis p N Φ l ∗ na_own p F }]][na_inv_wsatd]
      siter f #ln #l @ E
    [[{ RET #(); ln ↦ #0 ∗ na_own p F }]].
  Proof.
    iIntros (??) "#f". iIntros (Ψ) "!> (↦n & #[ihd itl] & pF) Ψ".
    iInduction n as [|n] "IH" forall (l) "ihd itl"; wp_rec; wp_pures; wp_load;
      wp_pures. { iModIntro. iApply "Ψ". iFrame. }
    wp_apply ("f" with "[$pF //]"). iIntros "pF". wp_pures. wp_load. wp_op.
    have -> : (S n - 1)%Z = n by lia. wp_store. wp_op. wp_bind (! _)%E.
    iMod (na_ninv_acc with "pF itl") as "/=[pF∖N[[%l'[↦ i]] cl]]";
      [done..|].
    rewrite rew_eq_hwf /=. iDestruct "i" as "#[??]". wp_load. wp_pures.
    iMod ("cl" with "pF∖N [↦]") as "pF".
    { iExists _. iFrame "↦". rewrite/= rew_eq_hwf /=. by iSplit. }
    by iApply ("IH" with "↦n pF Ψ").
  Qed.

  (** [siter_nd] terminates under [na_ilistis] *)
  Lemma twp_siter_nd_na {p N Φ E F l} {f : val} : ↑N ⊆ E → ↑N ⊆ F →
    (∀ l, [[{ na_ninvd p N (Φ l) ∗ na_own p F }]][na_inv_wsatd]
            f #l @ E
          [[{ RET #(); na_own p F }]]) -∗
    [[{ na_ilistis p N Φ l ∗ na_own p F }]][na_inv_wsatd]
      siter_nd f #l @ E
    [[{ RET #(); True }]].
  Proof.
    iIntros (??) "#?". iIntros (Ψ) "!> ipF Ψ". wp_lam. wp_pures.
    wp_apply twp_ndnat; [done|]. iIntros (?) "_". wp_alloc ln as "↦n". wp_pures.
    wp_apply (twp_siter_na with "[] [$↦n $ipF]")=>//. iIntros. by iApply "Ψ".
  Qed.

  (** Introduce a Hoare triple with [na_ninvd] *)
  Lemma twp_na_ninvd {p N Φ E F l} {f : val} : ↑N ⊆ E → ↑N ⊆ F →
    [[{ ⟦ Φ l ⟧ }]][na_inv_wsatd] f #l @ E [[{ RET #(); ⟦ Φ l ⟧ }]] -∗
    [[{ na_ninvd p N (Φ l) ∗ na_own p F }]][na_inv_wsatd]
      f #l @ E
    [[{ RET #(); na_own p F }]].
  Proof.
    iIntros (??) "#f". iIntros (Ψ) "!> [#? pF] Ψ". iApply twpw_fupdw_nonval=>//.
    iMod (na_ninv_acc with "pF []") as "/=[pF∖N[Φ cl]]"; [done..|].
    wp_apply ("f" with "Φ"). iIntros "Φ". iMod ("cl" with "pF∖N Φ") as "?".
    iModIntro. by iApply "Ψ".
  Qed.
End verify.
