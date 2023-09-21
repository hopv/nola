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
Definition na_ilisti `{!nintpGS Σ} d p N Φ l : iProp Σ :=
  na_nninv d p N (Φ l) ∗ na_nninv d p N (na_ilisttl p N Φ l).
Notation na_ilistis := (na_ilisti nderiv).

Section verify.
  Context `{!nintpGS Σ}.

  (** [na_ilist] is interpreted into [na_ilisti] *)
  Fact na_ilist_ilisti {κ p N Φ l d} :
    ⟦ na_ilist p N Φ l ⟧{κ}(d) ⊣⊢ na_ilisti d p N Φ l.
  Proof. by rewrite/= rew_eq_hwf /=. Qed.

  (** Convert the predicate of [na_ilisti] *)
  Lemma na_ilisti_convert `{!nderivy Σ ih d} {p N Φ Ψ l} :
    □ ⸨ ∀ l, (Φ l ={∅}=∗ Ψ l) ∗ (Ψ l ={∅}=∗ Φ l) ⸩(d) -∗
    na_ilisti d p N Φ l -∗ na_ilisti d p N Ψ l.
  Proof.
    move: d nderivy0 Φ Ψ l. apply (derivy_acc (λ _, ∀ Φ Ψ l, _ -∗ _)).
    move=> d ? Φ Ψ l. iIntros "#sΦ↔Ψ #[ihd itl]".
    iSplit; iApply na_nninv_convert; [|iApply "ihd"| |iApply "itl"]; iModIntro.
    { iApply derivy_map; [|done]=>/=. iIntros (d' sys' _) "Φ↔Ψ Φ".
      iDestruct ("Φ↔Ψ" $! _) as "[ΦΨ ΨΦ]". iMod ("ΦΨ" with "Φ") as "$".
      iIntros "!> Ψ". by iApply "ΨΦ". }
    iApply derivy_byintp=>/=. iIntros (d' sys' [IH _]) "_ #to _ (%l' & ↦ & i)".
    iModIntro. rewrite rew_eq_hwf /=. iDestruct "i" as "#i".
    iDestruct ("to" with "[//]") as "?". iSplitL.
    { iExists _. iFrame "↦". rewrite rew_eq_hwf /=. by iApply IH. }
    iIntros "(%l'' & ↦ & i') !>". iExists _. iFrame "↦".
    rewrite !rew_eq_hwf /=. iApply IH; [|done]. iModIntro.
    iApply (derivy_map (derivy0:=sys')); [|done]=>/=.
    iIntros (? _ _) "Φ↔'Ψ %". iApply bi.sep_comm. iApply "Φ↔'Ψ".
  Qed.

  (** [na_ilisti] by cons *)
  Lemma na_ilisti_cons `{!nderivy Σ ih d} {p N Φ l l'} :
    na_nninv d p N (Φ l) -∗ na_ilisti d p N Φ l' -∗ (l +ₗ 1) ↦ #l'
      =[nninv_wsat d]=∗ na_ilisti d p N Φ l.
  Proof.
    iIntros "$ #i ↦".
    iMod (na_nninv_alloc (na_ilisttl _ _ _ _) with "[↦]") as "$"; [|done].
    simpl. iExists _. iFrame "↦". by rewrite rew_eq_hwf /=.
  Qed.

  (** [na_ilisti] from a one-node loop *)
  Lemma na_ilisti_loop_1 `{!nderivy Σ ih d} {p N Φ l} :
    na_nninv d p N (Φ l) -∗ (l +ₗ 1) ↦ #l =[nninv_wsat d]=∗
      na_ilisti d p N Φ l.
  Proof.
    iIntros "#Φ ↦". iFrame "Φ".
    iMod (na_nninv_alloc_rec (na_ilisttl _ _ _ _) with "[↦]") as "$"; [|done].
    iIntros "/= #?". iExists _. rewrite rew_eq_hwf /=. by iFrame "↦ Φ".
  Qed.

  (** [na_ilisti] from a two-node loop *)
  Lemma na_ilisti_loop_2 `{!nderivy Σ ih d} {p N Φ l l'} :
    na_nninv d p N (Φ l) -∗ na_nninv d p N (Φ l') -∗
    (l +ₗ 1) ↦ #l' -∗ (l' +ₗ 1) ↦ #l =[nninv_wsat d]=∗
      na_ilisti d p N Φ l ∗ na_ilisti d p N Φ l'.
  Proof.
    iIntros "#Φ #Φ' ↦ ↦'". iFrame "Φ Φ'".
    iMod (na_nninv_alloc_rec (na_ilisttl _ _ _ _ ∗ na_ilisttl _ _ _ _)
      with "[↦ ↦']") as "inv"; last first.
    { simpl. by iDestruct (na_nninv_split with "inv") as "[$ $]". }
    iIntros "/= itls". iDestruct (na_nninv_split with "itls") as "[#? #?]".
    iSplitL "↦"; iExists _; rewrite rew_eq_hwf /=; iFrame; by iSplit.
  Qed.

  (** [siter] terminates under [na_ilistis] *)
  Lemma twp_siter_na {p N Φ E F l} {f : val} {c : nat} : ↑N ⊆ E → ↑N ⊆ F →
    na_ilistis p N Φ l -∗
    (∀ l, [[{ na_nninvd p N (Φ l) ∗ na_own p F }]][nninv_wsatd]
            f #l @ E
          [[{ RET #(); na_own p F }]]) -∗
    [[{ na_own p F }]][nninv_wsatd]
      siter f #c #l @ E
    [[{ RET #(); True }]].
  Proof.
    iIntros (??) "#[ihd itl] #f". iIntros (Ψ) "!> pF Ψ".
    iInduction c as [|c] "IH" forall (l) "ihd itl"; wp_rec; wp_pures;
      [by iApply "Ψ"|].
    wp_apply ("f" with "[$pF //]"). iIntros "pF". wp_pures. wp_bind (! _)%E.
    iMod (na_nninv_acc with "[//] pF") as "/=((%l' & ↦ & i) & pF∖N & cl)";
      [done..|].
    rewrite rew_eq_hwf /=. iDestruct "i" as "#[??]". wp_load. wp_pures.
    iMod ("cl" with "[↦] pF∖N") as "pF".
    { iExists _. iFrame "↦". rewrite/= rew_eq_hwf /=. by iSplit. }
    have ->: (S c - 1)%Z = c by lia. by iApply ("IH" with "pF Ψ").
  Qed.

  (** [siter_nd] terminates under [na_ilistis] *)
  Lemma twp_siter_nd_na {p N Φ E F l} {f : val} : ↑N ⊆ E → ↑N ⊆ F →
    na_ilistis p N Φ l -∗
    (∀ l, [[{ na_nninvd p N (Φ l) ∗ na_own p F }]][nninv_wsatd]
            f #l @ E
          [[{ RET #(); na_own p F }]]) -∗
    [[{ na_own p F }]][nninv_wsatd]
      siter_nd f #l @ E
    [[{ RET #(); True }]].
  Proof.
    iIntros (??) "#? #?". iIntros (?) "!> pF ?". wp_lam. wp_pures.
    wp_apply twp_ndnat; [done|]. iIntros (?) "_".
    by wp_apply (twp_siter_na with "[] [] pF").
  Qed.

  (** Introduce a Hoare triple with [na_nninvd] *)
  Lemma twp_na_nninvd {p N Φ E F l} {f : val} : ↑N ⊆ E → ↑N ⊆ F →
    [[{ ⟦ Φ l ⟧ }]][nninv_wsatd] f #l @ E [[{ RET #(); ⟦ Φ l ⟧ }]] -∗
    [[{ na_nninvd p N (Φ l) ∗ na_own p F }]][nninv_wsatd]
      f #l @ E
    [[{ RET #(); na_own p F }]].
  Proof.
    iIntros (??) "#f". iIntros (Ψ) "!> [#? pF] Ψ". iApply twpw_fupdw_nonval=>//.
    iMod (na_nninv_acc with "[] pF") as "/=(Φ & pF∖N & cl)"; [done..|].
    wp_apply ("f" with "Φ"). iIntros "Φ". iMod ("cl" with "Φ pF∖N") as "?".
    iModIntro. by iApply "Ψ".
  Qed.
End verify.
