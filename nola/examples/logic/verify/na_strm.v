(** * Verification on non-atomic shared mutable singly linked streams *)

From nola.examples.logic Require Export na_inv verify.strm_base.
From nola.iris Require Export wp.
From nola.examples.heap_lang Require Export proofmode notation.

(** Stream whose elements satisfy the condition [Φ] *)
Definition na_strm {κ Γᵘ Γᵍ} (p : na_inv_pool_name) (N N' : namespace)
  (Φ : loc → nPropL (;ᵞ Γᵘ ++ Γᵍ)) : loc → nProp κ (Γᵘ;ᵞ Γᵍ) :=
  (rec:ˢ l, n_na_inv' (_::_) 0 p N (¢ᵍ Φ l) ∗
    n_na_inv' (_::_) 0 p N' (∃ l' : loc, (l +ₗ 1) ↦ # l' ∗ %ᵍˢ 0@ l'))%n.

(** Substitution over [na_strm] *)
Fact na_strm_nsubst {κ p N N' V Φ Ψ l} :
  na_strm (κ:=κ) (Γᵘ:=[V]) p N N' Φ l /: Ψ =
    na_strm (Γᵘ:=[]) p N N' (λ l, Φ l /:ᵍ Ψ) l.
Proof. done. Qed.

(** Interpreted [strm] *)
Definition na_strmtl {κ} p N N' (Φ : _ → _ (;ᵞ)) l : nProp κ (;ᵞ) :=
  ∃ l' : loc, (l +ₗ 1) ↦ # l' ∗ na_strm (Γᵘ:=[]) p N N' Φ l'.
Definition na_strmi `{!nintpGS Σ} d p N N' Φ l : iProp Σ :=
  na_nninv d 0 p N (Φ l) ∗ na_nninv d 0 p N' (na_strmtl p N N' Φ l).
Notation na_strmis := (na_strmi nderiv).

Section verify.
  Context `{!nintpGS Σ}.

  (** [na_strm] is interpreted into [na_strmi] *)
  Fact na_strm_strmi {κ p N N' Φ l d} :
    ⟦ na_strm p N N' Φ l ⟧{κ}(d) ⊣⊢ na_strmi d p N N' Φ l.
  Proof. by rewrite/= rew_eq_hwf /=. Qed.

  (** Convert the predicate of [na_strmi] *)
  Lemma na_strmi_convert `{!nderivy Σ ih d} {p N N' Φ Ψ l} :
    □ ⸨ ∀ l, (Φ l ={∅}=∗ Ψ l) ∗ (Ψ l ={∅}=∗ Φ l) ⸩(d, 0) -∗
    na_strmi d p N N' Φ l -∗ na_strmi d p N N' Ψ l.
  Proof.
    move: d nderivy0 Φ Ψ l. apply (derivy_acc (λ _, ∀ Φ Ψ l, _ -∗ _)).
    move=> d ? Φ Ψ l. iIntros "#sΦ↔Ψ #[??]".
    iSplit; iApply na_nninv_convert=>//; iModIntro.
    { iApply derivy_map; [|done]=>/=. iIntros (d' sys' _) "Φ↔Ψ Φ".
      iDestruct ("Φ↔Ψ" $! _) as "[ΦΨ ΨΦ]". iMod ("ΦΨ" with "Φ") as "$".
      iIntros "!> Ψ". by iApply "ΨΦ". }
    iApply derivy_byintp=>/=. iIntros (d' sys' [IH _]) "_ #to _ (%l' & ↦ & s)".
    iModIntro. rewrite rew_eq_hwf /=. iDestruct "s" as "#s".
    iDestruct ("to" with "[//]") as "?". iSplitL.
    { iExists _. iFrame "↦". rewrite rew_eq_hwf /=. by iApply IH. }
    iIntros "(%l'' & ↦ & s') !>". iExists _. iFrame "↦".
    rewrite !rew_eq_hwf /=. iApply IH; [|done]. iModIntro.
    iApply (derivy_map (derivy0:=sys')); [|done]=>/=.
    iIntros (? _ _) "Φ↔'Ψ %". iApply bi.sep_comm. iApply "Φ↔'Ψ".
  Qed.

  (** [na_strmi] by cons *)
  Lemma na_strmi_cons `{!nderivy Σ ih d} {p N N' Φ l l'} :
    na_nninv d 0 p N (Φ l) -∗ na_strmi d p N N' Φ l' -∗ (l +ₗ 1) ↦ #l'
      =[nninv_wsat d]=∗ na_strmi d p N N' Φ l.
  Proof.
    iIntros "$ #s ↦".
    iMod (na_nninv_alloc (na_strmtl _ _ _ _ _) with "[↦]") as "$"; [|done].
    simpl. iExists _. iFrame "↦". by rewrite rew_eq_hwf /=.
  Qed.

  (** [na_strmi] from a one-node loop *)
  Lemma na_strmi_loop_1 `{!nderivy Σ ih d} {p N N' Φ l} :
    na_nninv d 0 p N (Φ l) -∗ (l +ₗ 1) ↦ #l =[nninv_wsat d]=∗
      na_strmi d p N N' Φ l.
  Proof.
    iIntros "#Φ ↦". iFrame "Φ".
    iMod (na_nninv_alloc_rec (na_strmtl _ _ _ _ _) with "[↦]") as "$"; [|done].
    iIntros "/= #?". iExists _. rewrite rew_eq_hwf /=. by iFrame "↦ Φ".
  Qed.

  (** [na_strmi] from a two-node loop *)
  Lemma na_strmi_loop_2 `{!nderivy Σ ih d} {p N N' Φ l l'} :
    na_nninv d 0 p N (Φ l) -∗ na_nninv d 0 p N (Φ l') -∗
    (l +ₗ 1) ↦ #l' -∗ (l' +ₗ 1) ↦ #l =[nninv_wsat d]=∗
      na_strmi d p N N' Φ l ∗ na_strmi d p N N' Φ l'.
  Proof.
    iIntros "#Φ #Φ' ↦ ↦'". iFrame "Φ Φ'".
    iMod (na_nninv_alloc_rec (na_strmtl _ _ _ _ _ ∗ na_strmtl _ _ _ _ _)
      with "[↦ ↦']") as "inv"; last first.
    { simpl. by iDestruct (na_nninv_split with "inv") as "[$ $]". }
    iIntros "/= itls". iDestruct (na_nninv_split with "itls") as "[#? #?]".
    iSplitL "↦"; iExists _; rewrite rew_eq_hwf /=; iFrame; by iSplit.
  Qed.

  (** [siter] terminates under [na_strmis] *)
  Lemma twp_siter_na {p N N' Φ E F l} {f : val} {c : nat} : ↑N' ⊆ E → ↑N' ⊆ F →
    na_strmis p N N' Φ l -∗
    (∀ l, [[{ na_nninvd 0 p N (Φ l) ∗ na_own p F }]][nninv_wsatd]
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
    iMod (na_nninvd_acc with "[//] pF") as "/=((%l' & ↦ & s) & pF∖N & cl)";
      [done..|].
    rewrite rew_eq_hwf /=. iDestruct "s" as "#[??]". wp_load. wp_pures.
    iMod ("cl" with "[↦] pF∖N") as "pF".
    { iExists _. iFrame "↦". rewrite/= rew_eq_hwf /=. by iSplit. }
    have ->: (S c - 1)%Z = c by lia. by iApply ("IH" with "pF Ψ").
  Qed.

  (** [siter_nd] terminates under [na_strmis] *)
  Lemma twp_siter_nd_na {p N N' Φ E F l} {f : val} : ↑N' ⊆ E → ↑N' ⊆ F →
    na_strmis p N N' Φ l -∗
    (∀ l, [[{ na_nninvd 0 p N (Φ l) ∗ na_own p F }]][nninv_wsatd]
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
    [[{ na_nninvd 0 p N (Φ l) ∗ na_own p F }]][nninv_wsatd]
      f #l @ E
    [[{ RET #(); na_own p F }]].
  Proof.
    iIntros (??) "#f". iIntros (Ψ) "!> [#? pF] Ψ". iApply twpw_fupdw_nonval=>//.
    iMod (na_nninvd_acc with "[] pF") as "/=(Φ & pF∖N & cl)"; [done..|].
    wp_apply ("f" with "Φ"). iIntros "Φ". iMod ("cl" with "Φ pF∖N") as "?".
    iModIntro. by iApply "Ψ".
  Qed.
End verify.
