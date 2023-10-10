(** * Verification on shared mutable singly linked infinite lists *)

From nola.examples.logic Require Export inv verify.ilist_base.
From nola.iris Require Export wp.
From nola.examples.heap_lang Require Export proofmode notation.

(** Infinite list whose elements satisfy the condition [Φ] *)
Definition ilist {κ Γᵘ Γᵍ} (N : namespace) (Φ : loc → nPropL (;ᵞ Γᵘ ++ Γᵍ))
  : loc → nProp κ (Γᵘ;ᵞ Γᵍ) :=
  (rec:ˢ l, n_inv' (_::_) N (¢ᵍ Φ l) ∗
    n_inv' (_::_) N (∃ l' : loc, (l +ₗ 1) ↦ # l' ∗ %ᵍˢ 0@ l'))%n.

(** Substitution over [ilist] *)
Fact ilist_nsubst {κ N V Φ Ψ l} :
  ilist (κ:=κ) (Γᵘ:=[V]) N Φ l /: Ψ = ilist (Γᵘ:=[]) N (λ l, Φ l /:ᵍ Ψ) l.
Proof. done. Qed.

(** Interpreted [ilist] *)
Definition ilisttl {κ} N (Φ : _ → _ (;ᵞ)) l : nProp κ (;ᵞ) :=
  ∃ l' : loc, (l +ₗ 1) ↦ # l' ∗ ilist (Γᵘ:=[]) N Φ l'.
Definition ilisti `{!nintpGS Σ} δ N Φ l : iProp Σ :=
  ninv δ N (Φ l) ∗ ninv δ N (ilisttl N Φ l).
Notation ilistis := (ilisti nderiv).

(** A has_multiplier of [δ] is stored at [l] *)
Definition has_mult {κ Γ} (δ : Z) l : nProp κ Γ := ∃ k, l ↦ #(k * δ).

(** Increment by calling [FAA] *)
Definition incr_faa (δ : Z) : val := λ: "l", FAA "l" #δ;; #().

(** Possibly increment by calling [CAS] *)
Definition may_incr_cas' (δ : Z) : val :=
  rec: "self" "c" "l" :=
    if: "c" = #0 then #() else
      let: "n" := !"l" in
      if: CAS "l" "n" ("n" + #δ) then #() else "self" ("c" - #1) "l".
Definition may_incr_cas (δ : Z) : val :=
  λ: "l", may_incr_cas' δ Ndnat "l".

Section verify.
  Context `{!nintpGS Σ}.

  (** [ilist] is interpreted into [ilisti] *)
  Fact ilist_ilisti {κ N Φ l δ} : ⟦ ilist N Φ l ⟧{κ}(δ) ⊣⊢ ilisti δ N Φ l.
  Proof. by rewrite/= rew_eq_hwf /=. Qed.

  (** Convert the predicate of [ilisti] *)
  Lemma ilisti_convert `{!nderivy ih δ} {N Φ Ψ l} :
    □ ⸨ ∀ l, (Φ l ={∅}=∗ Ψ l) ∗ (Ψ l ={∅}=∗ Φ l) ⸩(δ) -∗
    ilisti δ N Φ l -∗ ilisti δ N Ψ l.
  Proof.
    move: δ nderivy0 Φ Ψ l. apply (derivy_acc (λ _, ∀ Φ Ψ l, _ -∗ _)).
    move=> δ ? Φ Ψ l. iIntros "#? #[ihd itl]".
    iSplit; iApply ninv_convert; [|iApply "ihd"| |iApply "itl"]; iModIntro.
    { iApply derivy_map; [|done]=>/=. iIntros (δ' dyd' _) "Φ↔Ψ Φ".
      iDestruct ("Φ↔Ψ" $! _) as "[ΦΨ ΨΦ]". iMod ("ΦΨ" with "Φ") as "$".
      iIntros "!> Ψ". by iApply "ΨΦ". }
    iApply derivy_byintp=>/=. iIntros (δ' dyd' [IH _]) "_ #→ _ (%l' & ↦ & i)".
    iModIntro. rewrite rew_eq_hwf /=. iDestruct "i" as "#i".
    iDestruct ("→" with "[//]") as "?". iSplitL.
    { iExists _. iFrame "↦". rewrite rew_eq_hwf /=. by iApply IH. }
    iIntros "(%l'' & ↦ & i') !>". iExists _. iFrame "↦".
    rewrite !rew_eq_hwf /=. iApply IH; [|done]. iModIntro.
    iApply (derivy_map (derivy0:=dyd')); [|done]=>/=.
    iIntros (? _ _) "Φ↔'Ψ %". iApply bi.sep_comm. iApply "Φ↔'Ψ".
  Qed.

  (** [ilisti] by cons *)
  Lemma ilisti_cons `{!nderivy ih δ} {N Φ l l'} :
    ninv δ N (Φ l) -∗ ilisti δ N Φ l' -∗ (l +ₗ 1) ↦ #l' =[inv_wsat' δ]=∗
      ilisti δ N Φ l.
  Proof.
    iIntros "$ #i ↦".
    iMod (ninv_alloc (ilisttl _ _ _) with "[↦]") as "$"; [|done].
    simpl. iExists _. iFrame "↦". by rewrite rew_eq_hwf /=.
  Qed.

  (** [ilisti] from a one-node loop *)
  Lemma ilisti_loop_1 `{!nderivy ih δ} {N Φ l} :
    ninv δ N (Φ l) -∗ (l +ₗ 1) ↦ #l =[inv_wsat' δ]=∗
      ilisti δ N Φ l.
  Proof.
    iIntros "#Φ ↦". iFrame "Φ".
    iMod (ninv_alloc_rec (ilisttl _ _ _) with "[↦]") as "$"; [|done].
    iIntros "/= #?". iExists _. rewrite rew_eq_hwf /=. by iFrame "↦ Φ".
  Qed.

  (** [ilisti] from a two-node loop *)
  Lemma ilisti_loop_2 `{!nderivy ih δ} {N Φ l l'} :
    ninv δ N (Φ l) -∗ ninv δ N (Φ l') -∗
    (l +ₗ 1) ↦ #l' -∗ (l' +ₗ 1) ↦ #l =[inv_wsat' δ]=∗
      ilisti δ N Φ l ∗ ilisti δ N Φ l'.
  Proof.
    iIntros "#Φ #Φ' ↦ ↦'". iFrame "Φ Φ'".
    iMod (ninv_alloc_rec (ilisttl _ _ _ ∗ ilisttl _ _ _) with "[↦ ↦']")
      as "inv"; last first.
    { simpl. by iDestruct (ninv_split with "inv") as "[$ $]". }
    iIntros "/= itls". iDestruct (ninv_split with "itls") as "[#? #?]".
    iSplitL "↦"; iExists _; rewrite rew_eq_hwf /=; iFrame; by iSplit.
  Qed.

  (** [siter] terminates under [ilistis] *)
  Lemma twp_siter {N E Φ ln l} {f : val} {n : nat} : ↑N ⊆ E →
    (∀ l : loc,
      [[{ ninvd N (Φ l) }]][inv_wsatd] f #l @ E [[{ RET #(); True }]]) -∗
    [[{ ln ↦ #n ∗ ilistis N Φ l }]][inv_wsatd]
      siter f #ln #l @ E
    [[{ RET #(); ln ↦ #0 }]].
  Proof.
    iIntros (?) "#f". iIntros (Ψ) "!> [↦n #[ihd itl]] Ψ".
    iInduction n as [|n] "IH" forall (l) "ihd itl"; wp_rec; wp_pures; wp_load;
      wp_pures; [by iApply "Ψ"|].
    wp_apply "f"; [done|]. iIntros "_". wp_pures. wp_load. wp_op.
    have -> : (S n - 1)%Z = n by lia. wp_store. wp_op. wp_bind (! _)%E.
    iMod (ninv_acc with "itl") as "/=[(%l' & ↦ & i) cl]"; [done|].
    rewrite rew_eq_hwf /=. iDestruct "i" as "#[??]". wp_load. iModIntro.
    iMod ("cl" with "[↦]") as "_".
    { iExists _. rewrite rew_eq_hwf /=. iFrame "↦". by iSplit. }
    iModIntro. by iApply ("IH" with "↦n Ψ").
  Qed.

  (** [siter_nd] terminates under [ilistis] *)
  Lemma twp_siter_nd {N E Φ l} {f : val} : ↑N ⊆ E →
    (∀ l : loc,
      [[{ ninvd N (Φ l) }]][inv_wsatd] f #l @ E [[{ RET #(); True }]]) -∗
    [[{ ilistis N Φ l }]][inv_wsatd]
      siter_nd f #l @ E
    [[{ RET #(); True }]].
  Proof.
    iIntros (?) "#?". iIntros (Ψ) "!> #? Ψ". wp_lam. wp_pures.
    wp_apply twp_ndnat; [done|]. iIntros (?) "_". wp_alloc ln as "↦n". wp_pures.
    wp_apply (twp_siter with "[] [$↦n]")=>//. iIntros. by iApply "Ψ".
  Qed.

  (** [siter_nd_forks] terminates under [ilistis] *)
  Lemma twp_siter_nd_forks {N E Φ l lk} {f : val} {k : nat} :
    (∀ l : loc,
      [[{ ninvd N (Φ l) }]][inv_wsatd] f #l [[{ RET #(); True }]]) -∗
    [[{ lk ↦ #k ∗ ilistis N Φ l }]][inv_wsatd]
      siter_nd_forks f #lk #l @ E
    [[{ RET #(); lk ↦ #0 }]].
  Proof.
    iIntros "#?" (Ψ) "!> [↦k #?] Ψ".
    iInduction k as [|k] "IH"; wp_lam; wp_pures; wp_load; wp_pures;
      [by iApply "Ψ"|].
    wp_apply twp_fork; [by wp_apply twp_siter_nd|]. wp_pures. wp_load. wp_pure.
    have -> : (S k - 1)%Z = k by lia. wp_store. by iApply ("IH" with "↦k").
  Qed.

  (** [siter_nd_forks_nd] terminates under [ilistis] *)
  Lemma twp_siter_nd_forks_nd {N E Φ l} {f : val} :
    (∀ l : loc,
      [[{ ninvd N (Φ l) }]][inv_wsatd] f #l [[{ RET #(); True }]]) -∗
    [[{ ilistis N Φ l }]][inv_wsatd]
      siter_nd_forks_nd f #l @ E
    [[{ RET #(); True }]].
  Proof.
    iIntros "#?" (Ψ) "!> #? Ψ". wp_lam. wp_pures. wp_apply twp_ndnat; [done|].
    iIntros (?) "_". wp_alloc lk as "↦k". wp_pures.
    wp_apply (twp_siter_nd_forks with "[] [$↦k]")=>//. iIntros. by iApply "Ψ".
  Qed.

  (** [incr_faa] on [ninvd] over [has_mult] *)
  Lemma twp_incr_faa {N E δ l} : ↑N ⊆ E →
    [[{ ninvd N (has_mult δ l) }]][inv_wsatd]
      incr_faa δ #l @ E
    [[{ RET #(); True }]].
  Proof.
    iIntros (??) "#? Φ". wp_lam. wp_bind (FAA _ _).
    iMod (ninv_acc with "[//]") as "/=[[%k ↦] cl]"; [done|]. wp_faa.
    iModIntro. iMod ("cl" with "[↦]") as "_".
    { iExists _. by have -> : (k * δ + δ = (k + 1) * δ)%Z by lia. }
    iModIntro. wp_pures. by iApply "Φ".
  Qed.

  (** [may_incr_cas] on [ninvd] over [has_mult] *)
  Lemma twp_may_incr_cas' {N E δ l} {c : nat} : ↑N ⊆ E →
    [[{ ninvd N (has_mult δ l) }]][inv_wsatd]
      may_incr_cas' δ #c #l @ E
    [[{ RET #(); True }]].
  Proof.
    iIntros (??) "#? Φ".
    iInduction c as [|c] "IH"; wp_lam; wp_pures; [by iApply "Φ"|].
    wp_bind (! _)%E. iMod (ninv_acc with "[//]") as "/=[[%k ↦] cl]"; [done|].
    wp_load. iModIntro. iMod ("cl" with "[↦]") as "_"; [by iExists _|].
    iModIntro. wp_pures. wp_bind (CmpXchg _ _ _).
    iMod (ninv_acc with "[//]") as "/=[[%k' ↦] cl]"; [done|].
    case (decide (k' * δ = k * δ)%Z)=> [->|?].
    - wp_apply (twp_cmpxchg_suc with "↦")=>//; [solve_vals_compare_safe|].
      iIntros "↦". iMod ("cl" with "[↦]") as "_".
      { iExists _. by have -> : (k * δ + δ = (k + 1) * δ)%Z by lia. }
      iModIntro. wp_pures. by iApply "Φ".
    - wp_apply (twp_cmpxchg_fail with "↦")=>//;
        [by case|solve_vals_compare_safe|].
      iIntros "↦". iMod ("cl" with "[↦]") as "_"; [by iExists _|]. iModIntro.
      wp_pures. have -> : (S c - 1)%Z = c by lia. by iApply "IH".
  Qed.
  Lemma twp_may_incr_cas {N E δ l} : ↑N ⊆ E →
    [[{ ninvd N (has_mult δ l) }]][inv_wsatd]
      may_incr_cas δ #l @ E
    [[{ RET #(); True }]].
  Proof.
    iIntros (??) "#? Φ". wp_lam. wp_apply twp_ndnat; [done|].
    iIntros (?) "_". by wp_apply twp_may_incr_cas'.
  Qed.
End verify.
