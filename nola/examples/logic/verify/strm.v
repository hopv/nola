(** * Verification on shared mutable singly linked streams *)

From nola.examples.logic Require Export inv verify.strm_base.
From nola.iris Require Export wp.
From nola.examples.heap_lang Require Export proofmode notation.

(** Stream whose elements satisfy the condition [Φ] *)
Definition strm {κ Γᵘ Γᵍ} (N N' : namespace) (Φ : loc → nPropL (;ᵞ Γᵘ ++ Γᵍ))
  : loc → nProp κ (Γᵘ;ᵞ Γᵍ) :=
  (rec:ˢ l, n_inv' (_::_) 0 N (¢ᵍ Φ l) ∗
    n_inv' (_::_) 0 N' (∃ l' : loc, (l +ₗ 1) ↦ # l' ∗ %ᵍˢ 0@ l'))%n.

(** Substitution over [strm] *)
Fact strm_nsubst {κ N N' V Φ Ψ l} :
  strm (κ:=κ) (Γᵘ:=[V]) N N' Φ l /: Ψ = strm (Γᵘ:=[]) N N' (λ l, Φ l /:ᵍ Ψ) l.
Proof. done. Qed.

(** Interpreted [strm] *)
Definition strmtl {κ} N N' (Φ : _ → _ (;ᵞ)) l : nProp κ (;ᵞ) :=
  ∃ l' : loc, (l +ₗ 1) ↦ # l' ∗ strm (Γᵘ:=[]) N N' Φ l'.
Definition strmi `{!nintpGS Σ} s N N' Φ l : iProp Σ :=
  nninv s 0 N (Φ l) ∗ nninv s 0 N' (strmtl N N' Φ l).
Notation strmis := (strmi nsintp).

(** A has_multiplier of [d] is stored at [l] *)
Definition has_mult {κ Γ} (d : Z) l : nProp κ Γ := ∃ k, l ↦ #(k * d).

(** Increment by calling [FAA] *)
Definition incr_faa (d : Z) : val := λ: "l", FAA "l" #d;; #().

(** Posssibly increment by calling [CAS] *)
Definition may_incr_cas' (d : Z) : val :=
  rec: "self" "c" "l" :=
    if: "c" = #0 then #() else
      let: "n" := !"l" in
      if: CAS "l" "n" ("n" + #d) then #() else "self" ("c" - #1) "l".
Definition may_incr_cas (d : Z) : val :=
  λ: "l", may_incr_cas' d Ndnat "l".

Section verify.
  Context `{!nintpGS Σ}.

  (** [strm] is interpreted into [strmi] *)
  Fact strm_strmi {κ N N' Φ l s} :
    ⟦ strm N N' Φ l ⟧{κ}(s) ⊣⊢ strmi s N N' Φ l.
  Proof. by rewrite/= rew_eq_hwf /=. Qed.

  (** Convert the predicate of [strmi] *)
  Lemma strmi_convert `{!nsintpy Σ ih s} {N N' Φ Ψ l} :
    □ ⸨ ∀ l, (Φ l ={∅}=∗ Ψ l) ∗ (Ψ l ={∅}=∗ Φ l) ⸩(s, 0) -∗
    strmi s N N' Φ l -∗ strmi s N N' Ψ l.
  Proof.
    move: s nsintpy0 Φ Ψ l. apply (sintpy_acc (λ _, ∀ Φ Ψ l, _ -∗ _)).
    move=> s ? Φ Ψ l. iIntros "#? #[??]".
    iSplit; iApply nninv_convert=>//; iModIntro.
    { iApply sintpy_map; [|done]=>/=. iIntros (s' sys' _) "Φ↔Ψ Φ".
      iDestruct ("Φ↔Ψ" $! _) as "[ΦΨ ΨΦ]". iMod ("ΦΨ" with "Φ") as "$".
      iIntros "!> Ψ". by iApply "ΨΦ". }
    iApply sintpy_byintp=>/=. iIntros (s' sys' [IH _]) "_ #to _ (%l' & ↦ & st)".
    iModIntro. rewrite rew_eq_hwf /=. iDestruct "st" as "#st".
    iDestruct ("to" with "[//]") as "?". iSplitL.
    { iExists _. iFrame "↦". rewrite rew_eq_hwf /=. by iApply IH. }
    iIntros "(%l'' & ↦ & st') !>". iExists _. iFrame "↦".
    rewrite !rew_eq_hwf /=. iApply IH; [|done]. iModIntro.
    iApply (sintpy_map (sintpy0:=sys')); [|done]=>/=.
    iIntros (? _ _) "Φ↔'Ψ %". iApply bi.sep_comm. iApply "Φ↔'Ψ".
  Qed.

  (** [strmi] by cons *)
  Lemma strmi_cons `{!nsintpy Σ ih s} {N N' Φ l l'} :
    nninv s 0 N (Φ l) -∗ strmi s N N' Φ l' -∗ (l +ₗ 1) ↦ #l' =[nninv_wsat s]=∗
      strmi s N N' Φ l.
  Proof.
    iIntros "$ #st ↦".
    iMod (nninv_alloc (strmtl _ _ _ _) with "[↦]") as "$"; [|done].
    simpl. iExists _. iFrame "↦". by rewrite rew_eq_hwf /=.
  Qed.

  (** [strmi] from a one-node loop *)
  Lemma strmi_loop_1 `{!nsintpy Σ ih s} {N N' Φ l} :
    nninv s 0 N (Φ l) -∗ (l +ₗ 1) ↦ #l =[nninv_wsat s]=∗
      strmi s N N' Φ l.
  Proof.
    iIntros "#Φ ↦". iFrame "Φ".
    iMod (nninv_alloc_rec (strmtl _ _ _ _) with "[↦]") as "$"; [|done].
    iIntros "/= #?". iExists _. rewrite rew_eq_hwf /=. by iFrame "↦ Φ".
  Qed.

  (** [strmi] from a two-node loop *)
  Lemma strmi_loop_2 `{!nsintpy Σ ih s} {N N' Φ l l'} :
    nninv s 0 N (Φ l) -∗ nninv s 0 N (Φ l') -∗
    (l +ₗ 1) ↦ #l' -∗ (l' +ₗ 1) ↦ #l =[nninv_wsat s]=∗
      strmi s N N' Φ l ∗ strmi s N N' Φ l'.
  Proof.
    iIntros "#Φ #Φ' ↦ ↦'". iFrame "Φ Φ'".
    iMod (nninv_alloc_rec (strmtl _ _ _ _ ∗ strmtl _ _ _ _) with "[↦ ↦']")
      as "inv"; last first.
    { simpl. by iDestruct (nninv_split with "inv") as "[$ $]". }
    iIntros "/= itls". iDestruct (nninv_split with "itls") as "[#? #?]".
    iSplitL "↦"; iExists _; rewrite rew_eq_hwf /=; iFrame; by iSplit.
  Qed.

  (** [siter] terminates under [strmis] *)
  Lemma twp_siter {N N' E Φ l} {f : val} {c : nat} : ↑N' ⊆ E →
    (∀ l : loc,
      [[{ nninvs 0 N (Φ l) }]][nninv_wsats] f #l @ E [[{ RET #(); True }]]) -∗
    [[{ strmis N N' Φ l }]][nninv_wsats]
      siter f #c #l @ E
    [[{ RET #(); True }]].
  Proof.
    iIntros (?) "#f". iIntros (Ψ) "!> #[ihd itl] Ψ".
    iInduction c as [|c] "IH" forall (l) "ihd itl"; wp_rec; wp_pures;
      [by iApply "Ψ"|].
    wp_apply "f"; [done|]. iIntros "_". wp_pures. wp_bind (! _)%E.
    iMod (nninvs_acc with "itl") as "/=[(%l' & ↦ & st) cl]"; [done|].
    rewrite rew_eq_hwf /=. iDestruct "st" as "#[??]". wp_load. iModIntro.
    iMod ("cl" with "[↦]") as "_".
    { iExists _. rewrite rew_eq_hwf /=. iFrame "↦". by iSplit. }
    iModIntro. wp_pures. have ->: (S c - 1)%Z = c by lia.
    by iApply ("IH" with "Ψ").
  Qed.

  (** [siter_nd] terminates under [strmis] *)
  Lemma twp_siter_nd {N N' E Φ l} {f : val} : ↑N' ⊆ E →
    (∀ l : loc,
      [[{ nninvs 0 N (Φ l) }]][nninv_wsats] f #l @ E [[{ RET #(); True }]]) -∗
    [[{ strmis N N' Φ l }]][nninv_wsats]
      siter_nd f #l @ E
    [[{ RET #(); True }]].
  Proof.
    iIntros (?) "#?". iIntros (?) "!> #? ?". wp_lam. wp_pures.
    wp_apply twp_ndnat; [done|]. iIntros (?) "_". by wp_apply twp_siter.
  Qed.

  (** [siter_nd_forks] terminates under [strmis] *)
  Lemma twp_siter_nd_forks {N N' E Φ l} {f : val} {c : nat} :
    (∀ l : loc,
      [[{ nninvs 0 N (Φ l) }]][nninv_wsats] f #l [[{ RET #(); True }]]) -∗
    [[{ strmis N N' Φ l }]][nninv_wsats]
      siter_nd_forks f #c #l @ E
    [[{ RET #(); True }]].
  Proof.
    iIntros "#?" (Ψ) "!> #? Ψ".
    iInduction c as [|c] "IH"; wp_lam; wp_pures; [by iApply "Ψ"|].
    wp_apply twp_fork; [by wp_apply twp_siter_nd|]. wp_pures.
    have ->: (S c - 1)%Z = c by lia. by iApply "IH".
  Qed.

  (** [siter_nd_forks_nd] terminates under [strmis] *)
  Lemma twp_siter_nd_forks_nd {N N' E Φ l} {f : val} :
    (∀ l : loc,
      [[{ nninvs 0 N (Φ l) }]][nninv_wsats] f #l [[{ RET #(); True }]]) -∗
    [[{ strmis N N' Φ l }]][nninv_wsats]
      siter_nd_forks_nd f #l @ E
    [[{ RET #(); True }]].
  Proof.
    iIntros "#?" (?) "!> #? ?". wp_lam. wp_pures. wp_apply twp_ndnat; [done|].
    iIntros (?) "_". by wp_apply twp_siter_nd_forks.
  Qed.

  (** [incr_faa] on [nninvs] over [has_mult] *)
  Lemma twp_incr_faa {N E d l} : ↑N ⊆ E →
    [[{ nninvs 0 N (has_mult d l) }]][nninv_wsats]
      incr_faa d #l @ E
    [[{ RET #(); True }]].
  Proof.
    iIntros (??) "#? Φ". wp_lam. wp_bind (FAA _ _).
    iMod (nninvs_acc with "[//]") as "/=[[%k ↦] cl]"; [done|]. wp_faa.
    iModIntro. iMod ("cl" with "[↦]") as "_".
    { iExists _. by have ->: (k * d + d = (k + 1) * d)%Z by lia. }
    iModIntro. wp_pures. by iApply "Φ".
  Qed.

  (** [may_incr_cas] on [nninvs] over [has_mult] *)
  Lemma twp_may_incr_cas' {N E d l} {c : nat} : ↑N ⊆ E →
    [[{ nninvs 0 N (has_mult d l) }]][nninv_wsats]
      may_incr_cas' d #c #l @ E
    [[{ RET #(); True }]].
  Proof.
    iIntros (??) "#? Φ".
    iInduction c as [|c] "IH"; wp_lam; wp_pures; [by iApply "Φ"|].
    wp_bind (! _)%E. iMod (nninvs_acc with "[//]") as "/=[[%k ↦] cl]"; [done|].
    wp_load. iModIntro. iMod ("cl" with "[↦]") as "_"; [by iExists _|].
    iModIntro. wp_pures. wp_bind (CmpXchg _ _ _).
    iMod (nninvs_acc with "[//]") as "/=[[%k' ↦] cl]"; [done|].
    case (decide (k' * d = k * d)%Z)=> [->|?].
    - wp_apply (twp_cmpxchg_suc with "↦")=>//; [solve_vals_compare_safe|].
      iIntros "↦". iMod ("cl" with "[↦]") as "_".
      { iExists _. by have ->: (k * d + d = (k + 1) * d)%Z by lia. }
      iModIntro. wp_pures. by iApply "Φ".
    - wp_apply (twp_cmpxchg_fail with "↦")=>//;
        [by case|solve_vals_compare_safe|].
      iIntros "↦". iMod ("cl" with "[↦]") as "_"; [by iExists _|]. iModIntro.
      wp_pures. have ->: (S c - 1)%Z = c by lia. by iApply "IH".
  Qed.
  Lemma twp_may_incr_cas {N E d l} : ↑N ⊆ E →
    [[{ nninvs 0 N (has_mult d l) }]][nninv_wsats]
      may_incr_cas d #l @ E
    [[{ RET #(); True }]].
  Proof.
    iIntros (??) "#? Φ". wp_lam. wp_apply twp_ndnat; [done|].
    iIntros (?) "_". by wp_apply twp_may_incr_cas'.
  Qed.
End verify.
