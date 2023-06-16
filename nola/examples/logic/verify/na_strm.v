(** * Verification on non-atomic shared mutable singly linked streams *)

From nola.examples.logic Require Export na_inv.
From nola.iris Require Export wp.
From nola.examples.heap_lang Require Export proofmode notation.

(** Stream whose elements satisfy the condition [Φ] *)
Definition na_strm {κ Γᵘ Γᵍ} (p : na_inv_pool_name) (N : namespace)
  (Φ : loc → nPropL (;ᵞ Γᵘ ++ Γᵍ)) : loc → nProp κ (Γᵘ;ᵞ Γᵍ) :=
  (rec:ˢ l, n_na_inv' (_::_) 0 p N
    (¢ᵍ Φ l ∗ ∃ l' : loc, (l +ₗ 1) ↦ # l' ∗ %ᵍˢ 0@ l'))%n.

(** Interpreted [strm] *)
Definition na_strmi `{!nintpGS Σ} s p N Φ l : iProp Σ :=
  na_nninv s 0 p N (Φ l ∗ ∃ l' : loc, (l +ₗ 1) ↦ # l' ∗ na_strm p N Φ l').
Notation na_strmis := (na_strmi nsintp).

(** Calls [f] on the first [c] elements of the stream by [d] *)
Definition iter : val :=
  rec: "self" "f" "c" "l" :=
    if: "c" = #0 then #() else "f" "l";; "self" "f" ("c" - #1) (! ("l" +ₗ #1)).

(** Calls [iter] with a non-deterministic [c] *)
Definition iter_nd : val := λ: "f" "l", iter "f" Ndnat "l".

Section verify.
  Context `{!nintpGS Σ}.

  (** [na_strm] is interpreted into [na_strmi] *)
  Fact na_strm_strmi {κ p N Φ l s} :
    ⟦ na_strm p N Φ l ⟧{κ}(s) ⊣⊢ na_strmi s p N Φ l.
  Proof. by rewrite/= rew_eq_hwf /=. Qed.

  (** Convert the predicate of [na_strmi] *)
  Lemma na_strmi_convert `{!nsintpy Σ ih s} {p N Φ Ψ l} :
    □ ⸨ ∀ l, (Φ l ={∅}=∗ Ψ l) ∗ (Ψ l ={∅}=∗ Φ l) ⸩(s, 0) -∗
    na_strmi s p N Φ l -∗ na_strmi s p N Ψ l.
  Proof.
    move: s nsintpy0 Φ Ψ l. apply (sintpy_acc (λ _, ∀ Φ Ψ l, _ -∗ _)).
    move=> s ? Φ Ψ l. iIntros "#sΦ↔Ψ". iApply na_nninv_convert. iModIntro.
    iApply sintpy_byintp=>/=.
    iIntros (s' sys' [IH _]) "#to #tos' _ (Φ & %l' & ↦ & inv)".
    rewrite rew_eq_hwf /=. iDestruct "inv" as "#inv".
    iDestruct ("to" with "sΦ↔Ψ") as "/=Φ↔Ψ".
    iDestruct ("tos'" with "sΦ↔Ψ") as "s'Φ↔Ψ".
    iDestruct ("Φ↔Ψ" $! _) as "[ΦΨ ΨΦ]". iMod ("ΦΨ" with "Φ") as "$". iModIntro.
    iSplitL "↦". { iExists _. iFrame "↦". rewrite rew_eq_hwf /=.
      iApply (IH with "[//] inv"). }
    iIntros "(Ψ & %l'' & ↦ & inv')". iMod ("ΨΦ" with "Ψ") as "$". iModIntro.
    iExists _. iFrame "↦". rewrite !rew_eq_hwf /=. iDestruct "inv'" as "#inv'".
    iApply (IH with "[]"); [|done]. iModIntro.
    iApply (sintpy_map (sintpy0:=sys') with "[] s'Φ↔Ψ")=>/=. iClear "#".
    iIntros (? _ _) "Φ↔Ψ %". iApply bi.sep_comm. iApply "Φ↔Ψ".
  Qed.

  (** [iter] terminates *)
  Lemma twp_iter {p N Φ E F l} {f : val} {c : nat} : ↑N ⊆ E → ↑N ⊆ F →
    na_strmis p N Φ l -∗
    (∀ l, [[{ ⟦ Φ l ⟧ }]][nninv_wsats] f #l @ E [[{ RET #(); ⟦ Φ l ⟧ }]]) -∗
    [[{ na_own p F }]][nninv_wsats]
      iter f #c #l @ E
    [[{ RET #(); True }]].
  Proof.
    iIntros (??) "#inv #f". iIntros (Ψ) "!> pF Ψ".
    iInduction c as [|c] "IH" forall (l) "inv"; wp_rec; wp_pures;
      [by iApply "Ψ"|].
    iMod (na_nninvs_acc with "inv pF")
      as "/=((Φ & % & ↦ & inv') & pF∖N & cl)"; [done..|].
    rewrite rew_eq_hwf /=. iDestruct "inv'" as "#inv'".
    wp_apply ("f" with "Φ"). iIntros "Φ". wp_pures. wp_load. wp_pures.
    iMod ("cl" with "[$Φ ↦] pF∖N") as "pF".
    { iExists _. rewrite/= rew_eq_hwf /=. by iFrame. }
    have ->: (S c - 1)%Z = c by lia. by iApply ("IH" with "pF Ψ").
  Qed.

  (** [iter_nd] terminates *)
  Lemma twp_iter_nd {p N Φ E F l} {f : val} : ↑N ⊆ E → ↑N ⊆ F →
    na_strmis p N Φ l -∗
    (∀ l, [[{ ⟦ Φ l ⟧ }]][nninv_wsats] f #l @ E [[{ RET #(); ⟦ Φ l ⟧ }]]) -∗
    [[{ na_own p F }]][nninv_wsats]
      iter_nd f #l @ E
    [[{ RET #(); True }]].
  Proof.
    iIntros (??) "#? #?". iIntros (Ψ) "!> pF ?". wp_lam. wp_pures.
    wp_apply twp_ndnat; [done|]. iIntros (?) "_".
    by wp_apply (twp_iter with "[//] [] pF").
  Qed.
End verify.
