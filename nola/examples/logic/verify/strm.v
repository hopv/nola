(** * Verification on shared mutable singly linked streams *)

From nola.examples.logic Require Export inv.
From nola.iris Require Export wp.
From nola.examples.heap_lang Require Export proofmode notation.

(** Stream whose elements satisfy the condition [Φ] *)
Definition strm {κ Γᵘ Γᵍ} (N : namespace) (Φ : loc → nPropL (;ᵞ Γᵘ ++ Γᵍ))
  : loc → nProp κ (Γᵘ;ᵞ Γᵍ) :=
  (rec:ˢ l, n_inv' (_::_) 0 N
    (¢ᵍ Φ l ∗ ∃ l' : loc, (l +ₗ 1) ↦ # l' ∗ %ᵍˢ 0@ l'))%n.

(** Substitution over [strm] *)
Fact strm_nsubst {κ N V Φ Ψ l} :
  strm (κ:=κ) (Γᵘ:=[V]) N Φ l /: Ψ = strm (Γᵘ:=[]) N (λ l, Φ l /:ᵍ Ψ) l.
Proof. done. Qed.

(** Interpreted [strm] *)
Definition strmi `{!nintpGS Σ} s N Φ l : iProp Σ :=
  nninv s 0 N (Φ l ∗ ∃ l' : loc, (l +ₗ 1) ↦ # l' ∗ strm N Φ l').
Notation strmis := (strmi nsintp).

(** Stream whose elements are multiples of [d] *)
Definition mul_strmi `{!nintpGS Σ} s N (d : Z) l : iProp Σ :=
  strmi s N (λ l, ∃ k, l ↦ #(k * d))%n l.
Notation mul_strmis := (mul_strmi nsintp).

(** Atomically increases the first [c] elements of the stream by [d] *)
Definition iter_inc : val :=
  rec: "self" "d" "c" "l" :=
    if: "c" = #0 then #() else
      FAA "l" "d";; "self" "d" ("c" - #1) (! ("l" +ₗ #1)).

(** Calls [iter_inc] with a non-deterministic [c] *)
Definition iter_inc_nd : val := λ: "d" "l", iter_inc "d" Ndnat "l".

(** Forks [c] threads executing [iter_inc_nd] *)
Definition iter_inc_nd_forks : val :=
  rec: "self" "d" "c" "l" :=
    if: "c" = #0 then #() else
      Fork (iter_inc_nd "d" "l");; "self" "d" ("c" - #1) "l".

(** Calls [iter_inc_nd_forks] with a non-deterministic [c] *)
Definition iter_inc_nd_forks_nd : val :=
  λ: "d" "l", iter_inc_nd_forks "d" Ndnat "l".

Section verify.
  Context `{!nintpGS Σ}.

  (** [strm] is interpreted into [strmi] *)
  Fact strm_strmi {κ N Φ l s} :
    ⟦ strm N Φ l ⟧{κ}(s) ⊣⊢ strmi s N Φ l.
  Proof. by rewrite/= rew_eq_hwf /=. Qed.

  (** Convert the predicate of [strmi] *)
  Lemma strmi_convert `{!nsintpy Σ ih s} {N Φ Ψ l} :
    □ ⸨ ∀ l, (Φ l ={∅}=∗ Ψ l) ∗ (Ψ l ={∅}=∗ Φ l) ⸩(s, 0) -∗
    strmi s N Φ l -∗ strmi s N Ψ l.
  Proof.
    move: s nsintpy0 Φ Ψ l. apply (sintpy_acc (λ _, ∀ Φ Ψ l, _ -∗ _)).
    move=> s ? Φ Ψ l. iIntros "#sΦ↔Ψ". iApply nninv_convert. iModIntro.
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

  (** [iter_inc] terminates *)
  Lemma twp_iter_inc {N E d l} {c : nat} : ↑N ⊆ E →
    [[{ mul_strmis N d l }]][nninv_wsats]
      iter_inc #d #c #l @ E
    [[{ RET #(); True }]].
  Proof.
    iIntros (??) "#inv Φ".
    iInduction c as [|c] "IH" forall (l) "inv"; wp_rec; wp_pures;
      [by iApply "Φ"|].
    wp_bind (FAA _ _). iDestruct (nninv_split with "inv") as "[ihd itl]".
    iMod (nninvs_acc with "ihd") as "/=[[%k ↦] cl]"; [done|]. wp_faa.
    iModIntro. iMod ("cl" with "[↦]") as "_".
    { iExists _. have ->: ((k * d) + d = (k + 1) * d)%Z by lia. iFrame. }
    iModIntro. wp_pures. wp_bind (! _)%E.
    iMod (nninvs_acc with "itl") as "/=[(%& ↦ & inv') cl]"; [done|].
    rewrite rew_eq_hwf /=. iDestruct "inv'" as "#inv'". wp_load. iModIntro.
    iMod ("cl" with "[↦]") as "_"; [|iModIntro].
    { iExists _. rewrite/= rew_eq_hwf /=. by iFrame. }
    wp_pures. have ->: (S c - 1)%Z = c by lia. by iApply ("IH" with "Φ").
  Qed.

  (** [iter_inc_nd] terminates *)
  Lemma twp_iter_inc_nd {N E d l} : ↑N ⊆ E →
    [[{ mul_strmis N d l }]][nninv_wsats]
      iter_inc_nd #d #l @ E
    [[{ RET #(); True }]].
  Proof.
    iIntros (??) "#? ?". wp_lam. wp_pures. wp_apply twp_ndnat; [done|].
    iIntros (?) "_". by wp_apply twp_iter_inc.
  Qed.

  (** [iter_inc_nd_forks] terminates *)
  Lemma twp_iter_inc_nd_forks {N E d l} {c : nat} : ↑N ⊆ E →
    [[{ mul_strmis N d l }]][nninv_wsats]
      iter_inc_nd_forks #d #c #l @ E
    [[{ RET #(); True }]].
  Proof.
    iIntros (??) "#? Φ".
    iInduction c as [|c] "IH"; wp_lam; wp_pures; [by iApply "Φ"|].
    wp_apply twp_fork; [by wp_apply twp_iter_inc_nd|]. wp_pures.
    have ->: (S c - 1)%Z = c by lia. by iApply "IH".
  Qed.

  (** [iter_inc_nd_forks_nd] terminates *)
  Lemma twp_iter_inc_nd_forks_nd {N E d l} : ↑N ⊆ E →
    [[{ mul_strmis N d l }]][nninv_wsats]
      iter_inc_nd_forks_nd #d #l @ E
    [[{ RET #(); True }]].
  Proof.
    iIntros (??) "#? ?". wp_lam. wp_pures. wp_apply twp_ndnat; [done|].
    iIntros (?) "_". by wp_apply twp_iter_inc_nd_forks.
  Qed.
End verify.
