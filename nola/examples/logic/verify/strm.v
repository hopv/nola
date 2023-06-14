(** * Verification on shared mutable singly linked streams *)

From nola.examples.logic Require Export inv.
From nola.iris Require Export wp.
From nola.examples.heap_lang Require Export proofmode notation.

(** Stream whose elements satisfy the condition [Φ] *)
Definition strm {κ Γᵘ Γᵍ} (N : namespace) (Φ : loc → nPropL (;ᵞ Γᵘ ++ Γᵍ))
  : loc → nProp κ (Γᵘ;ᵞ Γᵍ) :=
  (rec:ˢ l, n_inv' (_::_) 0 N (∃ l' : loc,
    l ↦ # l' ∗ ¢ᵍ Φ (l +ₗ 1) ∗ %ᵍˢ 0@ l'))%n.

(** Stream whose elements are multiples of [d] *)
Definition mul_strm {κ Γ} (N : namespace) (d : Z) : loc → nProp κ Γ :=
  strm N (λ l, ∃ k, l ↦ #(k * d))%n.

(** Atomically increases the first [c] elements of the stream by [d] *)
Definition iter_inc (d : Z) : val :=
  rec: "self" "c" "l" :=
    if: "c" = #0 then #() else FAA ("l" +ₗ #1) #d;; "self" ("c" - #1) (! "l").

(** Calls [iter_inc] with a non-deterministic [c] *)
Definition iter_inc_nd d : val := λ: "l", iter_inc d Ndnat "l".

(** Forks [c] threads executing [iter_inc_nd] *)
Definition iter_inc_nd_forks d : val :=
  rec: "self" "c" "l" :=
    if: "c" = #0 then #() else Fork (iter_inc_nd d "l");; "self" ("c" - #1) "l".

(** Calls [iter_inc_nd_forks] with a non-deterministic [c] *)
Definition iter_inc_nd_forks_nd d : val :=
  λ: "l", iter_inc_nd_forks d Ndnat "l".

Section verify.
  Context `{!nintpGS Σ}.

  (** [iter_inc] terminates *)
  Lemma twp_iter_inc {N E d l} {c : nat} : ↑N ⊆ E →
    [[{ ⟦ mul_strm N d l ⟧{nL} }]][nninv_wsats]
      iter_inc d #c #l @ E
    [[{ RET #(); True }]].
  Proof.
    rewrite/= rew_eq_hwf /=. iIntros (??) "#inv Φ".
    iInduction c as [|c] "IH" forall (l) "inv"; wp_rec; wp_pures;
      [by iApply "Φ"|].
    wp_bind (FAA _ _). iMod (nninvs_acc with "[//]") as "/=[big cl]"; [done|].
    iDestruct "big" as (?) "(l↦ & (%k & l+1↦) & inv')".
    wp_faa. iModIntro. iMod ("cl" with "[l↦ l+1↦ inv']") as "_".
    { iExists _. iFrame "l↦ inv'". iExists _.
      have ->: ((k * d) + d = (k + 1) * d)%Z by lia. iFrame. }
    iModIntro. wp_pures. wp_bind (! _)%E.
    iMod (nninvs_acc with "[//]") as "/=[big cl]"; [done|].
    iDestruct "big" as (?) "(l↦ & l+1↦ & inv')". rewrite rew_eq_hwf /=.
    iDestruct "inv'" as "#inv'". wp_load. iModIntro.
    iMod ("cl" with "[l↦ l+1↦]") as "_"; [|iModIntro].
    { iExists _. rewrite/= rew_eq_hwf. by iFrame. }
    wp_pures. have ->: (S c - 1)%Z = c by lia. by iApply ("IH" with "Φ").
  Qed.

  (** [iter_inc_nd] terminates *)
  Lemma twp_iter_inc_nd {N E d l} : ↑N ⊆ E →
    [[{ ⟦ mul_strm N d l ⟧{nL} }]][nninv_wsats]
      iter_inc_nd d #l @ E
    [[{ RET #(); True }]].
  Proof.
    rewrite/= rew_eq_hwf /=. iIntros (??) "#? Φ". wp_lam. wp_pures.
    wp_apply twp_ndnat; [done|]. iIntros (?) "_".
    wp_apply (twp_iter_inc with "[]"); by [|rewrite/= rew_eq_hwf /=|]. Unshelve.
  Qed.

  (** [iter_inc_nd_forks] terminates *)
  Lemma twp_iter_inc_nd_forks {N E d l} {c : nat} : ↑N ⊆ E →
    [[{ ⟦ mul_strm N d l ⟧{nL} }]][nninv_wsats]
      iter_inc_nd_forks d #c #l @ E
    [[{ RET #(); True }]].
  Proof.
    rewrite/= rew_eq_hwf /=. iIntros (??) "#? Φ".
    iInduction c as [|c] "IH"; wp_lam; wp_pures; [by iApply "Φ"|].
    wp_apply twp_fork.
    - wp_apply (twp_iter_inc_nd with "[]"); by [|rewrite/= rew_eq_hwf /=|].
    - wp_pures. have ->: (S c - 1)%Z = c by lia. by iApply "IH".
  Qed.

  (** [iter_inc_nd_forks_nd] terminates *)
  Lemma twp_iter_inc_nd_forks_nd {N E d l} : ↑N ⊆ E →
    [[{ ⟦ mul_strm N d l ⟧{nL} }]][nninv_wsats]
      iter_inc_nd_forks_nd d #l @ E
    [[{ RET #(); True }]].
  Proof.
    rewrite/= rew_eq_hwf /=. iIntros (??) "#? Φ". wp_lam. wp_pures.
    wp_apply twp_ndnat; [done|]. iIntros (?) "_".
    wp_apply (twp_iter_inc_nd_forks with "[]"); by [|rewrite/= rew_eq_hwf /=|].
  Qed.
End verify.
