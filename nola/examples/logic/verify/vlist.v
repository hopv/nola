(** * Verification on singly linked lists with values *)

From nola.examples.logic Require Export inv.
From nola.examples.heap_lang Require Export notation.

(** List whose elements satisfy the pure condition [φ] *)
Fixpoint vlist {κ Γ} (N : namespace) (φ : Z → Prop) (ns : list Z) (l : loc)
  : nProp κ Γ :=
  match ns with [] => True | n :: ns =>
    n_inv N (⌜φ n⌝ ∗ l ↦ # n) ∗
      n_inv N (∃ l' : loc, (l +ₗ 1) ↦ # l' ∗ vlist N φ ns l') end.

(** Interpretaion of [vlist] *)
Definition vlisti `{!nintpGS Σ} δ N φ (ns : list Z) l
  : iProp Σ :=
  match ns with [] => True | n :: ns =>
    ninv δ N (⌜φ n⌝ ∗ l ↦ # n) ∗
      ninv δ N (∃ l' : loc, (l +ₗ 1) ↦ # l' ∗ vlist N φ ns l') end.
Notation vlistis := (vlisti nderiv).

Section verify.
  Context `{!nintpGS Σ}.

  #[export] Instance vlisti_pers {δ N φ ns l} :
    Persistent (vlisti δ N φ ns l).
  Proof. case ns; exact _. Qed.

  Lemma vlist_vlisti {κ N φ ns l δ} :
    ⟦ vlist N φ ns l ⟧{κ}(δ) ⊣⊢ vlisti δ N φ ns l.
  Proof. by case ns. Qed.

  Lemma vlist_all {E N φ ns l} : ↑ N ⊆ E → ↑ N ⊆ E →
    vlistis N φ ns l =[inv_wsatd]{E}=∗ ⌜Forall φ ns⌝.
  Proof.
    move=> ?. move: l. elim ns; [iPureIntro=>/= ??; by apply Forall_nil|].
    iIntros (?? IH ??) "[#ihd #itl]".
    iMod (ninv_acc with "ihd") as "/=[[% ↦] cl]"; [done|].
    iMod ("cl" with "[$↦//]") as "_".
    iMod (ninv_acc with "itl") as "/=[(%& ↦ & vl) cl]"; [done|].
    rewrite vlist_vlisti. iDestruct "vl" as "#?". iMod ("cl" with "[↦]") as "_".
    { iExists _. rewrite vlist_vlisti. by iFrame. }
    iMod (IH with "[//]") as %?; [done|]. iPureIntro. by constructor.
  Qed.
End verify.
