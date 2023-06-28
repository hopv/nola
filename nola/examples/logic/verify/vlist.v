(** * Verification on singly linked lists with values *)

From nola.examples.logic Require Export inv.
From nola.examples.heap_lang Require Export notation.

(** List whose elements satisfy the pure condition [φ] *)
Fixpoint vlist {κ Γ} (N N' : namespace) (φ : Z → Prop) (ns : list Z) (l : loc)
  : nProp κ Γ :=
  match ns with [] => True | n :: ns =>
    n_inv 0 N (⌜φ n⌝ ∗ l ↦ # n) ∗
      n_inv 0 N' (∃ l' : loc, (l +ₗ 1) ↦ # l' ∗ vlist N N' φ ns l') end.

(** Interpretaion of [vlist] *)
Definition vlisti `{!nintpGS Σ} s N N' φ (ns : list Z) l
  : iProp Σ :=
  match ns with [] => True | n :: ns =>
    nninv s 0 N (⌜φ n⌝ ∗ l ↦ # n) ∗
      nninv s 0 N' (∃ l' : loc, (l +ₗ 1) ↦ # l' ∗ vlist N N' φ ns l') end.
Notation vlistis := (vlisti nsintp).

Section verify.
  Context `{!nintpGS Σ}.

  #[export] Instance vlisti_pers {s N N' φ ns l} :
    Persistent (vlisti s N N' φ ns l).
  Proof. case ns; exact _. Qed.

  Lemma vlist_vlisti {κ N N' φ ns l s} :
    ⟦ vlist N N' φ ns l ⟧{κ}(s) ⊣⊢ vlisti s N N' φ ns l.
  Proof. by case ns. Qed.

  Lemma vlist_all {E N N' φ ns l} : ↑ N ⊆ E → ↑ N' ⊆ E →
    vlistis N N' φ ns l =[nninv_wsats]{E}=∗ ⌜Forall φ ns⌝.
  Proof.
    move=> ?. move: l. elim ns; [iPureIntro=>/= ??; by apply Forall_nil|].
    iIntros (?? IH ??) "[#ihd #itl]".
    iMod (nninvs_acc with "ihd") as "/=[[% ↦] cl]"; [done|].
    iMod ("cl" with "[$↦//]") as "_".
    iMod (nninvs_acc with "itl") as "/=[(%& ↦ & vl) cl]"; [done|].
    rewrite vlist_vlisti. iDestruct "vl" as "#?". iMod ("cl" with "[↦]") as "_".
    { iExists _. rewrite vlist_vlisti. by iFrame. }
    iMod (IH with "[//]") as %?; [done|]. iPureIntro. by constructor.
  Qed.
End verify.
