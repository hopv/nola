(** * Infinite shared mutable linked list examples *)

From nola.examples Require Export con.
From nola.rust_lang Require Export notation proofmode.
Import FunPRNotation WpwNotation DsemNotation.

Section ilist.
  Context `{!Csem CON JUDG Σ, !Jsem JUDG (iProp Σ), !lrustGS_gen hlc Σ,
    !inv'GS (cifOF CON) Σ, !inv_tokC CON, !inv_tokCS CON JUDG Σ}.
  Implicit Type (Px Qx : cif CON Σ) (Φx Ψx : loc → cif CON Σ) (l : loc).

  (** ** Linked list *)

  (** [cif_ilist]: Formula for a list *)
  Definition ilist_gen N (Φx : loc -pr> cif CON Σ)
    (Ilist : loc -pr> cif CON Σ) l : iProp Σ :=
    inv_tok N (Φx l) ∗ inv_tok N (∃ l', ▷ (l +ₗ 1) ↦ #l' ∗ Ilist l')%cif.
  Definition cif_ilist_gen N (Φx : loc -pr> cif CON Σ) Ilist
    : loc -pr> cif CON Σ :=
    λ l, as_cif (λ _, ilist_gen N Φx Ilist l).
  #[export] Instance cif_ilist_gen_productive {k N} :
    Proper (proeq_later k ==> proeq_later k ==> proeq k) (cif_ilist_gen N).
  Proof.
    unfold cif_ilist_gen=>/= ?? eq ?? eq' ?.
    f_equiv; apply cif_inv_tok_productive; (destruct k as [|k]; [done|]);
      [apply eq|]=>/=.
    f_equiv=> ?. by f_equiv.
  Qed.
  #[export] Instance cif_ilist_gen_productive' {N Φx} :
    Productive (cif_ilist_gen N Φx).
  Proof. move=> ?. by apply cif_ilist_gen_productive. Qed.
  Definition cif_ilist N (Φx : loc -pr> cif CON Σ) : loc -pr> cif CON Σ :=
    profix (cif_ilist_gen N Φx).
  (** Unfold [cif_ilist] *)
  Lemma cif_ilist_unfold {N Φx l} :
    cif_ilist N Φx l ≡ cif_ilist_gen N Φx (cif_ilist N Φx) l.
  Proof. by rewrite /cif_ilist (profix_unfold (f:=cif_ilist_gen _ _) l). Qed.
  (** Semantics *)
  Definition ilist N Φx := ilist_gen N Φx (cif_ilist N Φx).
  (** Unfold semantics over [cif_ilist] *)
  Lemma sem_ilist {δ N Φx l} : cif_sem δ (cif_ilist N Φx l) ⊣⊢ ilist N Φx l.
  Proof. by rewrite cif_ilist_unfold /= !sem_cif_in /=. Qed.
  (** [cif_ilist] is productive *)
  #[export] Instance cif_ilist_productive {N} : Productive (cif_ilist N).
  Proof. move=> ????. apply profix_preserv=> ?. by f_equiv. Qed.

  (** [cif_ilist_gen] is non-expansive *)
  #[export] Instance cif_ilist_gen_ne {N} : NonExpansive2 (cif_ilist_gen N).
  Proof.
    unfold cif_ilist_gen=>/= ??*?*?. (do 3 f_equiv=>//)=> ?. by f_equiv.
  Qed.
  #[export] Instance cif_ilist_gen_proper {N} :
    Proper ((≡) ==> (≡) ==> (≡)) (cif_ilist_gen N).
  Proof. apply ne_proper_2, _. Qed.
  (** [cif_ilist] is non-expansive *)
  #[export] Instance cif_ilist_ne {N} : NonExpansive (cif_ilist N).
  Proof. move=> ????. apply profix_ne=> ???. by f_equiv. Qed.
  #[export] Instance cif_ilist_proper {N} :
    Proper ((≡) ==> (≡)) (cif_ilist N).
  Proof. apply ne_proper, _. Qed.

  (** Access the tail of a list *)
  Definition tail_ilist : val := λ: ["l"], !ˢᶜ("l" +ₗ #1).
  Lemma twp_tail_list {N E Φx l} : ↑N ⊆ E →
    [[{ ilist N Φx l }]][inv_wsat ⟦⟧]
      tail_ilist [ #l] @ E
    [[{ l', RET #l'; ilist N Φx l' }]].
  Proof.
    iIntros (? Ψ) "/= [_ #itl] →Ψ". wp_rec. wp_op.
    iMod (inv_tok_acc with "itl") as "/=[(%l' & >↦l' & ltl) cl]"; [done|].
    rewrite sem_ilist. iDestruct "ltl" as "#ltl". wp_read.
    iMod ("cl" with "[$↦l']") as "_". { by rewrite sem_ilist. }
    iModIntro. iApply ("→Ψ" with "ltl").
  Qed.

  (** Iterate over a list *)
  Definition iter_ilist : val := rec: "self" ["f"; "c"; "l"] :=
    if: !"c" ≤ #0 then #☠ else
      "f" ["l"];; "c" <- !"c" - #1;; "self" ["f"; "c"; tail_ilist ["l"]].
  Lemma twp_iter_list {N E Φx c l} {f : val} {n : nat} : ↑N ⊆ E →
    (∀ l', [[{ inv_tok N (Φx l') }]][inv_wsat ⟦⟧] f [ #l'] @ E
      [[{ RET #☠; True }]]) -∗
    [[{ c ↦ #n ∗ ilist N Φx l }]][inv_wsat ⟦⟧]
      iter_ilist [f; #c; #l] @ E
    [[{ RET #☠; c ↦ #0 }]].
  Proof.
    iIntros "% #f /=" (Ψ) "!> [c↦ #l] →Ψ".
    iInduction n as [|m] "IH" forall (l) "l".
    { wp_rec. wp_read. wp_op. wp_if. by iApply "→Ψ". }
    wp_rec. wp_read. wp_op. wp_if. wp_apply "f".
    { iDestruct "l" as "[$ _]". }
    iIntros "_". wp_seq. wp_read. wp_op. wp_write.
    have -> : (S m - 1)%Z = m by lia.
    wp_apply twp_tail_list; [done..|]. iIntros (l') "#ltl".
    iApply ("IH" with "c↦ →Ψ ltl").
  Qed.

  (** Iterate over a list with two threads *)
  Lemma twp_fork_iter_list {N E Φx c' c l} {f : val} {m n : nat} : ↑N ⊆ E →
    (∀ l', [[{ inv_tok N (Φx l') }]][inv_wsat ⟦⟧] f [ #l'] @ E
      [[{ RET #☠; True }]]) -∗
    [[{ c' ↦ #m ∗ c ↦ #n ∗ ilist N Φx l }]][inv_wsat ⟦⟧]
      Fork (iter_ilist [f; #c'; #l]);; iter_ilist [f; #c; #l] @ E
    [[{ RET #☠; c ↦ #0 }]].
  Proof.
    iIntros "% #f" (Ψ) "!> (↦' & ↦ & #l) →Ψ". wp_apply (twp_fork with "[↦']").
    { iApply (twp_mask_mono _ E); [done|].
      wp_apply (twp_iter_list with "f [$↦' $l //]"); [done|]. by iIntros. }
    iIntros. wp_seq. by wp_apply (twp_iter_list with "f [$↦ $l //]").
  Qed.

  (** Iterate over an unbounded number of elements of a list with an unbounded
    number of threads *)
  Definition forks_iter_list : val := rec: "self" ["f"; "k"; "l"] :=
    if: !"k" ≤ #0 then #☠ else
      Fork (let: "c" := Alloc #1 in "c" <- Ndnat;; iter_ilist ["f"; "c"; "l"]);;
      "k" <- !"k" - #1;; "self" ["f"; "k"; "l"].
  Lemma twp_forks_iter_list {N E Φx k l} {f : val} {n : nat} :
    (∀ l', [[{ inv_tok N (Φx l') }]][inv_wsat ⟦⟧] f [ #l']
      [[{ RET #☠; True }]]) -∗
    [[{ k ↦ #n ∗ ilist N Φx l }]][inv_wsat ⟦⟧]
      forks_iter_list [f; #k; #l] @ E
    [[{ RET #☠; k ↦ #0 }]].
  Proof.
    iIntros "#f" (Ψ) "!> [↦ #l] →Ψ". iInduction n as [|m] "IH" forall (l) "l".
    { wp_rec. wp_read. wp_op. wp_if. by iApply "→Ψ". }
    wp_rec. wp_read. wp_op. wp_if. wp_apply twp_fork.
    { wp_alloc c as "↦" "†". rewrite heap_pointsto_vec_singleton. wp_let.
      wp_apply twp_ndnat; [done|]. iIntros (?) "_". wp_write.
      wp_apply (twp_iter_list with "f [$↦ $l //]"); by [|iIntros]. }
    iIntros. wp_seq. wp_read. wp_op. have -> : (S m - 1)%Z = m by lia. wp_write.
    iApply ("IH" with "↦ →Ψ l").
  Qed.
  Lemma twp_nd_forks_iter_list {N E Φx l} {f : val} :
    (∀ l', [[{ inv_tok N (Φx l') }]][inv_wsat ⟦⟧] f [ #l']
      [[{ RET #☠; True }]]) -∗
    [[{ ilist N Φx l }]][inv_wsat ⟦⟧]
      let: "k" := Alloc #1 in "k" <- Ndnat;; forks_iter_list [f; "k"; #l] @ E
    [[{ RET #☠; True }]].
  Proof.
    iIntros "#f" (Ψ) "!> #l →Ψ". wp_alloc k as "↦" "†".
    rewrite heap_pointsto_vec_singleton. wp_let. wp_apply twp_ndnat; [done|].
    iIntros (?) "_". wp_write.
    wp_apply (twp_forks_iter_list with "f [$↦ $l //]"). iIntros "_".
    by iApply "→Ψ".
  Qed.
End ilist.
