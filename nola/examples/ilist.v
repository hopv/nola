(** * Infinite shared mutable linked list examples *)

From nola.examples Require Export con.
From nola.rust_lang Require Export notation proofmode.
Import ProeqvNotation FunPRNotation ModwNotation WpwNotation CsemNotation.

Section ilist.
  Context `{!Csem CON JUDG Σ, !Jsem JUDG (iProp Σ), !lrustGS_gen hlc Σ,
    !inv'GS (cifOF CON) Σ, !inv_tokC CON, !inv_tokCS CON JUDG Σ}.
  Implicit Type (Px Qx : cif CON Σ) (Φx Ψx : loc → cif CON Σ) (l : loc).

  (** ** Linked list *)

  (** [cif_ilist]: Formula for a list *)
  Definition ilist_gen N N' (Φx : loc -pr> cif CON Σ)
    (Ilist : loc -pr> cif CON Σ) l : iProp Σ :=
    inv_tok N (Φx l) ∗ inv_tok N' (∃ l', ▷ (l +ₗ 1) ↦ #l' ∗ Ilist l')%cif.
  Definition cif_ilist_gen N N' (Φx : loc -pr> cif CON Σ) Ilist
    : loc -pr> cif CON Σ :=
    λ l, as_cif (λ _, ilist_gen N N' Φx Ilist l).
  #[export] Instance cif_ilist_gen_productive {k N N'} :
    Proper ((≡[<k]≡) ==> (≡[<k]≡) ==> (≡[k]≡)) (cif_ilist_gen N N').
  Proof.
    unfold cif_ilist_gen=>/= ?? eq ?? eq' ?.
    f_equiv; apply cif_inv_tok_productive; (destruct k as [|k]; [done|]);
      [apply eq|]=>/=.
    f_equiv=> ?. by f_equiv.
  Qed.
  #[export] Instance cif_ilist_gen_productive' {N N' Φx} :
    Productive (cif_ilist_gen N N' Φx).
  Proof. move=> ?. exact: cif_ilist_gen_productive. Qed.
  Definition cif_ilist N N' (Φx : loc -pr> cif CON Σ) : loc -pr> cif CON Σ :=
    profix (cif_ilist_gen N N' Φx).
  (** Unfold [cif_ilist] *)
  Lemma cif_ilist_unfold {N N' Φx l} :
    cif_ilist N N' Φx l ≡ cif_ilist_gen N N' Φx (cif_ilist N N' Φx) l.
  Proof. by rewrite /cif_ilist (profix_unfold (f:=cif_ilist_gen _ _ _) l). Qed.
  (** Semantics *)
  Definition ilist N N' Φx := ilist_gen N N' Φx (cif_ilist N N' Φx).
  (** Unfold semantics over [cif_ilist] *)
  Lemma sem_ilist {δ N N' Φx l} :
    cif_sem δ (cif_ilist N N' Φx l) ⊣⊢ ilist N N' Φx l.
  Proof. by rewrite cif_ilist_unfold /= !sem_cif_in /=. Qed.
  (** [cif_ilist] is productive *)
  #[export] Instance cif_ilist_productive {N N'} : Productive (cif_ilist N N').
  Proof. move=> ????. apply profix_preserv=> ?. by f_equiv. Qed.

  (** [cif_ilist_gen] is non-expansive *)
  #[export] Instance cif_ilist_gen_ne {N N'} :
    NonExpansive2 (cif_ilist_gen N N').
  Proof.
    unfold cif_ilist_gen=>/= ??*?*?. (do 3 f_equiv=>//)=> ?. by f_equiv.
  Qed.
  #[export] Instance cif_ilist_gen_proper {N N'} :
    Proper ((≡) ==> (≡) ==> (≡)) (cif_ilist_gen N N').
  Proof. apply ne_proper_2, _. Qed.
  (** [cif_ilist] is non-expansive *)
  #[export] Instance cif_ilist_ne {N N'} : NonExpansive (cif_ilist N N').
  Proof. move=> ????. apply profix_ne=> ???. by f_equiv. Qed.
  #[export] Instance cif_ilist_proper {N N'} :
    Proper ((≡) ==> (≡)) (cif_ilist N N').
  Proof. apply ne_proper, _. Qed.

  (** Turn cyclic references into [ilist] *)
  Lemma twp_new_ilist_cyclic {N N' E Φx l} : ↑N' ⊆ E →
    inv_tok N (Φx l) -∗ (l +ₗ 1) ↦ #l =[inv_wsat ⟦⟧ᶜ]{E}=∗ ilist N N' Φx l.
  Proof.
    iIntros (?) "#$ ↦". iMod inv_tok_alloc_open as "[#$ cl]"=>//=. iApply "cl".
    iExists _. iFrame "↦". rewrite sem_ilist. by iSplit.
  Qed.
  Lemma twp_new_ilist_cyclic2 {N N' E Φx l l'} : ↑N' ⊆ E →
    inv_tok N (Φx l) -∗ inv_tok N (Φx l') -∗ (l +ₗ 1) ↦ #l' -∗ (l' +ₗ 1) ↦ #l
      =[inv_wsat ⟦⟧ᶜ]{E}=∗ ilist N N' Φx l ∗ ilist N N' Φx l'.
  Proof.
    iIntros (?) "#$ #$ ↦ ↦'".
    iMod (inv_tok_alloc_open _ (N'.@ 0)) as "[#l cl]"; [solve_ndisj|].
    iMod (inv_tok_alloc_open _ (N'.@ 1)) as "[#l' cl']"; [solve_ndisj|].
    rewrite !(inv_tok_subset (N:=_.@_)); [iFrame "l l'"|solve_ndisj..]=>/=.
    iMod ("cl'" with "[$↦']"); [|iApply "cl"; iFrame "↦"]; rewrite sem_ilist;
      by iSplit.
  Qed.

  (** Construct [ilist] from the head and tail *)
  Lemma twp_new_ilist_cons {N N' Φx l l'} :
    inv_tok N (Φx l) -∗ (l +ₗ 1) ↦ #l' -∗ ilist N N' Φx l' =[inv_wsat ⟦⟧ᶜ]=∗
      ilist N N' Φx l.
  Proof.
    iIntros "$ ↦ ?". iApply inv_tok_alloc=>/=. iFrame "↦". by rewrite sem_ilist.
  Qed.

  (** Access the tail of a list *)
  Definition tail_ilist : val := λ: ["l"], !ˢᶜ("l" +ₗ #1).
  Lemma twp_tail_list {N N' E Φx l} : ↑N ⊆ E → ↑N' ⊆ E →
    [[{ ilist N N' Φx l }]][inv_wsat ⟦⟧ᶜ]
      tail_ilist [ #l] @ E [[{ l', RET #l'; ilist N N' Φx l' }]].
  Proof.
    iIntros (?? Ψ) "/= [_ #itl] →Ψ". wp_rec. wp_op.
    iMod (inv_tok_acc with "itl") as "/=[(%l' & >↦l' & ltl) cl]"; [done|].
    rewrite sem_ilist. iDestruct "ltl" as "#ltl". wp_read.
    iMod ("cl" with "[$↦l']") as "_". { by rewrite sem_ilist. }
    iModIntro. iApply ("→Ψ" with "ltl").
  Qed.

  (** Iterate over a list *)
  Definition iter_ilist : val := rec: "self" ["f"; "c"; "l"] :=
    if: !"c" ≤ #0 then #☠ else
      "f" ["l"];; "c" <- !"c" - #1;; "self" ["f"; "c"; tail_ilist ["l"]].
  Lemma twp_iter_ilist {N N' E Φx c l} {f : val} {n : nat} : ↑N ⊆ E → ↑N' ⊆ E →
    (∀ l', [[{ inv_tok N (Φx l') }]][inv_wsat ⟦⟧ᶜ] f [ #l'] @ E
      [[{ v, RET v; True }]]) -∗
    [[{ c ↦ #n ∗ ilist N N' Φx l }]][inv_wsat ⟦⟧ᶜ]
      iter_ilist [f; #c; #l] @ E [[{ RET #☠; c ↦ #0 }]].
  Proof.
    iIntros "%% #f /=" (Ψ) "!> [c↦ #l] →Ψ".
    iInduction n as [|m] "IH" forall (l) "l".
    { wp_rec. wp_read. wp_op. wp_if. by iApply "→Ψ". }
    wp_rec. wp_read. wp_op. wp_if. wp_apply "f".
    { iDestruct "l" as "[$ _]". }
    iIntros (?) "_". wp_seq. wp_read. wp_op. wp_write.
    have -> : (S m - 1)%Z = m by lia.
    wp_apply twp_tail_list; [|done..|]=>//. iIntros (l') "#ltl".
    iApply ("IH" with "c↦ →Ψ ltl").
  Qed.

  (** Iterate over a list with two threads *)
  Definition fork2_iter_ilist : val := λ: ["f"; "c'"; "c"; "l"],
    Fork (iter_ilist ["f"; "c'"; "l"]);; iter_ilist ["f"; "c"; "l"].
  Lemma twp_fork2_iter_ilist {N N' E Φx c' c l} {f : val} {m n : nat} :
    ↑N ⊆ E → ↑N' ⊆ E →
    (∀ l', [[{ inv_tok N (Φx l') }]][inv_wsat ⟦⟧ᶜ] f [ #l'] @ E
      [[{ v, RET v; True }]]) -∗
    [[{ c' ↦ #m ∗ c ↦ #n ∗ ilist N N' Φx l }]][inv_wsat ⟦⟧ᶜ]
      fork2_iter_ilist [f; #c'; #c; #l] @ E [[{ RET #☠; c ↦ #0 }]].
  Proof.
    iIntros "%% #f" (Ψ) "!> (↦' & ↦ & #l) →Ψ". wp_rec.
    wp_apply (twp_fork with "[↦']").
    { iApply (twp_mask_mono _ E); [done|].
      wp_apply (twp_iter_ilist with "f [$↦' $l //]"); [done..|]. by iIntros. }
    iIntros. wp_seq. by wp_apply (twp_iter_ilist with "f [$↦ $l //]").
  Qed.

  (** Iterate over an unbounded number of elements of a list with an unbounded
    number of threads *)
  Definition forks_iter_ilist : val := rec: "self" ["f"; "k"; "l"] :=
    if: !"k" ≤ #0 then #☠ else
      Fork (let: "c" := Alloc #1 in "c" <- Ndnat;; iter_ilist ["f"; "c"; "l"]);;
      "k" <- !"k" - #1;; "self" ["f"; "k"; "l"].
  Lemma twp_forks_iter_ilist {N N' E Φx k l} {f : val} {n : nat} :
    (∀ l', [[{ inv_tok N (Φx l') }]][inv_wsat ⟦⟧ᶜ] f [ #l']
      [[{ v, RET v; True }]]) -∗
    [[{ k ↦ #n ∗ ilist N N' Φx l }]][inv_wsat ⟦⟧ᶜ]
      forks_iter_ilist [f; #k; #l] @ E [[{ RET #☠; k ↦ #0 }]].
  Proof.
    iIntros "#f" (Ψ) "!> [↦ #l] →Ψ". iInduction n as [|m] "IH" forall (l) "l".
    { wp_rec. wp_read. wp_op. wp_if. by iApply "→Ψ". }
    wp_rec. wp_read. wp_op. wp_if. wp_apply twp_fork.
    { wp_alloc c as "↦" "†". rewrite heap_pointsto_vec_singleton. wp_let.
      wp_apply twp_ndnat; [done|]. iIntros (?) "_". wp_write.
      wp_apply (twp_iter_ilist with "f [$↦ $l //]"); by [|iIntros]. }
    iIntros. wp_seq. wp_read. wp_op. have -> : (S m - 1)%Z = m by lia. wp_write.
    iApply ("IH" with "↦ →Ψ l").
  Qed.
  Definition nd_forks_iter_ilist : val := λ: ["f"; "l"],
    let: "k" := Alloc #1 in "k" <- Ndnat;; forks_iter_ilist ["f"; "k"; "l"].
  Lemma twp_nd_forks_iter_ilist {N N' E Φx l} {f : val} :
    (∀ l', [[{ inv_tok N (Φx l') }]][inv_wsat ⟦⟧ᶜ] f [ #l']
      [[{ v, RET v; True }]]) -∗
    [[{ ilist N N' Φx l }]][inv_wsat ⟦⟧ᶜ]
      nd_forks_iter_ilist [f; #l] @ E [[{ RET #☠; True }]].
  Proof.
    iIntros "#f" (Ψ) "!> #l →Ψ". wp_rec. wp_alloc k as "↦" "†".
    rewrite heap_pointsto_vec_singleton. wp_let. wp_apply twp_ndnat; [done|].
    iIntros (?) "_". wp_write.
    wp_apply (twp_forks_iter_ilist with "f [$↦ $l //]"). iIntros "_".
    by iApply "→Ψ".
  Qed.

  (** Example invariant: [l] stores a multiple of 3 *)
  Definition cif_mul3 (l : loc) : cif CON Σ := ∃ k : Z, ▷ l ↦ #(3 * k).
  (** Function that atomically increments [l] by 3 *)
  Definition faa3 : val := λ: ["l"], FAA "l" #3.
  (** [faa3] preserves the invariant of [cif_mul3] *)
  Lemma twp_faa3_mul3 {N E l} : ↑N ⊆ E →
    [[{ inv_tok N (cif_mul3 l) }]][inv_wsat ⟦⟧ᶜ] faa3 [ #l] @ E
    [[{ v, RET v; True }]].
  Proof.
    iIntros (??) "i →Φ". wp_rec.
    iMod (inv_tok_acc with "i") as "/=[[%k >↦] cl]"; [done|].
    wp_apply (twp_faa with "↦"). iIntros "↦".
    have ->: 3 * k + 3 = 3 * (k + 1) by lia. iMod ("cl" with "[$↦]"). iModIntro.
    by iApply "→Φ".
  Qed.
  (** On [iter_ilist] *)
  Lemma twp_iter_ilist_faa3_mul3 {N N' E c l} {n : nat} : ↑N ⊆ E → ↑N' ⊆ E →
    [[{ c ↦ #n ∗ ilist N N' cif_mul3 l }]][inv_wsat ⟦⟧ᶜ]
      iter_ilist [faa3; #c; #l] @ E
    [[{ RET #☠; c ↦ #0 }]].
  Proof.
    move=> ??. iApply (twp_iter_ilist with "[]")=>//. iIntros (??).
    by iApply twp_faa3_mul3.
  Qed.
  Lemma twp_fork2_iter_ilist_faa3_mul3 {N N' E c' c l} {m n : nat} :
    ↑N ⊆ E → ↑N' ⊆ E →
    [[{ c' ↦ #m ∗ c ↦ #n ∗ ilist N N' cif_mul3 l }]][inv_wsat ⟦⟧ᶜ]
      fork2_iter_ilist [faa3; #c'; #c; #l] @ E [[{ RET #☠; c ↦ #0 }]].
  Proof.
    move=> ??. iApply (twp_fork2_iter_ilist with "[]")=>//. iIntros (??).
    by iApply twp_faa3_mul3.
  Qed.
  Lemma twp_forks_iter_ilist_faa3_mul3 {N N' E k l} {n : nat} :
    ↑N ⊆ E → ↑N' ⊆ E →
    [[{ k ↦ #n ∗ ilist N N' cif_mul3 l }]][inv_wsat ⟦⟧ᶜ]
      forks_iter_ilist [faa3; #k; #l] @ E [[{ RET #☠; k ↦ #0 }]].
  Proof.
    move=> ??. iApply (twp_forks_iter_ilist with "[]")=>//. iIntros (??).
    by iApply twp_faa3_mul3.
  Qed.
  Lemma twp_nd_forks_iter_ilist_faa3_mul3 {N N' E l} : ↑N ⊆ E → ↑N' ⊆ E →
    [[{ ilist N N' cif_mul3 l }]][inv_wsat ⟦⟧ᶜ]
      nd_forks_iter_ilist [faa3; #l] @ E [[{ RET #☠; True }]].
  Proof.
    move=> ??. iApply (twp_nd_forks_iter_ilist with "[]")=>//. iIntros (??).
    by iApply twp_faa3_mul3.
  Qed.
End ilist.
