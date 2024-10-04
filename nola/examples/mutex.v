(** * Mutex borrow examples *)

From nola.examples Require Export nsynty con.
From nola.rust_lang Require Export notation proofmode.
Import FunPRNotation UpdwNotation WpwNotation DsemNotation LftNotation
  NsyntyNotation.

Section mutex_bor.
  Context `{!lrustGS_gen hlc Σ, !SemCifcon JUDG CON Σ, !Jsem JUDG (iProp Σ),
    !inv'GS (cifOF CON) Σ, !InvCon CON, !InvSem JUDG CON Σ,
    !pborrowGS nsynty (cifOF CON) Σ, !BorCon CON, !BorSem JUDG CON Σ}.
  Implicit Type (Px Qx : cif CON Σ) (Φx Ψx : loc → cif CON Σ) (b : bool)
    (l : loc).

  (** ** Mutex operations *)
  (** Try to acquire the lock on the mutex *)
  Definition try_acquire_mutex : val := λ: ["l"], CAS "l" #false #true.
  (** Try to acquire the lock on the mutex repeatedly with a timeout *)
  Definition try_acquire_loop_mutex : val :=
    rec: "self" ["n"; "l"] :=
      if: "n" = #0 then #false else
      if: try_acquire_mutex ["l"] then #true else "self" ["n" - #1; "l"].
  (** Release the lock on the mutex *)
  Definition release_mutex : val := λ: ["l"], "l" <-ˢᶜ #false.

  (** Shared borrow of a mutex *)
  Definition cif_mutex_bor' α l Px :=
    cif_bor α ((▷ l ↦ #false ∗ cif_bor α Px) ∨ ▷ l ↦ #true).
  Definition mutex_bor α l Px := inv_tok nroot (cif_mutex_bor' α l Px).
  Definition cif_mutex_bor α l Px := as_cif (λ _, mutex_bor α l Px).
  (** [cif_mutex_bor'] is productive *)
  #[export] Instance cif_mutex_bor'_productive {α l} :
    Productive (cif_mutex_bor' α l).
  Proof.
    unfold cif_mutex_bor'=> n ?? eq. f_equiv. destruct n as [|n]=>//=.
    do 3 f_equiv. move: eq. apply proeq_later_anti. lia.
  Qed.
  #[export] Instance cif_mutex_bor_productive {α l} :
    Productive (cif_mutex_bor α l).
  Proof.
    unfold cif_mutex_bor=>/= n ?? eq. f_equiv. destruct n as [|n]=>//=. f_equiv.
    move: eq. apply proeq_later_anti. lia.
  Qed.
  (** [cif_mutex_bor'] is non-expansive *)
  #[export] Instance cif_mutex_bor'_ne {α l} :
    NonExpansive (cif_mutex_bor' α l).
  Proof. solve_proper. Qed.
  #[export] Instance cif_mutex_bor'_proper {α l} :
    Proper ((≡) ==> (≡)) (cif_mutex_bor' α l).
  Proof. apply ne_proper, _. Qed.
  #[export] Instance cif_mutex_bor_ne {α l} : NonExpansive (cif_mutex_bor α l).
  Proof. solve_proper. Qed.
  #[export] Instance cif_mutex_bor_proper {α l} :
    Proper ((≡) ==> (≡)) (cif_mutex_bor α l).
  Proof. apply ne_proper, _. Qed.

  (** Try to acquire a lock from a shared borrow over a mutex *)
  Lemma mutex_bor_try_acquire {α l Px q} :
    [[{ mutex_bor α l Px ∗ q.[α] }]][inv_wsat ⟦⟧ ∗ pborrow_wsat bupd_0 ⟦⟧]
      try_acquire_mutex [ #l]
    [[{ b, RET #b; (if b then nbor_tok α Px else True) ∗ q.[α] }]].
  Proof.
    iIntros (Φ) "[#m [α α']] →Φ". wp_lam.
    iMod (inv_tok_acc with "m") as "/=[b cl]"; [done|]. rewrite sem_ecustom /=.
    iMod (nbor_tok_open (M:=bupd_0) with "α b") as "[o big]".
    rewrite /= sem_ecustom.
    iDestruct "big" as "[[>↦ b']|>↦]";
      [wp_apply (twp_cas_suc with "↦")|wp_apply (twp_cas_int_fail with "↦")]
      =>//; iIntros "↦";
      (iMod (nobor_tok_close (M:=bupd_0) with "o [↦]") as "[α b]"=>/=;
        [by iFrame|]);
      iMod ("cl" with "b") as "_"; iModIntro; iApply "→Φ"; by iFrame.
  Qed.
  (** [mutex_bor_try_acquire], repeatedly with a timeout *)
  Lemma mutex_bor_try_acquire_loop {α l Px q} {n : nat} :
    [[{ mutex_bor α l Px ∗ q.[α] }]][inv_wsat ⟦⟧ ∗ pborrow_wsat bupd_0 ⟦⟧]
      try_acquire_loop_mutex [ #n; #l]
    [[{ b, RET #b; (if b then nbor_tok α Px else True) ∗ q.[α] }]].
  Proof.
    iIntros (Φ) "[#l α] →Φ". iInduction n as [|n] "IH".
    { wp_lam. wp_op. wp_if. iApply "→Φ". by iFrame. }
    wp_lam. wp_op. wp_if. wp_apply (mutex_bor_try_acquire with "[$l $α //]").
    iIntros ([|]).
    - iIntros "?". wp_if. by iApply "→Φ".
    - iIntros "[_ α]". wp_if. wp_op. have ->: (S n - 1)%Z = n by lia.
      iApply ("IH" with "α →Φ").
  Qed.

  (** Release a lock from a shared borrow over a mutex *)
  Lemma mutex_bor_release {α l Px q} :
    [[{ mutex_bor α l Px ∗ nbor_tok α Px ∗ q.[α] }]]
      [inv_wsat ⟦⟧ ∗ pborrow_wsat bupd_0 ⟦⟧]
      release_mutex [ #l]
    [[{ RET #☠; q.[α] }]].
  Proof.
    iIntros (Φ) "(#m & b' & α) →Φ". wp_lam.
    iMod (inv_tok_acc with "m") as "/=[b cl]"; [done|].
    rewrite sem_ecustom /=.
    iMod (nbor_tok_open (M:=bupd_0) with "α b") as "[o big]"=>/=.
    iAssert (∃ b, ▷ l ↦ #b)%I with "[big]" as (?) ">↦".
    { iDestruct "big" as "[[$ _]|$]". }
    wp_write.
    iMod (nobor_tok_close (M:=bupd_0) with "o [b' ↦]") as "[α b]"=>/=.
    { iLeft. rewrite sem_ecustom /=. iFrame. }
    iMod ("cl" with "b") as "_". iModIntro. by iApply "→Φ".
  Qed.

  (** Create a shared borrow and a lender of a mutex *)
  Lemma mutex_bor_lend_new {α l Px b q} :
    l ↦ #b -∗ ⟦ Px ⟧ -∗ q.[α] =[inv_wsat ⟦⟧ ∗ pborrow_wsat bupd_0 ⟦⟧]=∗◇
      mutex_bor α l Px ∗ nlend_tok α (∃ b', ▷ l ↦ #b' ∗ Px)%cif ∗ q.[α].
  Proof.
    iIntros "↦ Px α".
    iMod (nbor_nlend_tok_new (M:=bupd_0) with "[↦ Px]") as "[b $]";
      [by iFrame|].
    iMod (nbor_tok_open (M:=bupd_0) with "α b") as "/=[o[%b'[↦ Px]]]".
    iMod (nobor_tok_subdiv (FML:=cifOF CON) (M:=bupd_0)
      [∃ b', ▷ l ↦ #b'; Px]%cif with "[] o [↦ Px] []")
      as "(α & _ & (b & b' & _))"=>/=.
    { iApply lft_sincl_refl. } { iSplitL "↦"; iFrame. }
    { by iIntros "_ [[% $][$ _]]". }
    iMod (nbor_tok_open (M:=bupd_0) with "α b") as "/=[o ↦]".
    iMod (nobor_tok_subdiv (FML:=cifOF CON) (M:=bupd_0)
      [(▷ l ↦ #false ∗ cif_bor α Px) ∨ ▷ l ↦ #true]%cif with "[] o [↦ b'] []")
      as "($ & _ & [b _])"=>/=. { iApply lft_sincl_refl. }
    { iSplit; [|done]. rewrite sem_ecustom /=.
      iDestruct "↦" as ([|]) "↦"; [|iLeft]; iFrame. }
    { by iIntros "_ [[[$ _]|$]_]". }
    iMod (inv_tok_alloc with "[b]") as "$"=>//=. by rewrite sem_ecustom.
  Qed.

  (** ** Linked list with a shared borrow over a mutex *)

  (** [cif_mblist]: Formula for a list with a shared borrow over a mutex *)
  Definition mblist_gen α (Φx : loc -pr> cif CON Σ)
    (Mblist : loc -pr> cif CON Σ) l : iProp Σ :=
    mutex_bor α l (Φx (l +ₗ 1) ∗ ∃ l', ▷ (l +ₗ 2) ↦ #l' ∗ Mblist l').
  Definition cif_mblist_gen α Φx Mblist : loc -pr> cif CON Σ :=
    λ l, as_cif (λ _, mblist_gen α Φx Mblist l).
  #[export] Instance cif_mblist_gen_productive {α Φx} :
    Productive (cif_mblist_gen α Φx).
  Proof.
    move=>/= k ?? eq ?. unfold cif_mblist_gen. apply cif_mutex_bor_productive.
    destruct k as [|k]=>//=. (do 2 f_equiv)=> ?. f_equiv. apply eq.
  Qed.
  Definition cif_mblist α Φx : loc → cif CON Σ :=
    profix (cif_mblist_gen α Φx).
  (** Unfold [cif_mblist] *)
  Lemma cif_mblist_unfold {α Φx l} :
    cif_mblist α Φx l ≡ cif_mblist_gen α Φx (cif_mblist α Φx) l.
  Proof. by rewrite /cif_mblist (profix_unfold (f:=cif_mblist_gen _ _) l). Qed.
  (** Semantics *)
  Definition mblist α Φx := mblist_gen α Φx (cif_mblist α Φx).
  (** Unfold semantics over [cif_ilist] *)
  Lemma sem_mblist {δ α Φx l} : cif_sem δ (cif_mblist α Φx l) ⊣⊢ mblist α Φx l.
  Proof. by rewrite cif_mblist_unfold !sem_ecustom /=. Qed.

  (** Iterate over [cif_mblist] *)
  Definition iter_mblist : val := rec: "self" ["f"; "k"; "c"; "l"] :=
    if: !"c" ≤ #0 then #true else
      if: try_acquire_loop_mutex ["k"; "l"] then
        "f" ["l" +ₗ #1];; let: "l'" := !("l" +ₗ #2) in release_mutex ["l"];;
        "c" <- !"c" - #1;; "self" ["f"; "k"; "c"; "l'"]
      else #false.
  Lemma twp_iter_mblist {α Φx c l q} {f : val} {k n : nat} :
    (∀ l', [[{ ⟦ Φx (l' +ₗ 1) ⟧ }]][inv_wsat ⟦⟧ ∗ pborrow_wsat bupd_0 ⟦⟧]
        f [ #(l' +ₗ 1)] [[{ RET #☠; ⟦ Φx (l' +ₗ 1) ⟧ }]]) -∗
    [[{ c ↦ #n ∗ mblist α Φx l ∗ q.[α] }]]
      [inv_wsat ⟦⟧ ∗ pborrow_wsat bupd_0 ⟦⟧]
      iter_mblist [f; #k; #c; #l]
    [[{ b, RET #b; (if b then c ↦ #0 else ∃ n', c ↦ #n') ∗ q.[α] }]].
  Proof.
    iIntros "#f" (Ψ) "!> (c↦ & #m & α) →Ψ".
    iInduction n as [|m] "IH" forall (l) "m"=>/=.
    { wp_rec. wp_read. wp_op. wp_if. iApply "→Ψ". by iFrame. }
    wp_rec. wp_read. wp_op. wp_if.
    wp_apply (mutex_bor_try_acquire_loop with "[$m $α //]").
    iIntros ([|])=>/=; last first.
    { iIntros "[_ α]". wp_if. iApply "→Ψ". iFrame. }
    iIntros "[b α]". wp_if. wp_op.
    iMod (nbor_tok_open (M:=bupd_0) with "α b")
      as "/=[o (Φx & %l' & >↦ & mtl)]".
    rewrite sem_mblist. iDestruct "mtl" as "#mtl". wp_apply ("f" with "Φx").
    iIntros "Φx". wp_seq. wp_op. wp_read. wp_seq.
    iMod (nobor_tok_close (M:=bupd_0) with "o [Φx ↦]") as "[α b]"=>/=.
    { iFrame. by rewrite sem_mblist. }
    wp_apply (mutex_bor_release with "[$b $α //]"). iIntros "α". wp_seq.
    wp_read. wp_op. wp_write. have -> : (S m - 1)%Z = m by lia.
    iApply ("IH" with "c↦ α →Ψ mtl").
  Qed.
End mutex_bor.
