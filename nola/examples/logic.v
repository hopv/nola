(** * Main logic *)

From nola.iris Require Export cif inv pborrow.
From nola.bi Require Import util.
From nola.heap_lang Require Export notation proofmode lib.mutex.
From nola.examples Require Export nsynty.
Import ProdNotation UpdwNotation WpwNotation iPropAppNotation PsemNotation
  SemNotation ProphNotation LftNotation NsyntyNotation.

Implicit Type (N : namespace) (dq : dfrac) (l : loc) (b : bool) (α β : lft)
  (q : Qp) (X Y : nsynty).

(** ** Preliminaries *)

(** [sel]: Selector *)
Variant sel :=
| (** Points-to token *) cifs_pointsto (l : loc) (dq : dfrac) (v : val)
| (** Invariant *) cifs_inv (N : namespace)
| (** Relaxed invariant *) cifs_inv' (N : namespace)
| (** Mutex *) cifs_mutex (l : loc)
| (** Non-prophetic borrower *) cifs_bor (α : lft)
| (** Non-prophetic open borrower *) cifs_obor (α : lft) (q : Qp)
| (** Non-prophetic lender *) cifs_lend (α : lft)
| (** Prophetic borrower *) cifs_pbor {X} (α : lft) (x : X) (ξ : prvar X)
| (** Prophetic open borrower *) cifs_pobor {X} (α : lft) (q : Qp) (ξ : prvar X)
| (** Prophetic lender *) cifs_plend {X} (α : lft) (xπ : clair nsynty X).
(** [idom]: Domain for inductive parts *)
Definition idom (_ : sel) : Type := Empty_set.
(** [cdom]: Domain for coinductive parts *)
Definition cdom (s : sel) : Type := match s with
  | cifs_pointsto _ _ _ => Empty_set
  | cifs_inv _ | cifs_inv' _ | cifs_mutex _
    | cifs_bor _ | cifs_obor _ _ | cifs_lend _ => unit
  | @cifs_pbor X _ _ _ | @cifs_pobor X _ _ _ | @cifs_plend X _ _ => X
  end.
(** [dataOF]: Data [oFunctor] *)
Definition dataOF (_ : sel) : oFunctor := unitO.
(** [dataOF] is contractive *)
#[export] Instance dataOF_contractive {s} : oFunctorContractive (dataOF s).
Proof. exact _. Qed.

(** ** [cif]: Formulas *)
Notation cif Σ := (cif idom cdom dataOF Σ).
Notation cifOF := (cifOF idom cdom dataOF).

(** [cifOF] is contractive *)
#[export] Instance cifOF_contractive : oFunctorContractive cifOF.
Proof. exact _. Qed.

(** Construct [cif] *)
Section cif.
  Context {Σ : gFunctors}.
  Implicit Type Px : cif Σ.
  (** Points-to token *)
  Definition cif_pointsto l dq v : cif Σ :=
    cif_custom (D:=dataOF) (cifs_pointsto l dq v) nullary nullary ().
  (** Invariant *)
  Definition cif_inv N Px : cif Σ :=
    cif_custom (cifs_inv N) nullary (unary Px) ().
  (** Relaxed invariant *)
  Definition cif_inv' N Px : cif Σ :=
    cif_custom (cifs_inv' N) nullary (unary Px) ().
  (** Mutex *)
  Definition cif_mutex l Px : cif Σ :=
    cif_custom (cifs_mutex l) nullary (unary Px) ().
  (** Non-prophetic borrower *)
  Definition cif_bor α Px : cif Σ :=
    cif_custom (cifs_bor α) nullary (unary Px) ().
  (** Non-prophetic open borrower *)
  Definition cif_obor α q Px : cif Σ :=
    cif_custom (cifs_obor α q) nullary (unary Px) ().
  (** Non-prophetic lender *)
  Definition cif_lend α Px : cif Σ :=
    cif_custom (cifs_lend α) nullary (unary Px) ().
  (** Prophetic borrower *)
  Definition cif_pbor {X} α x ξ (Φx : X -d> cif Σ) : cif Σ :=
    cif_custom (@cifs_pbor X α x ξ) nullary Φx ().
  (** Prophetic open borrower *)
  Definition cif_pobor {X} α q ξ (Φx : X -d> cif Σ) : cif Σ :=
    cif_custom (@cifs_pobor X α q ξ) nullary Φx ().
  (** Prophetic lender *)
  Definition cif_plend {X} α xπ (Φx : X -d> cif Σ) : cif Σ :=
    cif_custom (@cifs_plend X α xπ) nullary Φx ().

  (** The custom constructors are productive *)
  #[export] Instance cif_inv_productive {N} : Productive (cif_inv N).
  Proof.
    move=> n ???. apply cif_custom_preserv_productive=>//. by destruct n=> >.
  Qed.
  #[export] Instance cif_inv'_productive  {N} : Productive (cif_inv' N).
  Proof.
    move=> n ???. apply cif_custom_preserv_productive=>//. by destruct n=> >.
  Qed.
  #[export] Instance cif_mutex_productive {l} : Productive (cif_mutex l).
  Proof.
    move=> n ???. apply cif_custom_preserv_productive=>//. by destruct n=> >.
  Qed.
  #[export] Instance cif_bor_productive {α} : Productive (cif_bor α).
  Proof.
    move=> n ???. apply cif_custom_preserv_productive=>//. by destruct n=> >.
  Qed.
  #[export] Instance cif_obor_productive {α q} : Productive (cif_obor α q).
  Proof.
    move=> n ???. apply cif_custom_preserv_productive=>//. by destruct n=> >.
  Qed.
  #[export] Instance cif_lend_productive {α} : Productive (cif_lend α).
  Proof.
    move=> n ???. apply cif_custom_preserv_productive=>//. by destruct n=> >.
  Qed.
  #[export] Instance cif_pbor_productive {X α x ξ} :
    Productive' (funPR (λ _, cif _)) _ (@cif_pbor X α x ξ).
  Proof. move=> ????. by apply cif_custom_preserv_productive. Qed.
  #[export] Instance cif_pobor_productive {X α q ξ} :
    Productive' (funPR (λ _, cif _)) _ (@cif_pobor X α q ξ).
  Proof. move=> ????. by apply cif_custom_preserv_productive. Qed.
  #[export] Instance cif_plend_productive {X α xπ} :
    Productive' (funPR (λ _, cif _)) _ (@cif_plend X α xπ).
  Proof. move=> ????. by apply cif_custom_preserv_productive. Qed.

  (** The custom constructors are non-expansive *)
  #[export] Instance cif_inv_ne {N} : NonExpansive (cif_inv N).
  Proof. move=> ????. apply cif_custom_ne; solve_proper. Qed.
  #[export] Instance cif_inv_proper {N} : Proper ((≡) ==> (≡)) (cif_inv N).
  Proof. apply ne_proper, _. Qed.
  #[export] Instance cif_inv'_ne {N} : NonExpansive (cif_inv' N).
  Proof. move=> ????. apply cif_custom_ne; solve_proper. Qed.
  #[export] Instance cif_inv'_proper {N} : Proper ((≡) ==> (≡)) (cif_inv' N).
  Proof. apply ne_proper, _. Qed.
  #[export] Instance cif_mutex_ne {l} : NonExpansive (cif_mutex l).
  Proof. move=> ????. apply cif_custom_ne; solve_proper. Qed.
  #[export] Instance cif_mutex_proper {l} : Proper ((≡) ==> (≡)) (cif_mutex l).
  Proof. apply ne_proper, _. Qed.
  #[export] Instance cif_bor_ne {α} : NonExpansive (cif_bor α).
  Proof. move=> ????. apply cif_custom_ne; solve_proper. Qed.
  #[export] Instance cif_bor_proper {α} : Proper ((≡) ==> (≡)) (cif_bor α).
  Proof. apply ne_proper, _. Qed.
  #[export] Instance cif_obor_ne {α q} : NonExpansive (cif_obor α q).
  Proof. move=> ????. apply cif_custom_ne; solve_proper. Qed.
  #[export] Instance cif_obor_proper {α q} :
    Proper ((≡) ==> (≡)) (cif_obor α q).
  Proof. apply ne_proper, _. Qed.
  #[export] Instance cif_lend_ne {α} : NonExpansive (cif_lend α).
  Proof. move=> ????. apply cif_custom_ne; solve_proper. Qed.
  #[export] Instance cif_lend_proper {α} : Proper ((≡) ==> (≡)) (cif_lend α).
  Proof. apply ne_proper, _. Qed.
  #[export] Instance cif_pbor_ne {X α x ξ} : NonExpansive (@cif_pbor X α x ξ).
  Proof. move=> ????. apply cif_custom_ne; solve_proper. Qed.
  #[export] Instance cif_pbor_proper {X α x ξ} :
    Proper ((≡) ==> (≡)) (@cif_pbor X α x ξ).
  Proof. apply ne_proper, _. Qed.
  #[export] Instance cif_pobor_ne {X α q ξ} : NonExpansive (@cif_pobor X α q ξ).
  Proof. move=> ????. apply cif_custom_ne; solve_proper. Qed.
  #[export] Instance cif_pobor_proper {X α q ξ} :
    Proper ((≡) ==> (≡)) (@cif_pobor X α q ξ).
  Proof. apply ne_proper, _. Qed.
  #[export] Instance cif_plend_ne {X α xπ} : NonExpansive (@cif_plend X α xπ).
  Proof. move=> ????. apply cif_custom_ne; solve_proper. Qed.
  #[export] Instance cif_plend_proper {X α xπ} :
    Proper ((≡) ==> (≡)) (@cif_plend X α xπ).
  Proof. apply ne_proper, _. Qed.
End cif.
Notation "l ↦ dq v" := (cif_pointsto l dq v)
  (at level 20, dq custom dfrac at level 1, format "l  ↦ dq  v") : cif_scope.

(** ** [judg]: Judgment *)
Definition judg Σ : ofe := (cif Σ * cif Σ)%type.

Section sem.
  Context `{!inv'GS cifOF Σ, !mutexGS cifOF Σ, !pborrowGS nsynty cifOF Σ,
    !heapGS_gen hlc Σ}.
  Implicit Type δ : judg Σ → iProp Σ.

  (** Relaxed invariant *)
  Definition inv' δ N Px : iProp Σ := ∃ Qx, δ (Px, Qx) ∗ inv_tok N Qx.
  (** [inv'] is non-expansive *)
  #[export] Instance inv'_ne `{!NonExpansive δ} {N} : NonExpansive (inv' δ N).
  Proof. solve_proper. Qed.
  #[export] Instance inv'_proper `{!NonExpansive δ} {N} :
    Proper ((≡) ==> (⊣⊢)) (inv' δ N).
  Proof. apply ne_proper, _. Qed.

  (** ** [bsem]: Base semantics *)
  Definition bsem δ s :
    (idom s -d> iProp Σ) → (cdom s -d> cif Σ) → dataOF s $oi Σ → iProp Σ :=
    match s with
    | cifs_pointsto l dq v => λ _ _ _, l ↦{dq} v
    | cifs_inv N => λ _ Pxs _, inv_tok N (Pxs ())
    | cifs_inv' N => λ _ Pxs _, inv' δ N (Pxs ())
    | cifs_mutex l => λ _ Pxs _, mutex_tok l (Pxs ())
    | cifs_bor α => λ _ Pxs _, nbor_tok α (Pxs ())
    | cifs_obor α q => λ _ Pxs _, nobor_tok α q (Pxs ())
    | cifs_lend α => λ _ Pxs _, nlend_tok α (Pxs ())
    | cifs_pbor α x ξ => λ _ Φx _, pbor_tok α x ξ Φx
    | cifs_pobor α q ξ => λ _ Φx _, pobor_tok α q ξ Φx
    | cifs_plend α xπ => λ _ Φx _, plend_tok α xπ Φx
    end%I.

  (** [bsem] is non-expansive *)
  #[export] Instance bsem_ne `{!NonExpansive δ} {s} : NonExpansive3 (bsem δ s).
  Proof. case s; try solve_proper; move=> ?*?*?*?*/=; f_equiv; by move: (). Qed.

  (** Parameterized semantics of [cif] *)
  #[export] Instance cif_dsem : Dsem (judg Σ) (cif Σ) (iProp Σ) :=
    DSEM (λ δ, cif_sem (bsem δ)).

  (** [cif_sem] is non-expansive *)
  #[export] Instance cif_sem_ne `{!NonExpansive δ} : NonExpansive ⟦⟧(δ)@{cif Σ}.
  Proof. exact _. Qed.
  #[export] Instance cif_sem_proper `{!NonExpansive δ} :
    Proper ((≡) ==> (⊣⊢)) ⟦⟧(δ)@{cif Σ}.
  Proof. exact _. Qed.

  Context `{!heapGS_gen hlc Σ}.

  (** [judg_sem]: Judgment semantics *)
  Definition judg_sem δ (J : judg Σ) := match J with
    | (Px, Qx) => □ (⟦ Px ⟧(δ) ∗-∗ ⟦ Qx ⟧(δ))
    end%I.
  Local Instance judg_sem_ne `{!NonExpansive δ} : NonExpansive (judg_sem δ).
  Proof. move=> ?[??][??][/=??]. solve_proper. Qed.
  #[export] Instance judg_dsem : Dsem (judg Σ) (judg Σ) (iProp Σ) :=
    DSEM judg_sem.
  Canonical judgJ : judgi (iProp Σ) := Judgi (judg Σ).

  (** Simplify [to_cit (of_cif Px)] *)
  Lemma sem_to_of_cif {Px} : ⟦ to_cit (of_cif Px) ⟧ ⊣⊢ ⟦ Px ⟧.
  Proof. by rewrite to_of_cif. Qed.
End sem.

Notation invd := (inv' der).

Section verify.
  Context `{!inv'GS cifOF Σ, !mutexGS cifOF Σ,
    !pborrowGS nsynty cifOF Σ, !heapGS_gen hlc Σ}.
  Implicit Type (Px Qx : cif Σ) (Φx Ψx : loc → cif Σ).

  (** ** Linked list *)

  (** [ilist]: Formula for a list *)
  Definition ilist_gen N Φx Ilist l : cif Σ :=
    cif_inv N (Φx l) ∗ cif_inv N (∃ l', (l +ₗ 1) ↦ #l' ∗ Ilist l').
  #[export] Instance ilist_gen_productive {N Φx} :
    Productive (ilist_gen N Φx).
  Proof.
    move=>/= n ????. unfold ilist_gen. do 2 f_equiv. destruct n as [|n]=>//=.
    f_equiv=> ?. by f_equiv.
  Qed.
  Definition ilist' N Φx : loc → cif Σ := profix (ilist_gen N Φx).
  Definition ilist N Φx : loc → cif Σ := ilist_gen N Φx (ilist' N Φx).
  (** Unfold [ilist'] *)
  Lemma ilist'_unfold {N Φx l} : ilist' N Φx l ≡ ilist N Φx l.
  Proof.
    move=> ?. apply cit_proeq_all=> n.
    have E : proeq n (ilist' N Φx) (ilist N Φx) by exact profix_unfold. apply E.
  Qed.

  (** Access the tail of a list *)
  Definition tail_ilist : val := λ: "l", !("l" +ₗ #1).
  Lemma twp_tail_list {N E Φx l} : ↑N ⊆ E →
    [[{ ⟦ ilist N Φx l ⟧ }]][inv_wsat ⟦⟧]
      tail_ilist #l @ E
    [[{ l', RET #l'; ⟦ ilist N Φx l' ⟧ }]].
  Proof.
    iIntros (? Ψ) "/= #[_ itl] →Ψ". wp_rec. wp_pure.
    iMod (inv_tok_acc (sm:=⟦⟧) with "itl") as "[↦ltl cl]"; [done|].
    rewrite /=. setoid_rewrite to_of_cif=>/=.
    iDestruct "↦ltl" as (?) "[↦l' ltl]". rewrite ilist'_unfold /=.
    iDestruct "ltl" as "#ltl". wp_load. iModIntro.
    iMod ("cl" with "[$↦l']") as "_"; [by rewrite ilist'_unfold|]. iModIntro.
    rewrite !to_of_cif. iApply ("→Ψ" with "ltl").
  Qed.

  (** Iterate over a list *)
  Definition iter_ilist : val := rec: "self" "f" "c" "l" :=
    if: !"c" ≤ #0 then #() else
      "f" "l";; "c" <- !"c" - #1;; "self" "f" "c" (tail_ilist "l").
  Lemma twp_iter_list {N E Φx c l} {f : val} {n : nat} : ↑N ⊆ E →
    (∀ l', [[{ inv_tok N (Φx l') }]][inv_wsat ⟦⟧] f #l' @ E
      [[{ RET #(); True }]]) -∗
    [[{ c ↦ #n ∗ ⟦ ilist N Φx l ⟧ }]][inv_wsat ⟦⟧]
      iter_ilist f #c #l @ E
    [[{ RET #(); c ↦ #0 }]].
  Proof.
    iIntros "% #f /=" (Ψ) "!> [c↦ #l] →Ψ".
    iInduction n as [|m] "IH" forall (l) "l".
    { wp_rec. wp_load. wp_pures. by iApply "→Ψ". }
    wp_rec. wp_load. wp_pures. wp_apply "f".
    { rewrite to_of_cif. iDestruct "l" as "[$ _]". }
    iIntros "_". wp_load. wp_store. have -> : (S m - 1)%Z = m by lia.
    wp_apply twp_tail_list; [done..|]. iIntros (l') "#ltl".
    iApply ("IH" with "c↦ →Ψ ltl").
  Qed.

  (** Iterate over a list with two threads *)
  Lemma twp_fork_iter_list {N E Φx c' c l} {f : val} {m n : nat} : ↑N ⊆ E →
    (∀ l', [[{ inv_tok N (Φx l') }]][inv_wsat ⟦⟧] f #l' @ E
      [[{ RET #(); True }]]) -∗
    [[{ c' ↦ #m ∗ c ↦ #n ∗ ⟦ ilist N Φx l ⟧ }]][inv_wsat ⟦⟧]
      Fork (iter_ilist f #c' #l);; iter_ilist f #c #l @ E
    [[{ RET #(); c ↦ #0 }]].
  Proof.
    iIntros "% #f" (Ψ) "!> (↦' & ↦ & #l) →Ψ". wp_apply (twp_fork with "[↦']").
    { iApply (twp_mask_mono _ E); [done|].
      wp_apply (twp_iter_list with "f [$↦' $l //]"); [done|]. by iIntros. }
    wp_pures. by wp_apply (twp_iter_list with "f [$↦ $l //]").
  Qed.

  (** Iterate over an unbounded number of elements of a list with an unbounded
    number of threads *)
  Definition forks_iter_list : val := rec: "self" "f" "k" "l" :=
    if: !"k" ≤ #0 then #() else
      Fork (let: "c" := ref Ndnat in iter_ilist "f" "c" "l");;
      "k" <- !"k" - #1;; "self" "f" "k" "l".
  Lemma twp_forks_iter_list {N E Φx k l} {f : val} {n : nat} :
    (∀ l', [[{ inv_tok N (Φx l') }]][inv_wsat ⟦⟧] f #l'
      [[{ RET #(); True }]]) -∗
    [[{ k ↦ #n ∗ ⟦ ilist N Φx l ⟧ }]][inv_wsat ⟦⟧]
      forks_iter_list f #k #l @ E
    [[{ RET #(); k ↦ #0 }]].
  Proof.
    iIntros "#f" (Ψ) "!> [↦ #l] →Ψ". iInduction n as [|m] "IH" forall (l) "l".
    { wp_rec. wp_load. wp_pures. by iApply "→Ψ". }
    wp_rec. wp_load. wp_pures. wp_apply twp_fork.
    { wp_apply twp_ndnat; [done|]. iIntros (?) "_". wp_alloc c as "↦".
      wp_pures. wp_apply (twp_iter_list with "f [$↦ $l //]"); by [|iIntros]. }
    wp_load. wp_op. have -> : (S m - 1)%Z = m by lia. wp_store.
    iApply ("IH" with "↦ →Ψ l").
  Qed.
  Lemma twp_nd_forks_iter_list {N E Φx l} {f : val} :
    (∀ l', [[{ inv_tok N (Φx l') }]][inv_wsat ⟦⟧] f #l'
      [[{ RET #(); True }]]) -∗
    [[{ ⟦ ilist N Φx l ⟧ }]][inv_wsat ⟦⟧]
      let: "k" := ref Ndnat in forks_iter_list f "k" #l @ E
    [[{ RET #(); True }]].
  Proof.
    iIntros "#f" (Ψ) "!> #l →Ψ". wp_apply twp_ndnat; [done|]. iIntros (?) "_".
    wp_alloc k as "↦". wp_pures.
    wp_apply (twp_forks_iter_list with "f [$↦ $l //]"). iIntros "_".
    by iApply "→Ψ".
  Qed.

  (** ** Linked list with a mutex *)

  (** [mlist]: Formula for a list with a mutex *)
  Definition mlist_gen Φx Mlist l : cif Σ :=
    cif_mutex l (Φx (l +ₗ 1) ∗ ∃ l', (l +ₗ 2) ↦ #l' ∗ Mlist l').
  #[export] Instance mlist_gen_productive {Φx} : Productive (mlist_gen Φx).
  Proof.
    move=>/= n ?? eq ?. unfold mlist_gen. f_equiv. destruct n as [|n]=>//=.
    (do 2 f_equiv)=> ?. f_equiv. apply eq.
  Qed.
  Definition mlist' Φx : loc → cif Σ := profix (mlist_gen Φx).
  Definition mlist Φx : loc → cif Σ := mlist_gen Φx (mlist' Φx).
  (** Unfold [mlist'] *)
  Lemma mlist'_unfold {Φx l} : mlist' Φx l ≡ mlist Φx l.
  Proof.
    move=> ?. apply cit_proeq_all=> n.
    have E : proeq n (mlist' Φx) (mlist Φx) by exact profix_unfold. apply E.
  Qed.

  (** Try to acquire the lock of [mlist] *)
  Lemma twp_try_acquire_loop_mlist {Φx l} {k : nat} :
    [[{ ⟦ mlist Φx l ⟧ }]][mutex_wsat ⟦⟧]
      try_acquire_loop_mutex #k #l
    [[{ b, RET #b; if negb b then True else
        ⟦ Φx (l +ₗ 1) ⟧ ∗ ∃ l', (l +ₗ 2) ↦ #l' ∗ ⟦ mlist Φx l' ⟧ }]].
  Proof.
    iIntros (Ψ) "/= #m →Ψ". iApply twp_fupd.
    wp_apply (twp_try_acquire_loop_mutex_tok (sm:=⟦⟧) with "m").
    iIntros ([|]); last first. { iIntros (?). by iApply "→Ψ". }
    rewrite sem_to_of_cif /=. iIntros "[Φx [%[↦ m']]]".
    rewrite mlist'_unfold /=. iApply "→Ψ". by iFrame.
  Qed.

  (** Release the lock of [mlist] *)
  Lemma twp_release_mlist {Φx l} :
    [[{ ⟦ mlist Φx l ⟧ ∗ ⟦ Φx (l +ₗ 1) ⟧ ∗
        ∃ l', (l +ₗ 2) ↦ #l' ∗ ⟦ mlist Φx l' ⟧ }]][mutex_wsat ⟦⟧]
      release_mutex #l
    [[{ RET #(); True }]].
  Proof.
    iIntros (Ψ) "(#m & Φx & %l' & ↦ & #mtl) →Ψ".
    wp_apply (twp_release_mutex_tok (sm:=⟦⟧) with "[Φx ↦]"); [|done].
    iSplit; [done|]. rewrite sem_to_of_cif /=. iFrame. by rewrite mlist'_unfold.
  Qed.

  (** Iterate over [mlist] *)
  Definition iter_mlist : val := rec: "self" "f" "k" "c" "l" :=
    if: !"c" ≤ #0 then #true else
      if: try_acquire_loop_mutex "k" "l" then
        "f" ("l" +ₗ #1);; let: "l'" := !("l" +ₗ #2) in release_mutex "l";;
        "c" <- !"c" - #1;; "self" "f" "k" "c" "l'"
      else #false.
  Lemma twp_iter_mlist {Φx c l} {f : val} {k n : nat} :
    (∀ l', [[{ ⟦ Φx (l' +ₗ 1) ⟧ }]][mutex_wsat ⟦⟧] f #(l' +ₗ 1)
      [[{ RET #(); ⟦ Φx (l' +ₗ 1) ⟧ }]]) -∗
    [[{ c ↦ #n ∗ ⟦ mlist Φx l ⟧ }]][mutex_wsat ⟦⟧]
      iter_mlist f #k #c #l
    [[{ b, RET #b; if b then c ↦ #0 else ∃ n', c ↦ #n' }]].
  Proof.
    iIntros "#f" (Ψ) "!> [c↦ #m] →Ψ". iInduction n as [|m] "IH" forall (l) "m".
    { wp_rec. wp_load. wp_pures. by iApply "→Ψ". }
    wp_rec. wp_load. wp_pures. wp_apply (twp_try_acquire_loop_mlist with "m").
    iIntros ([|])=>/=; last first.
    { iIntros (?). wp_pure. iModIntro. iApply "→Ψ". by iExists _. }
    iIntros "(Φx & %l' & ↦ & #mtl)". wp_pures. wp_apply ("f" with "Φx").
    iIntros "Φx". wp_load. wp_pures.
    wp_apply (twp_release_mlist with "[Φx ↦]"). { iSplit; [done|]. by iFrame. }
    iIntros "_". wp_load. wp_store. have -> : (S m - 1)%Z = m by lia.
    iApply ("IH" with "c↦ →Ψ mtl").
  Qed.

  (** ** On borrows *)

  (** Dereference a nested mutable reference *)
  Lemma bor_bor_deref {α β l Φx q} :
    [[{ β ⊑□ α ∗ q.[β] ∗ nbor_tok β (∃ l', l ↦ #l' ∗ cif_bor α (Φx l'))%cif }]]
      [pborrow_wsat bupd ⟦⟧]
      !#l
    [[{ l', RET #l'; q.[β] ∗ nbor_tok β (Φx l') }]].
  Proof.
    iIntros (Ψ) "(#⊑ & [β β'] & b) →Ψ".
    iMod (nbor_tok_open (sm:=⟦⟧) (M:=bupd) with "β b") as "/=[o [%l'[↦ b']]]".
    iApply twpw_fupdw_nonval; [done|]. wp_load. iModIntro.
    iMod (lft_sincl_live_acc with "⊑ β'") as (?) "[α →β']".
    iMod (nbor_tok_reborrow (sm:=⟦⟧) (M:=bupd) with "⊑ α b'")
      as "(α & →b' & b')".
    iDestruct ("→β'" with "α") as "β'".
    iMod (nobor_tok_subdiv (sm:=⟦⟧) (M:=bupd) [] with "[] o [] [↦ →b']")
      as "[β _]"=>/=. { iApply lft_sincl_refl. } { done. }
    { iIntros "† _". iModIntro. iExists _. iFrame "↦". by iApply "→b'". }
    iModIntro. iApply "→Ψ". rewrite to_of_cif. iFrame.
  Qed.

  (** Dereference a nested prophetic mutable reference *)
  Lemma pbor_pbor_deref {X η ξ α β l Φxx q} {x : X} :
    [[{ β ⊑□ α ∗ q.[β] ∗
        pbor_tok β ((x, ξ)' : _ *'ₛ prvarₛ _) η
          (λ '(x', ξ')', ∃ l', l ↦ #l' ∗ cif_pbor α x' ξ' (Φxx l'))%cif }]]
      [pborrow_wsat bupd ⟦⟧]
      !#l
    [[{ l', RET #l';
        q.[β] ∗ ∃ ξ' : prvar X,
          ⟨π, π η = (π ξ', ξ)'⟩ ∗ pbor_tok β x ξ' (Φxx l') }]].
  Proof.
    iIntros (Ψ) "(#⊑ & [β β'] & b) →Ψ".
    iMod (pbor_tok_open (sm:=⟦⟧) (M:=bupd) with "β b") as "/=[o[%l'[↦ b']]]".
    iApply twpw_fupdw_nonval; [done|]. wp_load. iModIntro.
    iMod (lft_sincl_live_acc with "⊑ β'") as (?) "[α →β']".
    iMod (pobor_pbor_tok_reborrow (TY:=nsynty) (sm:=⟦⟧) (M:=bupd)
      (λ _, (_,_)' : _ *'ₛ _) with "⊑ o α b' [↦]") as (?) "(β & α & obs & b)".
    { iIntros "/=% _ ? !>". iExists _. iFrame. }
    iModIntro. iApply "→Ψ". iDestruct ("→β'" with "α") as "$". iFrame "β".
    iExists _. iFrame "obs". iClear "⊑". iStopProof. apply bi.equiv_entails.
    f_equiv=> ?. by rewrite to_of_cif.
  Qed.

  (** Load from an immutable shared borrow *)
  Lemma imbor_load {l α q} {n : Z} :
    [[{ q.[α] ∗ inv_tok nroot (cif_bor α (l ↦ #n)) }]]
      [inv_wsat ⟦⟧ ∗ pborrow_wsat bupd ⟦⟧]
      !#l
    [[{ RET #n; q.[α] }]].
  Proof.
    iIntros (Φ) "[α #i] →Φ".
    iMod (inv_tok_acc (sm:=⟦⟧) with "i") as "/=[b cl]"; [done|].
    iMod (nbor_tok_open (sm:=⟦⟧) (M:=bupd) with "α b") as "[o ↦]".
    rewrite sem_to_of_cif /=. wp_load. iModIntro.
    iMod (nobor_tok_close (sm:=⟦⟧) (M:=bupd) with "o [↦]") as "[α b]".
    { by rewrite sem_to_of_cif. }
    iMod ("cl" with "b") as "_". iModIntro. by iApply "→Φ".
  Qed.

  (** Shared borrow of a mutex *)
  Definition mutex_bor' α l Px :=
    cif_bor α ((l ↦ #false ∗ cif_bor α Px) ∨ l ↦ #true).
  Definition mutex_bor α l Px := inv_tok nroot (mutex_bor' α l Px).
  Definition cif_mutex_bor α l Px := cif_inv nroot (mutex_bor' α l Px).
  #[export] Instance mutex_bor'_productive {α l} :
    Productive (mutex_bor' α l).
  Proof.
    unfold mutex_bor'=> n ?? eq. f_equiv. destruct n as [|n]=>//=. do 3 f_equiv.
    move: eq. apply proeq_later_anti. lia.
  Qed.
  #[export] Instance cif_mutex_bor_productive {α l} :
    Productive (cif_mutex_bor α l).
  Proof.
    unfold cif_mutex_bor=> n ?? eq. f_equiv. destruct n as [|n]=>//=. f_equiv.
    move: eq. apply proeq_later_anti. lia.
  Qed.

  (** Try to acquire a lock from a shared borrow over a mutex *)
  Lemma mutex_bor_try_acquire {α l Px q} :
    [[{ mutex_bor α l Px ∗ q.[α] }]][inv_wsat ⟦⟧ ∗ pborrow_wsat bupd ⟦⟧]
      try_acquire_mutex #l
    [[{ b, RET #b; (if b then nbor_tok α Px else True) ∗ q.[α] }]].
  Proof.
    iIntros (Φ) "[#m [α α']] →Φ". wp_lam. wp_bind (CmpXchg _ _ _).
    iMod (inv_tok_acc (sm:=⟦⟧) with "m") as "/=[b cl]"; [done|].
    iMod (nbor_tok_open (sm:=⟦⟧) (M:=bupd) with "α b") as "[o big]".
    rewrite sem_to_of_cif /=.
    iDestruct "big" as "[[↦ b']|↦]"; [wp_cmpxchg_suc|wp_cmpxchg_fail];
      iModIntro;
      (iMod (nobor_tok_close (sm:=⟦⟧) (M:=bupd) with "o [↦]") as "[α b]";
        [rewrite sem_to_of_cif /=; by iFrame|]);
      iMod ("cl" with "b") as "_"; iModIntro; wp_pure; iApply "→Φ"; iFrame=>//.
    by rewrite to_of_cif.
  Qed.
  (** [mutex_bor_try_acquire], repeatedly with a timeout *)
  Lemma mutex_bor_try_acquire_loop {α l Px q} {n : nat} :
    [[{ mutex_bor α l Px ∗ q.[α] }]][inv_wsat ⟦⟧ ∗ pborrow_wsat bupd ⟦⟧]
      try_acquire_loop_mutex #n #l
    [[{ b, RET #b; (if b then nbor_tok α Px else True) ∗ q.[α] }]].
  Proof.
    iIntros (Φ) "[#l α] →Φ". iInduction n as [|n] "IH".
    { wp_lam. wp_pures. iApply "→Φ". by iFrame. }
    wp_lam. wp_pures. wp_apply (mutex_bor_try_acquire with "[$l $α //]").
    iIntros ([|]).
    - iIntros "?". wp_pures. iModIntro. by iApply "→Φ".
    - iIntros "[_ α]". wp_pures. have ->: (S n - 1)%Z = n by lia.
      iApply ("IH" with "α →Φ").
  Qed.

  (** Release a lock from a shared borrow over a mutex *)
  Lemma mutex_bor_release {α l Px q} :
    [[{ mutex_bor α l Px ∗ nbor_tok α Px ∗ q.[α] }]]
      [inv_wsat ⟦⟧ ∗ pborrow_wsat bupd ⟦⟧]
      release_mutex #l
    [[{ RET #(); q.[α] }]].
  Proof.
    iIntros (Φ) "(#m & b' & α) →Φ". wp_lam.
    iMod (inv_tok_acc (sm:=⟦⟧) with "m") as "/=[b cl]"; [done|].
    iMod (nbor_tok_open (sm:=⟦⟧) (M:=bupd) with "α b") as "[o big]".
    rewrite sem_to_of_cif /=.
    iAssert (∃ b, l ↦ #b)%I with "[big]" as (?) "↦".
    { iDestruct "big" as "[[$ _]|$]". }
    wp_store. iModIntro. rewrite to_of_cif.
    iMod (nobor_tok_close (sm:=⟦⟧) (M:=bupd) with "o [b' ↦]") as "/=[α b]".
    { rewrite /= to_of_cif. iLeft. iFrame. }
    iMod ("cl" with "b") as "_". iModIntro. by iApply "→Φ".
  Qed.

  (** Create a shared borrow and a lender of a mutex *)
  Lemma mutex_bor_lend_new {α l Px b q} :
    l ↦ #b -∗ ⟦ Px ⟧ -∗ q.[α] =[inv_wsat ⟦⟧ ∗ pborrow_wsat bupd ⟦⟧]=∗
      mutex_bor α l Px ∗ nlend_tok α (∃ b', l ↦ #b' ∗ Px)%cif ∗ q.[α].
  Proof.
    iIntros "↦ Px α".
    iMod (nbor_nlend_tok_new (M:=bupd) with "[↦ Px]") as "[b $]"; [by iFrame|].
    iMod (nbor_tok_open (M:=bupd) (sm:=⟦⟧) with "α b") as "/=[o[%b'[↦ Px]]]".
    iMod (nobor_tok_subdiv (FML:=cifOF) (sm:=⟦⟧) (M:=bupd)
      [∃ b', l ↦ #b'; Px]%cif with "[] o [↦ Px] []")
      as "(α & _ & (b & b' & _))"=>/=.
    { iApply lft_sincl_refl. } { iSplitL "↦"; iFrame. }
    { by iIntros "_ [[% $][$ _]]". }
    iMod (nbor_tok_open (M:=bupd) (sm:=⟦⟧) with "α b") as "/=[o ↦]".
    iMod (nobor_tok_subdiv (FML:=cifOF) (sm:=⟦⟧) (M:=bupd)
      [(l ↦ #false ∗ cif_bor α Px) ∨ l ↦ #true]%cif with "[] o [↦ b'] []")
      as "($ & _ & [b _])"=>/=. { iApply lft_sincl_refl. }
    { iSplit; [|done]. rewrite to_of_cif.
      iDestruct "↦" as ([|]) "↦"; [|iLeft]; iFrame. }
    { by iIntros "_ [[[$ _]|$]_]". }
    iMod (inv_tok_alloc with "[b]") as "$"=>//=. by rewrite to_of_cif.
  Qed.

  (** ** Linked list with a shared borrow over a mutex *)

  (** [mblist]: Formula for a list with a shared borrow over a mutex *)
  Definition mblist_gen α Φx Mblist l : cif Σ :=
    cif_mutex_bor α l (Φx (l +ₗ 1) ∗ ∃ l', (l +ₗ 2) ↦ #l' ∗ Mblist l').
  #[export] Instance mblist_gen_productive {α Φx} :
    Productive (mblist_gen α Φx).
  Proof.
    move=>/= n ?? eq ?. unfold mblist_gen. f_equiv. destruct n as [|n]=>//=.
    (do 2 f_equiv)=> ?. f_equiv. apply eq.
  Qed.
  Definition mblist' α Φx : loc → cif Σ := profix (mblist_gen α Φx).
  Definition mblist α Φx : loc → cif Σ := mblist_gen α Φx (mblist' α Φx).
  (** Unfold [mblist'] *)
  Lemma mblist'_unfold {α Φx l} : mblist' α Φx l ≡ mblist α Φx l.
  Proof.
    move=> ?. apply cit_proeq_all=> n.
    have E : proeq n (mblist' α Φx) (mblist α Φx) by exact profix_unfold.
    apply E.
  Qed.

  (** Iterate over [mblist] *)
  Definition iter_mblist : val := rec: "self" "f" "k" "c" "l" :=
    if: !"c" ≤ #0 then #true else
      if: try_acquire_loop_mutex "k" "l" then
        "f" ("l" +ₗ #1);; let: "l'" := !("l" +ₗ #2) in release_mutex "l";;
        "c" <- !"c" - #1;; "self" "f" "k" "c" "l'"
      else #false.
  Lemma twp_iter_mblist {α Φx c l q} {f : val} {k n : nat} :
    (∀ l', [[{ ⟦ Φx (l' +ₗ 1) ⟧ }]][inv_wsat ⟦⟧ ∗ pborrow_wsat bupd ⟦⟧]
        f #(l' +ₗ 1) [[{ RET #(); ⟦ Φx (l' +ₗ 1) ⟧ }]]) -∗
    [[{ c ↦ #n ∗ ⟦ mblist α Φx l ⟧ ∗ q.[α] }]]
      [inv_wsat ⟦⟧ ∗ pborrow_wsat bupd ⟦⟧]
      iter_mblist f #k #c #l
    [[{ b, RET #b; (if b then c ↦ #0 else ∃ n', c ↦ #n') ∗ q.[α] }]].
  Proof.
    iIntros "#f" (Ψ) "!> (c↦ & #m & α) →Ψ".
    iInduction n as [|m] "IH" forall (l) "m"=>/=.
    { wp_rec. wp_load. wp_pures. iApply "→Ψ". by iFrame. }
    rewrite to_of_cif. wp_rec. wp_load. wp_pures.
    wp_apply (mutex_bor_try_acquire_loop with "[$m $α //]").
    iIntros ([|])=>/=; last first.
    { iIntros "[_ α]". wp_pure. iModIntro. iApply "→Ψ". iFrame. }
    iIntros "[b α]". wp_pures.
    iMod (nbor_tok_open (M:=bupd) (sm:=⟦⟧) with "α b")
      as "/=[o (Φx & %l' & ↦ & mtl)]".
    rewrite mblist'_unfold /=. iDestruct "mtl" as "#mtl".
    wp_apply ("f" with "Φx"). iIntros "Φx". wp_load. wp_pures.
    iMod (nobor_tok_close (M:=bupd) (sm:=⟦⟧) with "o [Φx ↦]") as "[α b]"=>/=.
    { iFrame. by rewrite mblist'_unfold. }
    wp_apply (mutex_bor_release with "[$b $α //]"). iIntros "α". wp_load.
    wp_store. have -> : (S m - 1)%Z = m by lia.
    iApply ("IH" with "c↦ α →Ψ mtl").
  Qed.

  (** ** On derivability *)

  (** [inv'] is persistent *)
  #[export] Instance inv'_persistent `{!Deriv ih δ} {N Px} :
    Persistent (inv' δ N Px).
  Proof. exact _. Qed.

  (** Turn [inv_tok] into [inv'] *)
  Lemma inv_tok_inv' `{!Deriv ih δ} {N Px} : inv_tok N Px ⊢ inv' δ N Px.
  Proof.
    iIntros "$". iApply Deriv_factor. iIntros. iModIntro. iSplit; by iIntros.
  Qed.

  (** Access using [invd] *)
  Lemma invd_acc {N Px E} : ↑N ⊆ E →
    invd N Px =[inv_wsat ⟦⟧]{E,E∖↑N}=∗
      ⟦ Px ⟧ ∗ (⟦ Px ⟧ =[inv_wsat ⟦⟧]{E∖↑N,E}=∗ True).
  Proof.
    iIntros (?) "[%Qx[#PQ i]]". iDestruct (der_sound with "PQ") as "{PQ}PQ".
    iMod (inv_tok_acc (sm:=⟦⟧) with "i") as "[Qx cl]"; [done|].
    iDestruct ("PQ" with "Qx") as "$". iIntros "!> Px". iApply "cl".
    by iApply "PQ".
  Qed.
  (** Access using [invd] via view shift *)
  Lemma invd_acc_vs {N Px E Q R} : ↑N ⊆ E →
    □ (⟦ Px ⟧ -∗ Q =[inv_wsat ⟦⟧]{E∖↑N}=∗ ⟦ Px ⟧ ∗ R) -∗
      □ (invd N Px -∗ Q =[inv_wsat ⟦⟧]{E}=∗ R).
  Proof.
    iIntros (?) "#vs !> i Q". iMod (invd_acc with "i") as "[Px cl]"; [done|].
    iMod ("vs" with "Px Q") as "[Px $]". by iApply "cl".
  Qed.
  (** Access using [invd] via [twp] *)
  Lemma invd_acc_twp {N Px E Q Ψ} `{!Atomic (stuckness_to_atomicity s) e} :
    ↑N ⊆ E → to_val e = None →
    [[{ ⟦ Px ⟧ ∗ Q }]][inv_wsat ⟦⟧] e @ s; E∖↑N [[{ v, RET v; ⟦ Px ⟧ ∗ Ψ v }]]
      -∗
      [[{ invd N Px ∗ Q }]][inv_wsat ⟦⟧] e @ s; E [[{ v, RET v; Ψ v }]].
  Proof.
    iIntros (??) "#twp %Φ !> [i Q] →Φ".
    iMod (invd_acc with "i") as "[Px cl]"; [done..|].
    iApply ("twp" with "[$Px $Q //]"). iIntros (?) "[Px Ψ]".
    iMod ("cl" with "Px") as "_". iModIntro. by iApply "→Φ".
  Qed.

  (** General rule for semantic alteration *)
  Lemma inv'_iff `{!Deriv ih δ} {N Px Qx} :
    □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Px ⟧(δ') ∗-∗ ⟦ Qx ⟧(δ')) -∗
      inv' δ N Px -∗ inv' δ N Qx.
  Proof.
    iIntros "#iff [%Rx[#? i]]". iExists Rx. iFrame "i".
    iApply Deriv_map; [|done]. iIntros (????). rewrite /⟦⟧(_) /=.
    iIntros "#[PR RP] !>". iSplit.
    - iIntros "Qx". iApply "PR". by iApply "iff".
    - iIntros "Rx". iApply "iff"; [done..|]. by iApply "RP".
  Qed.
  Lemma inv'_iff' `{!Deriv ih δ} {N Px Qx} :
    □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Px ⟧(δ') ∗-∗ ⟦ Qx ⟧(δ')) -∗
      inv' δ N Px ∗-∗ inv' δ N Qx.
  Proof.
    iIntros "#iff". iSplit; iApply inv'_iff; [done|]. iIntros "!>" (????).
    rewrite bi.wand_iff_sym. by iApply "iff".
  Qed.

  (** Derived semantic alteration *)
  Local Lemma inv'_sep_comm' `{!Deriv ih δ} {N Px Qx} :
    inv' δ N (Px ∗ Qx)%cif ⊢ inv' δ N (Qx ∗ Px)%cif.
  Proof.
    iApply inv'_iff. iIntros "!> /=" (????). rewrite bi.sep_comm.
    iApply bi.wand_iff_refl.
  Qed.
  Lemma inv'_sep_comm `{!Deriv ih δ} {N Px Qx} :
    inv' δ N (Px ∗ Qx)%cif ⊣⊢ inv' δ N (Qx ∗ Px)%cif.
  Proof. apply bi.equiv_entails. split; exact inv'_sep_comm'. Qed.
  Local Lemma inv'_inv'_sep_comm' `{!Deriv ih δ} {N N' Px Qx} :
    inv' δ N (cif_inv' N' (Px ∗ Qx)) ⊢ inv' δ N (cif_inv' N' (Qx ∗ Px)).
  Proof.
    iApply inv'_iff. iIntros "!> /=" (????). rewrite !to_of_cif inv'_sep_comm.
    iApply bi.wand_iff_refl.
  Qed.
  Lemma inv'_inv'_sep_comm `{!Deriv ih δ} {N N' Px Qx} :
    inv' δ N (cif_inv' N' (Px ∗ Qx)) ⊣⊢ inv' δ N (cif_inv' N' (Qx ∗ Px)).
  Proof. apply bi.equiv_entails. split; exact inv'_inv'_sep_comm'. Qed.
  Local Lemma inv'_bor_lft' `{!Deriv ih δ} {N α β Px} :
    α ⊑□ β -∗ β ⊑□ α -∗ inv' δ N (cif_bor α Px) -∗ inv' δ N (cif_bor β Px).
  Proof.
    iIntros "#? #?". iApply inv'_iff. iIntros "!>" (????). rewrite /⟦⟧(_) /=.
    iSplit; by iApply nbor_tok_lft.
  Qed.
  Lemma inv'_bor_lft `{!Deriv ih δ} {N α β Px} :
    α ⊑□ β -∗ β ⊑□ α -∗ inv' δ N (cif_bor α Px) ∗-∗ inv' δ N (cif_bor β Px).
  Proof. iIntros "#? #?". iSplit; by iApply inv'_bor_lft'. Qed.
End verify.
