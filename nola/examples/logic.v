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
| (** Non-prophetic closed borrower *) cifs_borc (α : lft)
| (** Non-prophetic borrower *) cifs_bor (α : lft)
| (** Non-prophetic open borrower *) cifs_obor (α : lft) (q : Qp)
| (** Non-prophetic lender *) cifs_lend (α : lft)
| (** Prophetic closed borrower *)
    cifs_pborc {X} (α : lft) (x : X) (ξ : prvar X)
| (** Prophetic borrower *) cifs_pbor {X} (α : lft) (x : X) (ξ : prvar X)
| (** Prophetic open borrower *) cifs_pobor {X} (α : lft) (q : Qp) (ξ : prvar X)
| (** Prophetic lender *) cifs_plend {X} (α : lft) (xπ : clair nsynty X).
(** [idom]: Domain for inductive parts *)
Definition idom (_ : sel) : Type := Empty_set.
(** [cdom]: Domain for coinductive parts *)
Definition cdom (s : sel) : Type := match s with
  | cifs_pointsto _ _ _ => Empty_set
  | cifs_inv _ | cifs_inv' _ | cifs_mutex _
    | cifs_borc _ | cifs_bor _ | cifs_obor _ _ | cifs_lend _ => unit
  | @cifs_pborc X _ _ _ | @cifs_pbor X _ _ _ | @cifs_pobor X _ _ _
    | @cifs_plend X _ _ => X
  end.
(** [dataOF]: Data [oFunctor] *)
Definition dataOF (_ : sel) : oFunctor := unitO.
(** [dataOF] is contractive *)
Fact dataOF_contractive {s} : oFunctorContractive (dataOF s).
Proof. exact _. Qed.

(** ** [cif]: Formulas *)
Notation cif Σ := (cif idom cdom dataOF Σ).
Notation cifOF := (cifOF idom cdom dataOF).

(** [cifOF] is contractive *)
Fact cifOF_contractive : oFunctorContractive cifOF.
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
  (** Non-prophetic closed borrower *)
  Definition cif_borc α Px : cif Σ :=
    cif_custom (cifs_borc α) nullary (unary Px) ().
  (** Non-prophetic borrower *)
  Definition cif_bor α Px : cif Σ :=
    cif_custom (cifs_bor α) nullary (unary Px) ().
  (** Non-prophetic open borrower *)
  Definition cif_obor α q Px : cif Σ :=
    cif_custom (cifs_obor α q) nullary (unary Px) ().
  (** Non-prophetic lender *)
  Definition cif_lend α Px : cif Σ :=
    cif_custom (cifs_lend α) nullary (unary Px) ().
  (** Prophetic closed borrower *)
  Definition cif_pborc {X} α x ξ (Φx : X -d> cif Σ) : cif Σ :=
    cif_custom (@cifs_pborc X α x ξ) nullary Φx ().
  (** Prophetic borrower *)
  Definition cif_pbor {X} α x ξ (Φx : X -d> cif Σ) : cif Σ :=
    cif_custom (@cifs_pbor X α x ξ) nullary Φx ().
  (** Prophetic open borrower *)
  Definition cif_pobor {X} α q ξ (Φx : X -d> cif Σ) : cif Σ :=
    cif_custom (@cifs_pobor X α q ξ) nullary Φx ().
  (** Prophetic lender *)
  Definition cif_plend {X} α xπ (Φx : X -d> cif Σ) : cif Σ :=
    cif_custom (@cifs_plend X α xπ) nullary Φx ().

  (** The custom constructors are non-expansive *)
  #[export] Instance cif_inv_ne {N} : NonExpansive (cif_inv N).
  Proof. move=> ????. apply cif_custom_ne; solve_proper. Qed.
  #[export] Instance cif_inv'_ne {N} : NonExpansive (cif_inv' N).
  Proof. move=> ????. apply cif_custom_ne; solve_proper. Qed.
  #[export] Instance cif_mutex_ne {l} : NonExpansive (cif_mutex l).
  Proof. move=> ????. apply cif_custom_ne; solve_proper. Qed.
  #[export] Instance cif_borc_ne {α} : NonExpansive (cif_borc α).
  Proof. move=> ????. apply cif_custom_ne; solve_proper. Qed.
  #[export] Instance cif_bor_ne {α} : NonExpansive (cif_bor α).
  Proof. move=> ????. apply cif_custom_ne; solve_proper. Qed.
  #[export] Instance cif_obor_ne {α q} : NonExpansive (cif_obor α q).
  Proof. move=> ????. apply cif_custom_ne; solve_proper. Qed.
  #[export] Instance cif_lend_ne {α} : NonExpansive (cif_lend α).
  Proof. move=> ????. apply cif_custom_ne; solve_proper. Qed.
  #[export] Instance cif_pborc_ne {X α x ξ} : NonExpansive (@cif_pborc X α x ξ).
  Proof. move=> ????. apply cif_custom_ne; solve_proper. Qed.
  #[export] Instance cif_pbor_ne {X α x ξ} : NonExpansive (@cif_pbor X α x ξ).
  Proof. move=> ????. apply cif_custom_ne; solve_proper. Qed.
  #[export] Instance cif_pobor_ne {X α q ξ} : NonExpansive (@cif_pobor X α q ξ).
  Proof. move=> ????. apply cif_custom_ne; solve_proper. Qed.
  #[export] Instance cif_plend_ne {X α xπ} : NonExpansive (@cif_plend X α xπ).
  Proof. move=> ????. apply cif_custom_ne; solve_proper. Qed.
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

  (** ** [bsem]: Base semantics *)
  Definition bsem δ s :
    (idom s -d> iProp Σ) → (cdom s -d> cif Σ) → dataOF s $oi Σ → iProp Σ :=
    match s with
    | cifs_pointsto l dq v => λ _ _ _, l ↦{dq} v
    | cifs_inv N => λ _ Pxs _, inv_tok N (Pxs ())
    | cifs_inv' N => λ _ Pxs _, inv' δ N (Pxs ())
    | cifs_mutex l => λ _ Pxs _, mutex_tok l (Pxs ())
    | cifs_borc α => λ _ Pxs _, nborc_tok α (Pxs ())
    | cifs_bor α => λ _ Pxs _, nbor_tok α (Pxs ())
    | cifs_obor α q => λ _ Pxs _, nobor_tok α q (Pxs ())
    | cifs_lend α => λ _ Pxs _, nlend_tok α (Pxs ())
    | cifs_pborc α x ξ => λ _ Φx _, pborc_tok α x ξ Φx
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
  Fact cif_sem_ne `{!NonExpansive δ} : NonExpansive ⟦⟧(δ)@{cif Σ}.
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
End sem.
Notation invd := (inv' der).

Section verify.
  Context `{!inv'GS cifOF Σ, !mutexGS cifOF Σ,
    !pborrowGS nsynty cifOF Σ, !heapGS_gen hlc Σ}.
  Implicit Type (Px Qx : cif Σ) (Φx Ψx : loc → cif Σ).

  (** ** Linked list *)

  (** [ilist]: Formula for a list *)
  Definition ilist_gen N Φx Ilist' l : cif Σ :=
    cif_inv N (Φx l) ∗ cif_inv N (Ilist' N Φx l).
  Definition ilist'_gen N Φx Ilist' l : cif Σ :=
    ∃ l', (l +ₗ 1) ↦ #l' ∗ ilist_gen N Φx Ilist' l'.
  CoFixpoint ilist' N Φx : loc → cif Σ := ilist'_gen N Φx ilist'.
  Definition ilist N Φx : loc → cif Σ := ilist_gen N Φx ilist'.

  (** Access the tail of a list *)
  Definition tail_ilist : val := λ: "l", !("l" +ₗ #1).
  Lemma twp_tail_list {N E Φx l} : ↑N ⊆ E →
    [[{ ⟦ ilist N Φx l ⟧ }]][inv_wsat ⟦⟧]
      tail_ilist #l @ E
    [[{ l', RET #l'; ⟦ ilist N Φx l' ⟧ }]].
  Proof.
    rewrite !/⟦ ilist _ _ _ ⟧ /=. iIntros (? Ψ) "/= #[_ itl] →Ψ". wp_rec.
    wp_pure. iMod (inv_tok_acc (sm:=⟦⟧) with "itl") as "[ltl cl]"; [done|].
    rewrite !/⟦ ilist' _ _ _ ⟧ /=. iDestruct "ltl" as (?) "[↦l' #ltl]".
    wp_load. iModIntro. iMod ("cl" with "[↦l']") as "_".
    { iExists _. by iFrame. } { iModIntro. iApply ("→Ψ" with "ltl"). }
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
    iIntros "% #f" (Ψ) "!> [c↦ #l] →Ψ".
    iInduction n as [|m] "IH" forall (l) "l".
    { wp_rec. wp_load. wp_pures. by iApply "→Ψ". }
    wp_rec. wp_load. wp_pures. wp_apply "f".
    { rewrite !/⟦ ilist _ _ _ ⟧ /=. iDestruct "l" as "[$ _]". }
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

  (** ** Linked list with a mutex *)

  (** [mlist]: Formula for a list with a mutex *)
  Definition mlist_gen Φx Mlist' l : cif Σ :=
    cif_mutex l (Mlist' Φx l).
  Definition mlist'_gen Φx Mlist' l : cif Σ :=
    Φx (l +ₗ 1) ∗ ∃ l', (l +ₗ 2) ↦ #l' ∗ mlist_gen Φx Mlist' l'.
  CoFixpoint mlist' Φx : loc → cif Σ := mlist'_gen Φx mlist'.
  Definition mlist Φx : loc → cif Σ := mlist_gen Φx mlist'.

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
    rewrite /⟦⟧ /=. iIntros "[Φx (% & ↦ & #m')]". iApply "→Ψ". by iFrame.
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
    iSplit; [done|]. rewrite /⟦⟧ /=. by iFrame.
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
    [[{ β ⊑□ α ∗ q.[β] ∗ nbor_tok α (∃ l', l ↦ #l' ∗ cif_bor β (Φx l'))%cif }]]
      [pborrow_wsat bupd ⟦⟧]
      !#l
    [[{ l', RET #l'; q.[β] ∗ nborc_tok β (Φx l') }]].
  Proof.
    iIntros (Ψ) "(#⊑ & [β β'] & b) →Ψ".
    iMod (lft_sincl_live_acc with "⊑ β'") as (?) "[α →β']".
    iMod (nbor_tok_open (sm:=⟦⟧) (M:=bupd) with "α b") as "[o big]".
    rewrite /⟦⟧ /=. iDestruct "big" as (l') "[↦ b']".
    iApply twpw_fupdw_nonval; [done|]. wp_load. iModIntro.
    iMod (nbor_tok_reborrow (sm:=⟦⟧) (M:=bupd) α with "β b'") as "[β[b' →b']]".
    iMod (nobor_tok_subdiv (sm:=⟦⟧) (M:=bupd) [] with "[] o [] [↦ →b']")
      as "[α _]"=>/=. { iApply lft_sincl_refl. } { done. }
    { iIntros "† _". iModIntro. iExists _. iFrame "↦". by iApply "→b'". }
    iModIntro. iApply "→Ψ". iFrame "β". iDestruct ("→β'" with "α") as "$".
    iApply nborc_tok_lft; [|done]. iApply lft_sincl_meet_intro; [|done].
    iApply lft_sincl_refl.
  Qed.

  (** Dereference a nested prophetic mutable reference *)
  Lemma pbor_pbor_deref {X η ξ α β l Φxx q} {x : X} :
    [[{ β ⊑□ α ∗ q.[β] ∗
        pbor_tok α ((x, ξ)' : _ *'ₛ prvarₛ _) η
          (λ '(x', ξ')', ∃ l', l ↦ #l' ∗ cif_pbor β x' ξ' (Φxx l'))%cif }]]
      [pborrow_wsat bupd ⟦⟧]
      !#l
    [[{ l', RET #l';
        q.[β] ∗ ∃ ξ' : prvar X,
          ⟨π, π η = (π ξ', ξ)'⟩ ∗ pborc_tok β x ξ' (Φxx l') }]].
  Proof.
    iIntros (Ψ) "(#⊑ & [β β'] & b) →Ψ".
    iMod (lft_sincl_live_acc with "⊑ β'") as (?) "[α →β']".
    iMod (pbor_tok_open (sm:=⟦⟧) (M:=bupd) with "α b") as "/=[o big]".
    rewrite /⟦⟧ /=. iDestruct "big" as (l') "[↦ b']".
    iApply twpw_fupdw_nonval; [done|]. wp_load. iModIntro.
    iMod (pobor_pbor_tok_reborrow (TY:=nsynty) (sm:=⟦⟧) (M:=bupd)
      (λ _, (_,_)' : _ *'ₛ _) with "o β b' [↦]") as (?) "[α[β[obs c]]]".
    { iIntros "/=% _ ? !>". iExists _. iFrame. }
    iModIntro. iApply "→Ψ". iFrame "β". iDestruct ("→β'" with "α") as "$".
    iExists _. iFrame "obs". iApply pborc_tok_lft; [|done].
    iApply lft_sincl_meet_intro; [done|]. iApply lft_sincl_refl.
  Qed.

  (** Load from an immutable shared borrow *)
  Lemma imbor_load {l α q} {n : Z} :
    [[{ q.[α] ∗ inv_tok nroot (cif_bor α (l ↦ #n)) }]]
      [inv_wsat ⟦⟧ ∗ pborrow_wsat bupd ⟦⟧]
      !#l
    [[{ RET #n; q.[α] }]].
  Proof.
    iIntros (Φ) "[α #i] →Φ".
    iMod (inv_tok_acc (sm:=⟦⟧) with "i") as "[b cl]"; [done|]. rewrite /⟦⟧ /=.
    iMod (nbor_tok_open (sm:=⟦⟧) (M:=bupd) with "α b") as "[o ↦]".
    rewrite /⟦⟧ /=. iDestruct "↦" as "↦". wp_load. iModIntro.
    iMod (nobor_tok_close (sm:=⟦⟧) (M:=bupd) with "o [$↦ //]") as "[α b]".
    rewrite nborc_tok_nbor_tok. iMod ("cl" with "b") as "_". iModIntro.
    by iApply "→Φ".
  Qed.

  (** Shared borrow of a mutex *)
  Definition mutex_bor α l Px :=
    inv_tok nroot (cif_bor α ((l ↦ #false ∗ cif_bor α Px) ∨ l ↦ #true)).

  (** Try to acquire a lock from a shared borrow over a mutex *)
  Lemma mutex_bor_try_acquire {α l Px q} :
    [[{ mutex_bor α l Px ∗ q.[α] }]][inv_wsat ⟦⟧ ∗ pborrow_wsat bupd ⟦⟧]
      CAS #l #false #true
    [[{ b, RET #b; (if b then nbor_tok α Px else True) ∗ q.[α] }]].
  Proof.
    iIntros (Φ) "[#m [α α']] →Φ". wp_bind (CmpXchg _ _ _).
    iMod (inv_tok_acc (sm:=⟦⟧) with "m") as "[b cl]"; [done|].
    rewrite /⟦ cif_bor _ _ ⟧ /=.
    iMod (nbor_tok_open (sm:=⟦⟧) (M:=bupd) with "α b") as "[o big]".
    rewrite /⟦_ ∨ _⟧%cif /=.
    iDestruct "big" as "[[↦ b']|↦]"; [wp_cmpxchg_suc|wp_cmpxchg_fail];
      iModIntro;
      iMod (nobor_tok_close (sm:=⟦⟧) (M:=bupd) with "o [$↦ //]") as "[α b]";
      rewrite nborc_tok_nbor_tok; iMod ("cl" with "b") as "_"; iModIntro;
      wp_pure; iApply "→Φ"; by iFrame.
  Qed.

  (** Release a lock from a shared borrow over a mutex *)
  Lemma mutex_bor_release {α l Px q} :
    [[{ mutex_bor α l Px ∗ nbor_tok α Px ∗ q.[α] }]]
      [inv_wsat ⟦⟧ ∗ pborrow_wsat bupd ⟦⟧]
      #l <- #false
    [[{ RET #(); q.[α] }]].
  Proof.
    iIntros (Φ) "(#m & b' & α) →Φ".
    iMod (inv_tok_acc (sm:=⟦⟧) with "m") as "[b cl]"; [done|].
    rewrite /⟦ cif_bor _ _ ⟧ /=.
    iMod (nbor_tok_open (sm:=⟦⟧) (M:=bupd) with "α b") as "[o big]".
    rewrite /⟦_ ∨ _⟧%cif /=.
    iAssert (∃ b, l ↦ #b)%I with "[big]" as (?) "↦".
    { iDestruct "big" as "[[$ _]|$]". }
    wp_store. iModIntro.
    iMod (nobor_tok_close (sm:=⟦⟧) (M:=bupd) with "o [b' ↦]") as "[α b]".
    { iLeft. iFrame. }
    rewrite nborc_tok_nbor_tok. iMod ("cl" with "b") as "_". iModIntro.
    by iApply "→Φ".
  Qed.

  (** Create a shared borrow and a lender of a mutex *)
  Lemma mutex_bor_lend_new {α l Px b q} :
    l ↦ #b -∗ ⟦ Px ⟧ -∗ q.[α] =[inv_wsat ⟦⟧ ∗ pborrow_wsat bupd ⟦⟧]=∗
      mutex_bor α l Px ∗ nlend_tok α (∃ b', l ↦ #b' ∗ Px)%cif ∗ q.[α].
  Proof.
    iIntros "↦ Px α".
    iMod (nborc_nlend_tok_new (M:=bupd) with "[↦ Px]") as "[b $]"; [by iFrame|].
    iMod (nborc_tok_open (sm:=⟦⟧) with "α b") as "[o big]". rewrite /⟦⟧ /=.
    iDestruct "big" as (b') "[↦ Px]".
    iMod (nobor_tok_subdiv (sm:=⟦⟧) (M:=bupd) [∃ b', l ↦ #b'; Px]%cif
      with "[] o [↦ Px] []") as "[α[b[b' _]]]"; rewrite /⟦⟧ /=.
    { iApply lft_sincl_refl. } { iSplitL "↦"; iFrame. }
    { by iIntros "_ [[% $][$ _]]". }
    iMod (nborc_tok_open (sm:=⟦⟧) with "α b") as "[o ↦]".
    iMod (nobor_tok_subdiv (sm:=⟦⟧) (M:=bupd)
      [(l ↦ #false ∗ cif_bor α Px) ∨ l ↦ #true]%cif with "[] o [↦ b'] []")
      as "[$[b _]]"; rewrite /⟦⟧ /=. { iApply lft_sincl_refl. }
    { iSplit; [|done]. rewrite nborc_tok_nbor_tok.
      iDestruct "↦" as ([|]) "↦"; [|iLeft]; iFrame. }
    { by iIntros "_ [[[$ _]|$]_]". }
    rewrite nborc_tok_nbor_tok. by iMod (inv_tok_alloc with "[b]") as "$".
  Qed.

  (** ** On derivability *)

  (** [inv'] is persistent *)
  Fact inv'_persistent `{!Deriv ih δ} {N Px} : Persistent (inv' δ N Px).
  Proof. exact _. Qed.

  (** Turn [inv_tok] into [inv'] *)
  Lemma inv_tok_inv' `{!Deriv ih δ} {N Px} : inv_tok N Px ⊢ inv' δ N Px.
  Proof.
    iIntros "$". iApply Deriv_factor. iIntros. iModIntro. iSplit; by iIntros.
  Qed.

  (** Access [invd] *)
  Lemma invd_acc {N Px E} : ↑N ⊆ E →
    invd N Px =[inv_wsat ⟦⟧]{E,E∖↑N}=∗
      ⟦ Px ⟧ ∗ (⟦ Px ⟧ =[inv_wsat ⟦⟧]{E∖↑N,E}=∗ True).
  Proof.
    iIntros (?) "[%Qx[#PQ i]]". iDestruct (der_sound with "PQ") as "{PQ}PQ".
    iMod (inv_tok_acc (sm:=⟦⟧) with "i") as "[Q cl]"; [done|].
    iDestruct ("PQ" with "Q") as "$". iIntros "!> P". iApply "cl".
    by iApply "PQ".
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
    - iIntros "Q". iApply "PR". by iApply "iff".
    - iIntros "R". iApply "iff"; [done..|]. by iApply "RP".
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
    iApply inv'_iff. iIntros "!>" (????). rewrite /⟦⟧(_) /= bi.sep_comm.
    iApply bi.wand_iff_refl.
  Qed.
  Lemma inv'_sep_comm `{!Deriv ih δ} {N Px Qx} :
    inv' δ N (Px ∗ Qx)%cif ⊣⊢ inv' δ N (Qx ∗ Px)%cif.
  Proof. apply bi.equiv_entails. split; exact inv'_sep_comm'. Qed.
  Local Lemma inv'_inv'_sep_comm' `{!Deriv ih δ} {N N' Px Qx} :
    inv' δ N (cif_inv' N' (Px ∗ Qx)) ⊢ inv' δ N (cif_inv' N' (Qx ∗ Px)).
  Proof.
    iApply inv'_iff. iIntros "!>" (????). rewrite /⟦⟧(_) /= inv'_sep_comm.
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
