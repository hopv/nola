(** * Showcase logic *)

From nola.iris Require Export cif inv_deriv pborrow_deriv.
From nola.bi Require Import util.
From nola.heap_lang Require Export notation proofmode lib.mutex.
From nola.examples Require Export nsynty.
Import ProdNotation UpdwNotation WpwNotation iPropAppNotation PsemNotation
  SemNotation ProphNotation LftNotation NsyntyNotation.

Implicit Type (N : namespace) (l : loc) (b : bool) (α β : lft) (q : Qp)
  (X Y : nsynty).

(** ** Preliminaries *)

(** [sel]: Selector *)
Variant sel :=
| (** Invariant *) cifs_inv (N : namespace)
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
  | cifs_inv _ | cifs_mutex _
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
  (** Invariant *)
  Definition cif_inv N Px : cif Σ :=
    cif_custom (cifs_inv N) nullary (unary Px) ().
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

(** ** [judg]: Judgment *)
Definition judg Σ : ofe :=
  (leibnizO namespace * cif Σ + cif Σ * cif Σ + cif Σ * cif Σ +
    sigT (A:=nsynty *' nsynty) (λ '(X, Y)',
      leibnizO (clair nsynty X *' clair nsynty Y) *
      (X -d> cif Σ) * (Y -d> cif Σ)))%type.
Definition inv_jacsr {Σ} N Px : judg Σ := inl (inl (inl (N, Px))).
Definition mutex_jiff {Σ} Px Qx : judg Σ := inl (inl (inr (Px, Qx))).
Definition pborrow_jto {Σ} Px Qx : judg Σ := inl (inr (Px, Qx)).
Definition pborrow_jlto {Σ X Y} xπ yπ Φx Ψx : judg Σ :=
  inr (existT (X, Y)' ((xπ, yπ)', Φx, Ψx)).
#[export] Instance inv_jacsr_ne {Σ N} : NonExpansive (@inv_jacsr Σ N).
Proof. move=> ????. by do 3 apply: inl_ne. Qed.
#[export] Instance mutex_jiff_ne {Σ} : NonExpansive2 (@mutex_jiff Σ).
Proof. move=> ???????. do 2 apply: inl_ne. exact: inr_ne. Qed.
#[export] Instance pborrow_jto_ne {Σ} : NonExpansive2 (@pborrow_jto Σ).
Proof. move=> ???????. apply: inl_ne. exact: inr_ne. Qed.
#[export] Instance pborrow_jlto_ne {Σ X Y xπ yπ} :
  NonExpansive2 (@pborrow_jlto Σ X Y xπ yπ).
Proof.
  move=> ???????. apply inr_ne. apply: existT_ne=>/=. by split; [split|].
Qed.

#[export] Instance judg_inv_pre_deriv {Σ} :
  InvPreDeriv (cif Σ) (judg Σ) := INV_PRE_DERIV inv_jacsr.
#[export] Instance judg_mutex_pre_deriv {Σ} :
  MutexPreDeriv (cif Σ) (judg Σ) := MUTEX_PRE_DERIV mutex_jiff.
#[export] Instance judg_pborrow_pre_deriv {Σ} :
  PborrowPreDeriv nsynty (cif Σ) (judg Σ) :=
  PBORROW_PRE_DERIV pborrow_jto (@pborrow_jlto _).

Section sem.
  Context `{!inv'GS cifOF Σ, !mutexGS cifOF Σ, !pborrowGS nsynty cifOF Σ}.
  Implicit Type δ : judg Σ → iProp Σ.

  (** ** [bsem]: Base semantics *)
  Definition bsem δ s :
    (idom s -d> iProp Σ) → (cdom s -d> cif Σ) → dataOF s $oi Σ → iProp Σ :=
    match s with
    | cifs_inv N => λ _ Pxs _, inv' δ N (Pxs ())
    | cifs_mutex l => λ _ Pxs _, mutex δ l (Pxs ())
    | cifs_borc α => λ _ Pxs _, nborc δ α (Pxs ())
    | cifs_bor α => λ _ Pxs _, nbor δ α (Pxs ())
    | cifs_obor α q => λ _ Pxs _, nobor δ α q (Pxs ())
    | cifs_lend α => λ _ Pxs _, nlend δ α (Pxs ())
    | cifs_pborc α x ξ => λ _ Φx _, pborc δ α x ξ Φx
    | cifs_pbor α x ξ => λ _ Φx _, pbor δ α x ξ Φx
    | cifs_pobor α q ξ => λ _ Φx _, pobor δ α q ξ Φx
    | cifs_plend α xπ => λ _ Φx _, plend δ α xπ Φx
    end.

  (** [bsem] is non-expansive *)
  #[export] Instance bsem_ne `{!NonExpansive δ} {s} : NonExpansive3 (bsem δ s).
  Proof. case s; solve_proper. Qed.

  (** Parameterized semantics of [cif] *)
  #[export] Instance cif_dsem : Dsem (judg Σ) (cif Σ) (iProp Σ) :=
    DSEM (λ δ, cif_sem (bsem δ)).

  (** [cif_sem] is non-expansive *)
  Fact cif_sem_ne `{!NonExpansive δ} : NonExpansive ⟦⟧(δ)@{cif Σ}.
  Proof. exact _. Qed.

  Context `{!heapGS_gen hlc Σ}.

  (** [judg_sem]: Judgment semantics *)
  Definition judg_sem δ (J : judg Σ) := match J with
    | inl (inl (inl (N, Px))) => inv_acsr ⟦⟧(δ) N ⟦ Px ⟧(δ)
    | inl (inl (inr (Px, Qx))) => mod_iff (fupd ⊤ ⊤) ⟦ Px ⟧(δ) ⟦ Qx ⟧(δ)
    | inl (inr (Px, Qx)) => ⟦ Px ⟧(δ) ==∗ ⟦ Qx ⟧(δ)
    | inr (existT (X, Y)' ((xπ, yπ)', Φx, Ψx)) =>
        plend_body ⟦ ⟧(δ) xπ Φx ==∗ plend_body ⟦ ⟧(δ) yπ Ψx
    end%I.
  Local Instance judg_sem_ne `{!NonExpansive δ} : NonExpansive (judg_sem δ).
  Proof.
    move=> ? _ _[_ _[_ _[|]|]|].
    - move=> [??][??][/=/leibniz_equiv_iff<- ?]. solve_proper.
    - move=> [??][??][/=??]. solve_proper.
    - move=> [??][??]/=[??]. solve_proper.
    - move=> [?[[[??]?]?]][?[[[??]?]?]][/=?]. subst=>/=.
      move=> [/=[/=/leibniz_equiv_iff[<-<-]?]?]. solve_proper.
  Qed.
  #[export] Instance judg_dsem : Dsem (judg Σ) (judg Σ) (iProp Σ) :=
    DSEM judg_sem.
  Canonical judgJ : judgi (iProp Σ) := Judgi (judg Σ).

  #[export] Instance judg_inv_deriv : InvDeriv cifOF Σ judgJ.
  Proof. done. Qed.
  #[export] Instance judg_mutex_deriv : MutexDeriv cifOF Σ judgJ.
  Proof. done. Qed.
  #[export] Instance judg_pborrow_deriv : PborrowDeriv nsynty cifOF Σ judgJ.
  Proof. done. Qed.
End sem.

Section verify.
  Context `{!inv'GS cifOF Σ, !mutexGS cifOF Σ,
    !pborrowGS nsynty cifOF Σ, !heapGS_gen hlc Σ}.
  Implicit Type (Px Qx : cif Σ) (Φx Ψx : loc → cif Σ).

  (** ** Linked list *)

  (** [ilist]: Formula for a list *)
  Definition ilist_gen N Φx Ilist' l : cif Σ :=
    cif_inv N (Φx l) ∗ cif_inv N (Ilist' N Φx l).
  Definition ilist'_gen N Φx Ilist' l : cif Σ :=
    ∃ l', ▷ (l +ₗ 1) ↦ #l' ∗ ilist_gen N Φx Ilist' l'.
  CoFixpoint ilist' N Φx : loc → cif Σ := ilist'_gen N Φx ilist'.
  Definition ilist N Φx : loc → cif Σ := ilist_gen N Φx ilist'.

  (** Convert the predicate of [ilist] using [mod_acsr] *)
  Local Lemma inv'_acsr_iff `{!Deriv ih δ} {N Φx Ψx l} :
    □ (∀ l' δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ →
      mod_acsr (fupd ∅ ∅) ⟦ Φx l' ⟧(δ') ⟦ Ψx l' ⟧(δ') ∧
      mod_acsr (fupd ∅ ∅) ⟦ Ψx l' ⟧(δ') ⟦ Φx l' ⟧(δ')) ⊢
      inv' δ N (Φx l) ∗-∗ inv' δ N (Ψx l).
  Proof.
    iIntros "#big". iSplit; iApply inv'_acsr; iIntros "!>" (????);
      [iApply bi.and_elim_l|iApply bi.and_elim_r]; by iApply "big".
  Qed.
  Local Lemma inv'_ilist'_iff `{!Deriv ih δ} {N Φx Ψx l} :
    □ (∀ l' δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ →
      inv' δ' N (Φx l') ∗-∗ inv' δ' N (Ψx l')) -∗
      inv' δ N (ilist' N Φx l) ∗-∗ inv' δ N (ilist' N Ψx l).
  Proof.
    move: l. apply Deriv_ind=> δ' ??. iIntros "#eqv".
    iSplit; iApply inv'_acsr; iIntros "!>" (??[IH ?]?);
      rewrite -(wand_iff_mod_acsr (M:=fupd _ _)) !/⟦ ilist' _ _ _ ⟧(_);
      (iModIntro; iSplit; iIntros "/=[%[$[ihd ?]]]"; (iSplit; [|by iApply IH]));
      iApply ("eqv" with "[%] [//] ihd"); by apply Deriv_mono=> ?[??].
  Qed.
  Lemma ilist_acsr `{!Deriv ih δ} {N Φx Ψx l} :
    □ (∀ l' δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ →
      mod_acsr (fupd ∅ ∅) ⟦ Φx l' ⟧(δ') ⟦ Ψx l' ⟧(δ') ∧
      mod_acsr (fupd ∅ ∅) ⟦ Ψx l' ⟧(δ') ⟦ Φx l' ⟧(δ')) -∗
      ⟦ ilist N Φx l ⟧(δ) ∗-∗ ⟦ ilist N Ψx l ⟧(δ).
  Proof.
    iIntros "#eqv". rewrite /⟦ ⟧(δ) /=.
    iSplit; (iIntros "[ihd itl]"; iSplitL "ihd";
      [by iApply (inv'_acsr_iff (Φx:=Φx))|]);
      iApply (inv'_ilist'_iff with "[] itl"); iIntros "!>" (????);
      [iApply bi.wand_iff_sym|]; by iApply inv'_acsr_iff.
  Qed.

  (** Access the tail of a list *)
  Definition tail_ilist : val := λ: "l", !("l" +ₗ #1).
  Lemma twp_tail_list {N E Φx l} : ↑N ⊆ E →
    [[{ ⟦ ilist N Φx l ⟧ }]][inv_wsatid]
      tail_ilist #l @ E
    [[{ l', RET #l'; ⟦ ilist N Φx l' ⟧ }]].
  Proof.
    rewrite !/⟦ ilist _ _ _ ⟧ /=. iIntros (? Ψ) "/= #[_ itl] →Ψ". wp_rec.
    wp_pure. iMod (invd_acc with "itl") as "[ltl cl]"; [done|].
    rewrite !/⟦ ilist' _ _ _ ⟧ /=. iDestruct "ltl" as (?) "[>↦l' #ltl]".
    wp_load. iModIntro. iMod ("cl" with "[↦l']") as "_".
    { iExists _. by iFrame. } { iModIntro. iApply ("→Ψ" with "ltl"). }
  Qed.

  (** Iterate over a list *)
  Definition iter_ilist : val := rec: "self" "f" "c" "l" :=
    if: !"c" ≤ #0 then #() else
      "f" "l";; "c" <- !"c" - #1;; "self" "f" "c" (tail_ilist "l").
  Lemma twp_iter_list {N E Φx c l} {f : val} {n : nat} : ↑N ⊆ E →
    (∀ l', [[{ invd N (Φx l') }]][inv_wsatid] f #l' @ E
      [[{ RET #(); True }]]) -∗
    [[{ c ↦ #n ∗ ⟦ ilist N Φx l ⟧ }]][inv_wsatid]
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
    (∀ l', [[{ invd N (Φx l') }]][inv_wsatid] f #l' @ E
      [[{ RET #(); True }]]) -∗
    [[{ c' ↦ #m ∗ c ↦ #n ∗ ⟦ ilist N Φx l ⟧ }]][inv_wsatid]
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
    Φx (l +ₗ 1) ∗ ∃ l', ▷ (l +ₗ 2) ↦ #l' ∗ mlist_gen Φx Mlist' l'.
  CoFixpoint mlist' Φx : loc → cif Σ := mlist'_gen Φx mlist'.
  Definition mlist Φx : loc → cif Σ := mlist_gen Φx mlist'.

  (** Convert the predicate of [mlist] using [mod_iff] *)
  Lemma mlist_iff `{!Deriv ih δ} {Φx Ψx l} :
    □ (∀ l' δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ →
      mod_iff (fupd ⊤ ⊤) ⟦ Φx l' ⟧(δ') ⟦ Ψx l' ⟧(δ')) -∗
      ⟦ mlist Φx l ⟧(δ) ∗-∗ ⟦ mlist Ψx l ⟧(δ).
  Proof.
    rewrite !/⟦ mlist _ _ ⟧(_) /=. move: l. apply Deriv_ind=> ???.
    iIntros "#eqv". iApply mutex_iff. iIntros "!>" (??[IH ?]?).
    rewrite !/⟦ mlist' _ _ ⟧(_) /=.
    have ?: Deriv ih δ'. { by apply Deriv_mono=> ?[??]. }
    iSplit; (iIntros "[hd[%[$ mtl]]]"; iSplitL "hd"; [by iApply "eqv"|]);
      iModIntro; iRevert "mtl"; [iApply bi.and_elim_l|iApply bi.and_elim_r];
      by iApply IH.
  Qed.

  (** Try to acquire the lock of [mlist] *)
  Lemma twp_try_acquire_loop_mlist {Φx l} {k : nat} :
    [[{ ⟦ mlist Φx l ⟧ }]][mutex_wsatid]
      try_acquire_loop_mutex #k #l
    [[{ b, RET #b; if negb b then True else
        ⟦ Φx (l +ₗ 1) ⟧ ∗ ∃ l', (l +ₗ 2) ↦ #l' ∗ ⟦ mlist Φx l' ⟧ }]].
  Proof.
    iIntros (Ψ) "/= #m →Ψ". iApply twp_fupd.
    wp_apply (twp_try_acquire_loop_mutexd with "m"). iIntros ([|]); last first.
    { iIntros (?). by iApply "→Ψ". }
    rewrite /sem /=. iIntros "[Φx (% & >↦ & #m')]". iApply "→Ψ". by iFrame.
  Qed.

  (** Release the lock of [mlist] *)
  Lemma twp_release_mlist {Φx l} :
    [[{ ⟦ mlist Φx l ⟧ ∗ ⟦ Φx (l +ₗ 1) ⟧ ∗
        ∃ l', (l +ₗ 2) ↦ #l' ∗ ⟦ mlist Φx l' ⟧ }]][mutex_wsatid]
      release_mutex #l
    [[{ RET #(); True }]].
  Proof.
    iIntros (Ψ) "(#m & Φx & %l' & ↦ & #mtl) →Ψ".
    wp_apply (twp_release_mutexd with "[Φx ↦]"); [|done]. iSplit; [done|].
    rewrite /sem /=. by iFrame.
  Qed.

  (** Iterate over [mlist] *)
  Definition iter_mlist : val := rec: "self" "f" "k" "c" "l" :=
    if: !"c" ≤ #0 then #true else
      if: try_acquire_loop_mutex "k" "l" then
        "f" ("l" +ₗ #1);; let: "l'" := !("l" +ₗ #2) in release_mutex "l";;
        "c" <- !"c" - #1;; "self" "f" "k" "c" "l'"
      else #false.
  Lemma twp_iter_mlist {Φx c l} {f : val} {k n : nat} :
    (∀ l', [[{ ⟦ Φx (l' +ₗ 1) ⟧ }]][mutex_wsatid] f #(l' +ₗ 1)
      [[{ RET #(); ⟦ Φx (l' +ₗ 1) ⟧ }]]) -∗
    [[{ c ↦ #n ∗ ⟦ mlist Φx l ⟧ }]][mutex_wsatid]
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
  Lemma bor_bor_deref {α β l Φx q} : β ⊑□ α -∗
    [[{ q.[β] ∗ nbord α (∃ l', ▷ l ↦ #l' ∗ cif_bor β (Φx l'))%n }]]
      [pborrow_wsatid bupd]
      !#l
    [[{ l', RET #l'; q.[β] ∗ nborcd β (Φx l') }]].
  Proof.
    iIntros "#⊑ %Ψ !> [[β β'] b] →Ψ".
    iMod (lft_sincl_live_acc with "⊑ β'") as (?) "[α →β']".
    iMod (nbord_open (M:=bupd) with "α b") as "[o big]". rewrite /sem /=.
    iDestruct "big" as (l') "[>↦ b']". iApply twpw_fupdw_nonval; [done|].
    wp_load. iModIntro.
    iMod (nbord_reborrow (M:=bupd) α with "β b'") as "[β[b' →b']]".
    iMod (nobord_subdiv (M:=bupd) [] with "[] o [] [↦ →b']") as "[α _]"=>/=.
    { iApply lft_sincl_refl. } { done. }
    { iIntros "† _". iModIntro. iExists _. iFrame "↦". by iApply "→b'". }
    iModIntro. iApply "→Ψ". iFrame "β". iDestruct ("→β'" with "α") as "$".
    iApply nborc_lft; [|done]. iApply lft_sincl_meet_intro; [|done].
    iApply lft_sincl_refl.
  Qed.

  (** Dereference a nested prophetic mutable reference *)
  Lemma pbor_pbor_deref {X η ξ α β l Φxx q} {x : X} : β ⊑□ α -∗
    [[{ q.[β] ∗
        pbord α ((x, ξ)' : _ *'ₛ prvarₛ _) η
          (λ '(x', ξ')', ∃ l', ▷ l ↦ #l' ∗ cif_pbor β x' ξ' (Φxx l'))%n }]]
      [pborrow_wsatid bupd]
      !#l
    [[{ l', RET #l';
        q.[β] ∗ ∃ ξ' : prvar X,
          ⟨π, π η = (π ξ', ξ)'⟩ ∗ pborcd β x ξ' (Φxx l') }]].
  Proof.
    iIntros "#⊑ %Ψ !> [[β β'] b] →Ψ".
    iMod (lft_sincl_live_acc with "⊑ β'") as (?) "[α →β']".
    iMod (pbord_open (M:=bupd) with "α b") as "/=[o big]".
    rewrite /sem /=. iDestruct "big" as (l') "[>↦ b']".
    iApply twpw_fupdw_nonval; [done|]. wp_load. iModIntro.
    iMod (pobord_pbord_reborrow (TY:=nsynty) (M:=bupd) (λ _, (_,_)' : _ *'ₛ _)
      with "o β b' [↦]") as (?) "[α[β[obs c]]]".
    { iIntros "/=% _ ? !>". iExists _. iFrame. }
    iModIntro. iApply "→Ψ". iFrame "β". iDestruct ("→β'" with "α") as "$".
    iExists _. iFrame "obs". iApply pborc_lft; [|done].
    iApply lft_sincl_meet_intro; [done|]. iApply lft_sincl_refl.
  Qed.

  (** Load from an immutable shared borrow *)
  Lemma imbor_load {l α q} {n : Z} :
    [[{ q.[α] ∗ invd nroot (cif_bor α (▷ l ↦ #n)) }]]
      [inv_wsatid ∗ pborrow_wsatid bupd]
      !#l
    [[{ RET #n; q.[α] }]].
  Proof.
    iIntros (Φ) "[α #i] →Φ". iMod (invd_acc with "i") as "[b cl]"; [done|].
    rewrite /sem /=. iMod (nbord_open (M:=bupd) with "α b") as "[o ↦]".
    rewrite /sem /=. iDestruct "↦" as ">↦". wp_load. iModIntro.
    iMod (nobord_close (M:=bupd) with "o [$↦ //]") as "[α b]".
    rewrite nborc_nbor. iMod ("cl" with "b") as "_". iModIntro. by iApply "→Φ".
  Qed.

  (** Shared borrow of a mutex *)
  Definition mutex_bor α l Px :=
    invd nroot (cif_bor α ((▷ l ↦ #false ∗ cif_bor α Px) ∨ ▷ l ↦ #true)).

  (** Create a shared borrow and a lender of a mutex *)
  Lemma mutex_bor_lend_new {α l Px b q} :
    l ↦ #b -∗ ⟦ Px ⟧ -∗ q.[α] =[inv_wsatid ∗ pborrow_wsatid bupd]=∗
      mutex_bor α l Px ∗ nlendd α (∃ b', ▷ l ↦ #b' ∗ Px)%n ∗ q.[α].
  Proof.
    iIntros "↦ Px α".
    iMod (nborc_nlend_new (M:=bupd) with "[↦ Px]") as "[b $]"; [by iFrame|].
    iMod (nborcd_open with "α b") as "[o big]". rewrite /sem /=.
    iDestruct "big" as (b') "[↦ Px]".
    iMod (nobord_subdiv (M:=bupd) [∃ b', ▷ l ↦ #b'; Px]%n
      with "[] o [↦ Px] []") as "[α[b[b' _]]]"; rewrite /sem /=.
    { iApply lft_sincl_refl. } { iSplitL "↦"; iFrame. }
    { by iIntros "_ [[% $][$ _]]". }
    iMod (nborcd_open with "α b") as "[o ↦]".
    iMod (nobord_subdiv (M:=bupd)
      [(▷ l ↦ #false ∗ cif_bor α Px) ∨ ▷ l ↦ #true]%n with "[] o [↦ b'] []")
      as "[$[b _]]"; rewrite /sem /=. { iApply lft_sincl_refl. }
    { iSplit; [|done]. rewrite nborc_nbor.
      iDestruct "↦" as ([|]) "↦"; [|iLeft]; iFrame. }
    { by iIntros "_ [[[$ _]|$]_]". }
    rewrite nborc_nbor. by iMod (inv'_alloc with "[b]") as "$".
  Qed.

  (** ** On derivability *)

  Local Lemma inv'_sep_comm' `{!Deriv ih δ} {N Px Qx} :
    inv' δ N (Px ∗ Qx)%n ⊢ inv' δ N (Qx ∗ Px)%n.
  Proof.
    iApply inv'_iff. iIntros "!>" (????). rewrite /psem /= bi.sep_comm.
    iApply bi.wand_iff_refl.
  Qed.
  Lemma inv'_sep_comm `{!Deriv ih δ} {N Px Qx} :
    inv' δ N (Px ∗ Qx)%n ⊣⊢ inv' δ N (Qx ∗ Px)%n.
  Proof. apply bi.equiv_entails. split; exact inv'_sep_comm'. Qed.

  Local Lemma inv'_inv'_sep_comm' `{!Deriv ih δ} {N N' Px Qx} :
    inv' δ N (cif_inv N' (Px ∗ Qx)) ⊢ inv' δ N (cif_inv N' (Qx ∗ Px)).
  Proof.
    iApply inv'_iff. iIntros "!>" (????). rewrite /psem /= inv'_sep_comm.
    iApply bi.wand_iff_refl.
  Qed.
  Lemma inv'_inv'_sep_comm `{!Deriv ih δ} {N N' Px Qx} :
    inv' δ N (cif_inv N' (Px ∗ Qx)) ⊣⊢ inv' δ N (cif_inv N' (Qx ∗ Px)).
  Proof. apply bi.equiv_entails. split; exact inv'_inv'_sep_comm'. Qed.

  Local Lemma inv'_bor_lft' `{!Deriv ih δ} {N α β Px} :
    α ⊑□ β -∗ β ⊑□ α -∗ inv' δ N (cif_bor α Px) -∗ inv' δ N (cif_bor β Px).
  Proof.
    iIntros "#? #?". iApply inv'_iff. iIntros "!>" (????). rewrite /psem /=.
    iSplit; by iApply nbor_lft.
  Qed.
  Lemma inv'_bor_lft `{!Deriv ih δ} {N α β Px} :
    α ⊑□ β -∗ β ⊑□ α -∗ inv' δ N (cif_bor α Px) ∗-∗ inv' δ N (cif_bor β Px).
  Proof. iIntros "#? #?". iSplit; by iApply inv'_bor_lft'. Qed.
End verify.
