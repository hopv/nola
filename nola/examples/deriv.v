(** * Logic with derivability *)

From nola.iris Require Export cif inv_deriv pborrow_deriv.
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
  | cifs_inv _ | cifs_mutex _
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
  Context `{!inv'GS cifOF Σ, !mutexGS cifOF Σ, !pborrowGS nsynty cifOF Σ,
    !heapGS_gen hlc Σ}.
  Implicit Type δ : judg Σ → iProp Σ.

  (** ** [bsem]: Base semantics *)
  Definition bsem δ s :
    (idom s -d> iProp Σ) → (cdom s -d> cif Σ) → dataOF s $oi Σ → iProp Σ :=
    match s with
    | cifs_pointsto l dq v => λ _ _ _, l ↦{dq} v
    | cifs_inv N => λ _ Pxs _, inv' δ N (Pxs ())
    | cifs_mutex l => λ _ Pxs _, mutex δ l (Pxs ())
    | cifs_bor α => λ _ Pxs _, nbor δ α (Pxs ())
    | cifs_obor α q => λ _ Pxs _, nobor δ α q (Pxs ())
    | cifs_lend α => λ _ Pxs _, nlend δ α (Pxs ())
    | cifs_pbor α x ξ => λ _ Φx _, pbor δ α x ξ Φx
    | cifs_pobor α q ξ => λ _ Φx _, pobor δ α q ξ Φx
    | cifs_plend α xπ => λ _ Φx _, plend δ α xπ Φx
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
  Definition ilist_gen N (Φx : loc → cif Σ) Ilist l : cif Σ :=
    cif_inv N (Φx l) ∗ cif_inv N (∃ l', (l +ₗ 1) ↦ #l' ∗ Ilist l').
  #[export] Instance ilist_gen_productive {N Φx} :
    Productive (ilist_gen N Φx).
  Proof.
    move=>/= n ????. unfold ilist_gen. do 2 f_equiv. destruct n as [|n]=>//=.
    f_equiv=> ?. by f_equiv.
  Qed.
  Definition ilist' N (Φx : loc → cif Σ) : loc → cif Σ :=
    profix (ilist_gen N Φx).
  Definition ilist N (Φx : loc → cif Σ) : loc → cif Σ :=
    ilist_gen N Φx (ilist' N Φx).
  (** Unfold [ilist'] *)
  Lemma ilist'_unfold {N Φx l} : ilist' N Φx l ≡ ilist N Φx l.
  Proof.
    move=> ?. apply cit_proeqa, (proeqa_fun (PRF:=λ _, _)), profix_unfold.
  Qed.
  (** [ilist_gen] is non-expansive *)
  #[export] Instance ilist_gen_ne {N} :
    NonExpansive2
      (ilist_gen N : (loc -d> cif Σ) → (loc -d> cif Σ) → loc -d> cif Σ).
  Proof. unfold ilist_gen=> ????????. (do 3 f_equiv)=> ?. do 2 f_equiv. Qed.
  #[export] Instance ilist_gen_proper {N} :
    Proper ((≡) ==> (≡) ==> (≡))
      (ilist_gen N : (loc -d> cif Σ) → (loc -d> cif Σ) → loc -d> cif Σ).
  Proof. apply ne_proper_2, _. Qed.
  (** [ilist'] is non-expansive *)
  #[export] Instance ilist'_ne {N} :
    NonExpansive (ilist' N : (loc -d> cif Σ) → loc -d> cif Σ).
  Proof.
    move=> n ???. apply: (profix_proper (PR:=funPR (λ _ : loc, cif Σ))).
    { apply (dist_equivalence (A:=_ -d> _)). }
    { move=> ?? eq ?/=. f_equiv=>/= ?. apply eq. }
    move=> ???. by f_equiv.
  Qed.
  #[export] Instance ilist'_proper {N} :
    Proper ((≡) ==> (≡)) (ilist' N : (loc -d> cif Σ) → loc -d> cif Σ).
  Proof. apply ne_proper, _. Qed.
  #[export] Instance ilist_ne {N} :
    NonExpansive (ilist N : (loc -d> cif Σ) → loc -d> cif Σ).
  Proof. unfold ilist=> ????. f_equiv=>//. by f_equiv. Qed.
  #[export] Instance ilist_proper {N} :
    Proper ((≡) ==> (≡)) (ilist N : (loc -d> cif Σ) → loc -d> cif Σ).
  Proof. apply ne_proper, _. Qed.

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
  Local Lemma inv'_ilisti_iff `{!Deriv ih δ} {N Φx Ψx l} :
    □ (∀ l' δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ →
      inv' δ' N (Φx l') ∗-∗ inv' δ' N (Ψx l')) -∗
      inv' δ N (∃ l', (l +ₗ 1) ↦ #l' ∗ ilist' N Φx l')%cif ∗-∗
        inv' δ N (∃ l', (l +ₗ 1) ↦ #l' ∗ ilist' N Ψx l')%cif.
  Proof.
    move: l. apply Deriv_ind=> δ' ??. iIntros "#eqv".
    iSplit; iApply inv'_acsr; iIntros "!> /=" (??[IH ?]?);
      rewrite -(wand_iff_mod_acsr (M:=fupd _ _));
      (iModIntro; iSplit; iIntros "/=[%[$ il]]";
      rewrite !ilist'_unfold /= !to_of_cif; iDestruct "il" as "[ihd itl]";
        (iSplit; [|by iApply IH]));
      iApply ("eqv" with "[%] [//] ihd"); by apply Deriv_mono=> ?[??].
  Qed.
  Lemma ilist_acsr `{!Deriv ih δ} {N Φx Ψx l} :
    □ (∀ l' δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ →
      mod_acsr (fupd ∅ ∅) ⟦ Φx l' ⟧(δ') ⟦ Ψx l' ⟧(δ') ∧
      mod_acsr (fupd ∅ ∅) ⟦ Ψx l' ⟧(δ') ⟦ Φx l' ⟧(δ')) -∗
      ⟦ ilist N Φx l ⟧(δ) ∗-∗ ⟦ ilist N Ψx l ⟧(δ).
  Proof.
    iIntros "#eqv /=".
    iSplit; (iIntros "[ihd itl]"; iSplitL "ihd"; rewrite !to_of_cif;
      [by iApply (inv'_acsr_iff (Φx:=Φx))|]);
      iApply (inv'_ilisti_iff with "[] itl"); iIntros "!>" (????);
      [iApply bi.wand_iff_sym|]; by iApply inv'_acsr_iff.
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
    move=> ?. apply cit_proeqa, (proeqa_fun (PRF:=λ _, _)), profix_unfold.
  Qed.

  (** Convert the predicate of [mlist] using [mod_iff] *)
  Lemma mlist_iff `{!Deriv ih δ} {Φx Ψx l} :
    □ (∀ l' δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ →
      mod_iff (fupd ⊤ ⊤) ⟦ Φx l' ⟧(δ') ⟦ Ψx l' ⟧(δ')) -∗
      ⟦ mlist Φx l ⟧(δ) ∗-∗ ⟦ mlist Ψx l ⟧(δ).
  Proof.
    move: l. apply Deriv_ind=>/= ???. iIntros "#eqv". iApply mutex_iff.
    iIntros "!>" (??[IH ?]?). rewrite !to_of_cif /=.
    have ?: Deriv ih δ'. { by apply Deriv_mono=> ?[??]. }
    iSplit; (iIntros "[hd[%[$ mtl]]]"; iSplitL "hd"; [by iApply "eqv"|]);
      iModIntro; iRevert "mtl"; [iApply bi.and_elim_l|iApply bi.and_elim_r];
      rewrite !mlist'_unfold; by iApply IH.
  Qed.

  (** ** On derivability *)

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
    inv' δ N (cif_inv N' (Px ∗ Qx)) ⊢ inv' δ N (cif_inv N' (Qx ∗ Px)).
  Proof.
    iApply inv'_iff. iIntros "!> /=" (????). rewrite !to_of_cif inv'_sep_comm.
    iApply bi.wand_iff_refl.
  Qed.
  Lemma inv'_inv'_sep_comm `{!Deriv ih δ} {N N' Px Qx} :
    inv' δ N (cif_inv N' (Px ∗ Qx)) ⊣⊢ inv' δ N (cif_inv N' (Qx ∗ Px)).
  Proof. apply bi.equiv_entails. split; exact inv'_inv'_sep_comm'. Qed.

  Local Lemma inv'_bor_lft' `{!Deriv ih δ} {N α β Px} :
    α ⊑□ β -∗ β ⊑□ α -∗ inv' δ N (cif_bor α Px) -∗ inv' δ N (cif_bor β Px).
  Proof.
    iIntros "#? #?". iApply inv'_iff. iIntros "!>" (????). rewrite /⟦⟧(_) /=.
    iSplit; by iApply nbor_lft.
  Qed.
  Lemma inv'_bor_lft `{!Deriv ih δ} {N α β Px} :
    α ⊑□ β -∗ β ⊑□ α -∗ inv' δ N (cif_bor α Px) ∗-∗ inv' δ N (cif_bor β Px).
  Proof. iIntros "#? #?". iSplit; by iApply inv'_bor_lft'. Qed.
End verify.
