(** * Showcase logic *)

From nola.iris Require Export ciprop inv_deriv pborrow_deriv.
From nola.bi Require Import util.
From nola.heap_lang Require Export notation proofmode lib.mutex.
From nola.examples Require Export nsynty.
Import ProdNotation WpwNotation iPropAppNotation PintpNotation IntpNotation
  NsyntyNotation.

Implicit Type (N : namespace) (l : loc) (b : bool) (α : lft) (q : Qp)
  (X Y : nsynty).

(** ** Preliminaries *)

(** [sel]: Selector *)
Variant sel :=
| (** Invariant *) cips_inv (N : namespace)
| (** Mutex *) cips_mutex (l : loc)
| (** Non-prophetic closed borrower *) cips_borc (α : lft)
| (** Non-prophetic borrower *) cips_bor (α : lft)
| (** Non-prophetic open borrower *) cips_obor (α : lft) (q : Qp)
| (** Non-prophetic lender *) cips_lend (α : lft)
| (** Prophetic closed borrower *)
    cips_pborc {X} (α : lft) (x : X) (ξ : prvar X)
| (** Prophetic borrower *) cips_pbor {X} (α : lft) (x : X) (ξ : prvar X)
| (** Prophetic open borrower *) cips_pobor {X} (α : lft) (q : Qp) (ξ : prvar X)
| (** Prophetic lender *) cips_plend {X} (α : lft) (xπ : clair nsynty X).
(** [idom]: Domain for inductive parts *)
Definition idom (_ : sel) : Type := Empty_set.
(** [cdom]: Domain for coinductive parts *)
Definition cdom (s : sel) : Type := match s with
  | cips_inv _ | cips_mutex _
    | cips_borc _ | cips_bor _ | cips_obor _ _ | cips_lend _ => unit
  | @cips_pborc X _ _ _ | @cips_pbor X _ _ _ | @cips_pobor X _ _ _
    | @cips_plend X _ _ => X
  end.
(** [dataOF]: Data [oFunctor] *)
Definition dataOF (_ : sel) : oFunctor := unitO.
(** [dataOF] is contractive *)
Fact dataOF_contractive {s} : oFunctorContractive (dataOF s).
Proof. exact _. Qed.

(** ** [ciProp]: Proposition *)
Notation ciProp Σ := (ciProp idom cdom dataOF Σ).
Notation ciPropOF := (ciPropOF idom cdom dataOF).

(** [ciPropOF] is contractive *)
Fact ciPropOF_contractive : oFunctorContractive ciPropOF.
Proof. exact _. Qed.

(** Construct [ciProp] *)
Section ciProp.
  Context {Σ : gFunctors}.
  Implicit Type Px : ciProp Σ.
  (** Invariant *)
  Definition cip_inv N Px : ciProp Σ :=
    cip_custom (cips_inv N) nullary (unary Px) ().
  (** Mutex *)
  Definition cip_mutex l Px : ciProp Σ :=
    cip_custom (cips_mutex l) nullary (unary Px) ().
  (** Non-prophetic closed borrower *)
  Definition cip_borc α Px : ciProp Σ :=
    cip_custom (cips_borc α) nullary (unary Px) ().
  (** Non-prophetic borrower *)
  Definition cip_bor α Px : ciProp Σ :=
    cip_custom (cips_bor α) nullary (unary Px) ().
  (** Non-prophetic open borrower *)
  Definition cip_obor α q Px : ciProp Σ :=
    cip_custom (cips_obor α q) nullary (unary Px) ().
  (** Non-prophetic lender *)
  Definition cip_lend α Px : ciProp Σ :=
    cip_custom (cips_lend α) nullary (unary Px) ().
  (** Prophetic closed borrower *)
  Definition cip_pborc {X} α x ξ (Φx : X -d> ciProp Σ) : ciProp Σ :=
    cip_custom (@cips_pborc X α x ξ) nullary Φx ().
  (** Prophetic borrower *)
  Definition cip_pbor {X} α x ξ (Φx : X -d> ciProp Σ) : ciProp Σ :=
    cip_custom (@cips_pbor X α x ξ) nullary Φx ().
  (** Prophetic open borrower *)
  Definition cip_pobor {X} α q ξ (Φx : X -d> ciProp Σ) : ciProp Σ :=
    cip_custom (@cips_pobor X α q ξ) nullary Φx ().
  (** Prophetic lender *)
  Definition cip_plend {X} α xπ (Φx : X -d> ciProp Σ) : ciProp Σ :=
    cip_custom (@cips_plend X α xπ) nullary Φx ().

  (** The custom constructors are non-expansive *)
  #[export] Instance cip_inv_ne {N} : NonExpansive (cip_inv N).
  Proof. move=> ????. apply cip_custom_ne; solve_proper. Qed.
  #[export] Instance cip_mutex_ne {l} : NonExpansive (cip_mutex l).
  Proof. move=> ????. apply cip_custom_ne; solve_proper. Qed.
  #[export] Instance cip_borc_ne {α} : NonExpansive (cip_borc α).
  Proof. move=> ????. apply cip_custom_ne; solve_proper. Qed.
  #[export] Instance cip_bor_ne {α} : NonExpansive (cip_bor α).
  Proof. move=> ????. apply cip_custom_ne; solve_proper. Qed.
  #[export] Instance cip_obor_ne {α q} : NonExpansive (cip_obor α q).
  Proof. move=> ????. apply cip_custom_ne; solve_proper. Qed.
  #[export] Instance cip_lend_ne {α} : NonExpansive (cip_lend α).
  Proof. move=> ????. apply cip_custom_ne; solve_proper. Qed.
  #[export] Instance cip_pborc_ne {X α x ξ} : NonExpansive (@cip_pborc X α x ξ).
  Proof. move=> ????. apply cip_custom_ne; solve_proper. Qed.
  #[export] Instance cip_pbor_ne {X α x ξ} : NonExpansive (@cip_pbor X α x ξ).
  Proof. move=> ????. apply cip_custom_ne; solve_proper. Qed.
  #[export] Instance cip_pobor_ne {X α q ξ} : NonExpansive (@cip_pobor X α q ξ).
  Proof. move=> ????. apply cip_custom_ne; solve_proper. Qed.
  #[export] Instance cip_plend_ne {X α xπ} : NonExpansive (@cip_plend X α xπ).
  Proof. move=> ????. apply cip_custom_ne; solve_proper. Qed.
End ciProp.

(** ** [judg]: Judgment *)
Definition judg Σ : ofe :=
  (leibnizO namespace * ciProp Σ + ciProp Σ * ciProp Σ + ciProp Σ * ciProp Σ +
    sigT (A:=nsynty *' nsynty) (λ '(X, Y)',
      leibnizO (clair nsynty X *' clair nsynty Y) *
      (X -d> ciProp Σ) * (Y -d> ciProp Σ)))%type.
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
  InvPreDeriv (ciProp Σ) (judg Σ) := INV_PRE_DERIV inv_jacsr.
#[export] Instance judg_mutex_pre_deriv {Σ} :
  MutexPreDeriv (ciProp Σ) (judg Σ) := MUTEX_PRE_DERIV mutex_jiff.
#[export] Instance judg_pborrow_pre_deriv {Σ} :
  PborrowPreDeriv nsynty (ciProp Σ) (judg Σ) :=
  PBORROW_PRE_DERIV pborrow_jto (@pborrow_jlto _).

Section intp.
  Context `{!inv'GS ciPropOF Σ, !mutexGS ciPropOF Σ,
    !pborrowGS nsynty ciPropOF Σ}.
  Implicit Type δ : judg Σ → iProp Σ.

  (** ** [bintp]: Base interpretation *)
  Definition bintp δ s :
    (idom s -d> iProp Σ) → (cdom s -d> ciProp Σ) → dataOF s $oi Σ → iProp Σ :=
    match s with
    | cips_inv N => λ _ Pxs _, inv' δ N (Pxs ())
    | cips_mutex l => λ _ Pxs _, mutex δ l (Pxs ())
    | cips_borc α => λ _ Pxs _, nborc δ α (Pxs ())
    | cips_bor α => λ _ Pxs _, nbor δ α (Pxs ())
    | cips_obor α q => λ _ Pxs _, nobor δ α q (Pxs ())
    | cips_lend α => λ _ Pxs _, nlend δ α (Pxs ())
    | cips_pborc α x ξ => λ _ Φx _, pborc δ α x ξ Φx
    | cips_pbor α x ξ => λ _ Φx _, pbor δ α x ξ Φx
    | cips_pobor α q ξ => λ _ Φx _, pobor δ α q ξ Φx
    | cips_plend α xπ => λ _ Φx _, plend δ α xπ Φx
    end.

  (** [bintp] is non-expansive *)
  #[export] Instance bintp_ne `{!NonExpansive δ} {s} :
    NonExpansive3 (bintp δ s).
  Proof. case s; solve_proper. Qed.

  (** Parameterized interpretation of [ciProp] *)
  #[export] Instance ciProp_dintp : Dintp (judg Σ) (ciProp Σ) (iProp Σ) :=
    DINTP (λ δ, cip_intp (bintp δ)).

  (** [ciProp_intp] is non-expansive *)
  Fact ciProp_intp_ne `{!NonExpansive δ} : NonExpansive ⟦⟧(δ)@{ciProp Σ}.
  Proof. exact _. Qed.

  Context `{!heapGS_gen hlc Σ}.

  (** [judg_intp]: Judgment interpretation *)
  Definition judg_intp δ (J : judg Σ) := match J with
    | inl (inl (inl (N, Px))) => inv_acsr ⟦⟧(δ) N ⟦ Px ⟧(δ)
    | inl (inl (inr (Px, Qx))) => mod_iff (fupd ⊤ ⊤) ⟦ Px ⟧(δ) ⟦ Qx ⟧(δ)
    | inl (inr (Px, Qx)) => ⟦ Px ⟧(δ) ==∗ ⟦ Qx ⟧(δ)
    | inr (existT (X, Y)' ((xπ, yπ)', Φx, Ψx)) =>
        plend_body ⟦ ⟧(δ) xπ Φx ==∗ plend_body ⟦ ⟧(δ) yπ Ψx
    end%I.
  Local Instance judg_intp_ne `{!NonExpansive δ} : NonExpansive (judg_intp δ).
  Proof.
    move=> ? _ _[_ _[_ _[|]|]|].
    - move=> [??][??][/=/leibniz_equiv_iff<- ?]. solve_proper.
    - move=> [??][??][/=??]. solve_proper.
    - move=> [??][??]/=[??]. solve_proper.
    - move=> [?[[[??]?]?]][?[[[??]?]?]][/=?]. subst=>/=.
      move=> [/=[/=/leibniz_equiv_iff[<-<-]?]?]. solve_proper.
  Qed.
  #[export] Instance judg_dintp : Dintp (judg Σ) (judg Σ) (iProp Σ) :=
    DINTP judg_intp.
  Canonical judgJ : judgi (iProp Σ) := Judgi (judg Σ).

  #[export] Instance judg_inv_deriv : InvDeriv ciPropOF Σ judgJ.
  Proof. done. Qed.
  #[export] Instance judg_mutex_deriv : MutexDeriv ciPropOF Σ judgJ.
  Proof. done. Qed.
  #[export] Instance judg_pborrow_deriv : PborrowDeriv nsynty ciPropOF Σ judgJ.
  Proof. done. Qed.
End intp.

(** ** Linked list mutation *)

(** Target function *)
Definition iter_ilist : val := rec: "self" "f" "c" "l" :=
  if: !"c" = #0 then #() else
    "f" "l";; "c" <- !"c" - #1;; "self" "f" "c" (!("l" +ₗ #1)).

Section verify.
  Context `{!inv'GS ciPropOF Σ, !mutexGS ciPropOF Σ,
    !pborrowGS nsynty ciPropOF Σ, !heapGS_gen hlc Σ}.
  Implicit Type Φx Ψx : loc → ciProp Σ.

  (** [ilist]: Syntactic proposition for a list *)
  Definition ilist_gen N Φx Ilist' l : ciProp Σ :=
    cip_inv N (Φx l) ∗ cip_inv N (Ilist' N Φx l).
  Definition ilist'_gen N Φx Ilist' l : ciProp Σ :=
    ∃ l', ▷ (l +ₗ 1) ↦ #l' ∗ ilist_gen N Φx Ilist' l'.
  CoFixpoint ilist' N Φx : loc → ciProp Σ := ilist'_gen N Φx ilist'.
  Definition ilist N Φx : loc → ciProp Σ := ilist_gen N Φx ilist'.

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

  (** Termination of [iter] *)
  Lemma twp_iter_list {N Φx c l} {f : val} {n : nat} :
    (∀ l', [[{ invd N (Φx l') }]][inv_wsatid] f #l' @ ↑N
      [[{ RET #(); True }]]) -∗
    [[{ c ↦ #n ∗ ⟦ ilist N Φx l ⟧ }]][inv_wsatid]
      iter_ilist f #c #l @ ↑N
    [[{ RET #(); c ↦ #0 }]].
  Proof.
    unfold intp. iIntros "#f" (Ψ) "!> /=[c↦ #[ihd itl]] →Ψ".
    iInduction n as [|m] "IH" forall (l) "ihd itl".
    { wp_rec. wp_load. wp_pures. by iApply "→Ψ". }
    wp_rec. wp_load. wp_pures. wp_apply "f"; [done|]. iIntros "_". wp_load.
    wp_store. wp_op. wp_bind (! _)%E. have -> : (S m - 1)%Z = m by lia.
    iMod (invd_acc with "itl") as "/=[(%l' & >↦l' & #itlhd & #itltl) cl]/=";
      [done|].
    wp_load. iModIntro. iMod ("cl" with "[↦l']") as "_".
    { iExists _. iFrame "↦l'". by iSplit. }
    iModIntro. by iApply ("IH" with "c↦ →Ψ").
  Qed.
End verify.

(** ** Linked list mutation over a mutex *)

(** Target function *)
Definition iter_mlist : val := rec: "self" "f" "k" "c" "l" :=
  if: !"c" = #0 then #true else
    if: try_acquire_loop_mutex "k" "l" then
      "f" "l";; let: "l'" := !("l" +ₗ #1) in release_mutex "l";;
      "c" <- !"c" - #1;; "self" "f" "k" "c" "l'"
    else #false.

Section verify.
  Context `{!inv'GS ciPropOF Σ, !mutexGS ciPropOF Σ,
    !pborrowGS nsynty ciPropOF Σ, !heapGS_gen hlc Σ}.
  Implicit Type Φx : loc → ciProp Σ.

  (** [mlist]: Syntactic proposition for a list with a mutex *)
  Definition mlist_gen Φx Mlist' l : ciProp Σ :=
    cip_mutex l (Mlist' Φx l).
  Definition mlist'_gen Φx Mlist' l : ciProp Σ :=
    Φx l ∗ ∃ l', ▷ (l +ₗ 1) ↦ #l' ∗ mlist_gen Φx Mlist' l'.
  CoFixpoint mlist' Φx : loc → ciProp Σ := mlist'_gen Φx mlist'.
  Definition mlist Φx : loc → ciProp Σ := mlist_gen Φx mlist'.

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

  (** Termination of [iter_mlist] *)
  Lemma twp_iter_mlist {Φx c l} {f : val} {k n : nat} :
    (∀ l', [[{ ⟦ Φx l' ⟧ }]][mutex_wsatid] f #l'
      [[{ RET #(); ⟦ Φx l' ⟧ }]]) -∗
    [[{ c ↦ #n ∗ ⟦ mlist Φx l ⟧ }]][mutex_wsatid]
      iter_mlist f #k #c #l
    [[{ b, RET #b; if b then c ↦ #0 else ∃ n', c ↦ #n' }]].
  Proof.
    rewrite !/⟦ mlist _ _ ⟧ /=. iIntros "#f" (Ψ) "!> [c↦ #ml] →Ψ".
    iInduction n as [|m] "IH" forall (l) "ml".
    { wp_rec. wp_load. wp_pures. by iApply "→Ψ". }
    wp_rec. wp_load. wp_pures.
    wp_apply (twp_try_acquire_loop_mutexd with "ml"). iIntros ([|]); last first.
    { iIntros (?). wp_pure. iModIntro. iApply "→Ψ". by iExists _. }
    rewrite !/⟦ mlist' _ _ ⟧ /=. iIntros "[Φx[%[>↦ #mtl]]]". wp_pure.
    wp_apply ("f" with "Φx"). iIntros "Φx". wp_load. wp_pures.
    wp_apply (twp_release_mutexd with "[Φx ↦]").
    { iSplit; [done|]. rewrite !/⟦ mlist' _ _ ⟧ /=. by iFrame. }
    iIntros "_". wp_load. wp_store. have -> : (S m - 1)%Z = m by lia.
    by iApply ("IH" with "c↦ →Ψ").
  Qed.
End verify.
