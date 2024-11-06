(** * Core features *)

From nola.examples.rust_halt Require Export type.
Import ProdNotation PlistNotation BigSepPLNotation ModwNotation WpwNotation
  iPropAppNotation ProphNotation LftNotation CsemNotation.

Implicit Type (sz d : nat) (X : xty) (t : thread_id) (v : val) (e : expr)
  (l : loc) (α : lft) (CON : cifcon) (Σ : gFunctors).

Section type.
  Context `{!rust_haltGS CON Σ, !rust_haltC CON, rust_haltJ CON JUDG Σ,
    !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ), !rust_haltCS CON JUDG Σ}.

  (** ** Operations on type contexts *)

  (** Leak the head in [sub] *)
  Lemma sub_leak_hd {X Yl α vT Γ} :
    ⊢ sub (Xl:=X::Yl) α (vT ᵖ:: Γ) Γ (λ post '(_, yl)', post yl).
  Proof. rewrite sub_unseal. iIntros (????) "!>/= $ $ ? [_ $] //". Qed.
  (** Swap the head elements *)
  Lemma sub_swap_hd {X Y Zl α vT vT' Γ} :
    ⊢ sub (Xl:=X::Y::Zl) α (vT ᵖ:: vT' ᵖ:: Γ) (vT' ᵖ:: vT ᵖ:: Γ)
      (λ post '(x, y, zl)', post (y, x, zl)').
  Proof.
    rewrite sub_unseal. iIntros (???[?[??]]) "!>/= $ $ ? (? & ? & ?) !>".
    iExists (_,_,_)'. iFrame.
  Qed.
  (** Copy the head element under [Copy] *)
  Lemma sub_copy_hd {X Yl α vl T Γ} `{!Copy T} :
    ⊢ sub (Xl:=X::Yl) α (vl *◁ T ᵖ:: Γ) (vl *◁ T ᵖ:: vl *◁ T ᵖ:: Γ)
        (λ post '(x, zl)', post (x, x, zl)').
  Proof.
    rewrite sub_unseal. iIntros (? t ? [xπ ?]) "!>/= $ $ ? [[%d T] ?] !>".
    have ? : Persistent ⟦ T.1 t d xπ vl ⟧ᶜ by exact copy_persistent.
    iDestruct "T" as "#T". iExists (_,_,_)'. iFrame "T". iFrame.
  Qed.
  (** Modify the head element by subtyping *)
  Lemma sub_subty_hd {X Y Zl α vl T U f Γ} :
    subtyd T U f ⊢
      sub (Xl:=X::Zl) (Yl:=Y::_) α (vl *◁ T ᵖ:: Γ) (vl *◁ U ᵖ:: Γ)
        (λ post '(x, zl)', post (f x, zl)').
  Proof.
    rewrite subty_unseal sub_unseal.
    iIntros "[#TU _] !>/=" (????) "$ $ pre [[% T] Γ] !>". iExists (_,_)'.
    iDestruct ("TU" with "T") as "$". iFrame.
  Qed.
  Lemma sub_subty_frozen_hd {X Y Zl α β vl T U Γ} `{!Inj (=) (=) f} :
    subtyd T U f ⊢
      sub (Xl:=X::Zl) (Yl:=Y::_) α (vl *◁[†β] T ᵖ:: Γ) (vl *◁[†β] U ᵖ:: Γ)
        (λ post '(x, zl)', post (f x, zl)').
  Proof.
    rewrite subty_unseal sub_unseal.
    iIntros "[#TU _] !>/=" (????) "$ $ pre [→T Γ] !>". iExists (_,_)'.
    iFrame "pre Γ". iIntros "†". iMod ("→T" with "†") as (??) "[eqz T]".
    iExists _, _. iDestruct ("TU" with "T") as "$".
    iApply (proph_eqz_f with "eqz").
  Qed.

  (** ** Operations on lifetimes *)

  (** Allocate a new local lifetime *)
  Lemma type_lft_new {Xl Yl β Γi e Γo pre} :
    (∀ α, type β (^[α] ᵖ:: Γi) e Γo pre) ⊢
      type (Xl:=Xl) (Yl:=Yl) β Γi e Γo (λ post xl, pre post ((), xl)').
  Proof.
    rewrite type_unseal.
    iIntros "#type !>" (????) "β t pre Γi". iMod lft_alloc as (α ?) "α".
    iApply ("type" $! _ _ _ _ (_,_)' with "β t pre")=>/=. by iFrame.
  Qed.
  (** Use a local lifetime *)
  Lemma type_lft_use {Xl Yl α β Γi e Γo pre} :
    type (Xl:=Xl) (Yl:=Yl) (α ⊓ β) Γi e Γo pre ⊢
      type β (^[α] ᵖ:: Γi) e (λ v, ^[α] ᵖ:: Γo v)
        (λ post '(_, xl)', pre (λ yl, post ((), yl)') xl).
  Proof.
    rewrite type_unseal. iIntros "#type !>/=" (q ???) "β t pre [[$ α] Γi]".
    case (Qp.lower_bound 1 q) as [?[?[?[->->]]]]. iDestruct "α" as "[α α']".
    iDestruct "β" as "[β β']".
    iDestruct ("type" with "[$α $β //] t pre Γi") as "twp".
    iApply (twp_wand with "twp"). iIntros (?) ">(% & [$$] & $ & pre & Γo) !>".
    iExists (λ _,(), _)'. iFrame.
  Qed.
  (** End a lifetime *)
  Lemma sub_lft_end {Xl Yl α β Γi Γo pre} :
    □ ([†α] -∗ sub (Xl:=Xl) (Yl:=Yl) β Γi Γo pre) ⊢
      sub β (^[α] ᵖ:: Γi) Γo (λ post '(_, xl)', pre post xl).
  Proof.
    rewrite sub_unseal. iIntros "#sub !>/=" (????) "β t pre [[% α] Γi]".
    iMod (lft_kill with "α") as "†"=>//. iApply ("sub" with "† β t pre Γi").
  Qed.
  (** Retrieve a frozen object *)
  Lemma sub_retrieve {X Yl α β vl T Γ} `{!TyOp T β} :
    [†α] -∗ sub (Xl:=X::Yl) β (vl *◁[†α] T ᵖ:: Γ) (vl *◁ T ᵖ:: Γ) id.
  Proof.
    rewrite sub_unseal.
    iIntros "#† !>/=" (???[??]) "β $ pre [T Γ]".
    iMod ("T" with "†") as (??) "[eqz T]".
    iMod (ty_own_proph with "β T") as (???) "[ξl cl]".
    iMod ("eqz" with "[//] ξl") as "[ξl eq]". iMod ("cl" with "ξl") as "[$ T]".
    iModIntro. iExists (_,_)'. iFrame "T Γ".
    by iApply (proph_obs_impl2 with "pre eq")=> ??<-.
  Qed.

  (** ** Basic typing rules *)

  (** Pure execution *)
  Lemma type_pure {Xl Yl α Γi e e' Γo pre n φ} :
    PureExec φ n e e' → φ →
    type (Xl:=Xl) (Yl:=Yl) α Γi e' Γo pre ⊢ type α Γi e Γo pre.
  Proof.
    rewrite type_unseal=> ??. iIntros "#type !>" (????) "α t pre Γ".
    wp_pure _. iApply ("type" with "α t pre Γ").
  Qed.
  (** Binding *)
  Lemma type_bind {Xl Yl Zl α Γ Γ' Γ'' pre pre'} K e :
    type (Yl:=Yl) α Γ e Γ' pre -∗
    (∀ v, type α (Γ' v) (fill K (of_val v)) Γ'' pre') -∗
      type (Xl:=Xl) (Yl:=Zl) α Γ (fill K e) Γ'' (pre ∘ pre').
  Proof.
    rewrite type_unseal. iIntros "#type #type' !>" (????) "α t pre Γ".
    iApply twp_bind. iDestruct ("type" with "α t pre Γ") as "big".
    iApply (twp_wand with "big"). iIntros (?) ">(% & α & t & pre & Γ')".
    iApply ("type'" with "α t pre Γ'").
  Qed.
  (** Let expression *)
  Lemma type_let {Xl Yl Zl α Γ Γ' Γ'' x e e' pre pre'}
    `{!Closed (x :b: []) e'} :
    type (Yl:=Yl) α Γ e Γ' pre -∗
    (∀ v, type α (Γ' v) (subst' x v e') Γ'' pre') -∗
      type (Xl:=Xl) (Yl:=Zl) α Γ (let: x := e in e') Γ'' (pre ∘ pre').
  Proof.
    iIntros "#type #type'". iApply (type_bind [LetCtx x e'] with "type")=>/=.
    iIntros (?). by iApply (type_pure with "type'").
  Qed.
End type.

(** ** Recursive type *)

(** [ty_rec]: Recursive type *)
Definition ty_rec {CON Σ X} (F : ty CON Σ X → ty CON Σ X) `{!Productive F}
  : ty CON Σ X := profix F.

Section ty_rec.
  Context {CON Σ X} {F : ty CON Σ X → ty CON Σ X} `{!Productive F}.

  (** Unfold [ty_rec] *)
  Lemma ty_rec_unfold : @ty_rec CON Σ X F _ ≡ F (ty_rec F).
  Proof. exact profix_unfold. Qed.

  (** Uniqueness of [ty_rec] *)
  Lemma ty_rec_unique {T} : T ≡ F T → T ≡ ty_rec F.
  Proof. exact profix_unique. Qed.

  (** Approximate [ty_rec] by an iteration *)
  Lemma ty_rec_iter {k} : proeq k (ty_rec F) (F (Nat.iter k F inhabitant)).
  Proof. exact profix_iter. Qed.

  (** Equivalence between [ty_rec]s *)
  Lemma ty_rec_equiv {G : ty CON Σ X → ty CON Σ X} `{!Productive G} :
    (∀ T U, T ≡ U → F T ≡ G U) → ty_rec F ≡ ty_rec G.
  Proof. exact profix_proper. Qed.

  (** [Send] on [ty_rec], coinductively *)
  #[export] Instance ty_rec_send `{Send0 : !∀ T, Send T → Send (F T)} :
    Send (ty_rec F).
  Proof.
    move=> ??. apply equiv_proeq=> k. etrans; [by apply ty_rec_iter|].
    etrans; [|symmetry; by apply ty_rec_iter]. apply equiv_proeq, Send0.
    elim: k; [by move|exact _].
  Qed.
  (** [Sync] on [ty_rec], coinductively *)
  #[export] Instance ty_rec_sync `{Sync0 : !∀ T, Sync T → Sync (F T)} :
    Sync (ty_rec F).
  Proof.
    move=> ??. apply equiv_proeq=> k. etrans; [by apply ty_rec_iter|].
    etrans; [|symmetry; by apply ty_rec_iter]. apply equiv_proeq, Sync0.
    elim: k; [by move|exact _].
  Qed.

  Context `{!Csem CON JUDG Σ, !Jsem JUDG (iProp Σ)}.
  Implicit Type δ : JUDG -n> iProp Σ.

  (** Unfold and fold [ty_rec] in subtyping *)
  Lemma ty_rec_unfold_sub {δ} :
    ⊢ subty (X:=X) δ (ty_rec (CON:=CON) F) (F (ty_rec F)) id.
  Proof.
    erewrite subty_proper; [exact subty_refl|exact ty_rec_unfold|done..].
  Qed.
  Lemma ty_rec_fold_sub {δ} :
    ⊢ subty (X:=X) δ (F (ty_rec F)) (ty_rec (CON:=CON) F) id.
  Proof.
    erewrite subty_proper; [exact subty_refl|done|exact ty_rec_unfold|done].
  Qed.

  (** [Ty] on [ty_rec] *)
  #[export] Instance ty_rec_ty `{!∀ T, Ty (F T) sz} : Ty (ty_rec F) sz.
  Proof. by rewrite ty_rec_unfold. Qed.

  Context `{!rust_haltGS CON Σ, rust_haltJ CON JUDG Σ}.

  (** [Copy] on [ty_rec] *)
  #[export] Instance ty_rec_copy `{!∀ T, Copy (F T)} : Copy (ty_rec F).
  Proof. by rewrite ty_rec_unfold. Qed.

  (** [TyOp] on [ty_rec] *)
  Lemma ty_rec_ty_op_lt {Yl} (Ul : plist (ty CON Σ) Yl)
    `{TyOp0: !∀ d T, TyOpLt T α d → TCPlistForall (λ _ U, TyOpLt U α d) Ul →
        TyOpAt (F T) α d} {d} :
    TCPlistForall (λ _ U, TyOpLt U α d) Ul → TyOpAt (ty_rec F) α d.
  Proof.
    rewrite ty_rec_unfold=> OpUl. apply TyOp0; [|done]. rewrite ty_rec_unfold.
    move: OpUl. elim: d; [move=> ??; lia|]=> d IH OpUl d' ?.
    apply TyOp0; last first.
    { move: OpUl. apply TCPlistForall_mono=> ??. apply: TyOpLt_mono=>//=. lia. }
    have le : (d' ≤ d)%nat by lia. apply: TyOpLt_mono=>//.
    rewrite ty_rec_unfold. apply IH. move: OpUl. apply TCPlistForall_mono=> ??.
    apply: TyOpLt_mono=>//=. lia.
  Qed.
  Lemma ty_rec_ty_op `{!∀ d T, TyOpLt T α d → TyOpAt (F T) α d} :
    TyOp (ty_rec F) α.
  Proof. move=> ?. by apply (ty_rec_ty_op_lt ᵖ[]). Qed.
End ty_rec.
