(** * Core features *)

From nola.examples.rust_halt Require Export type.

Implicit Type X Y : xty.

Section type.
  Context `{!rust_haltGS CON Σ, !rust_haltC CON, !rust_haltJ CON JUDG Σ,
    !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ), !rust_haltCS CON JUDG Σ}.

  (** ** Operations on type contexts *)

  (** Leak *)
  Lemma sub_leak {Xl} Γ
    `{!TcxExtract (Xl:=Xl) (Yl:=Yl) (Zl:=Zl) Γ Γg Γr get getr} {α} :
    ⊢ sub α Γg Γr (λ post yl, post (getr yl)).
  Proof.
    rewrite sub_unseal. iIntros (????) "!>/= $ $ ?". rewrite tcx_extract.
    by iIntros "[_ $]".
  Qed.
  Lemma sub_leak_rest {Xl} Γ
    `{!TcxExtract (Xl:=Xl) (Yl:=Yl) (Zl:=Zl) Γ Γg Γr get getr} {α} :
    ⊢ sub α Γg Γ (λ post yl, post (get yl)).
  Proof.
    rewrite sub_unseal. iIntros (????) "!>/= $ $ ?". rewrite tcx_extract.
    by iIntros "[$ _]".
  Qed.
  (** Modify by subtyping *)
  Lemma sub_subty v {X Y T} U (f : X → Y) {α}
    `{!EtcxExtract (X:=X) (Yl:=Zl) (Zl:=Zl') (v ◁ T) Γ Γr get getr} :
    subtyd T U f ⊢
      sub α Γ (v ◁ U ᵖ:: Γr) (λ post zl, post (f (get zl), getr zl)').
  Proof.
    rewrite subty_unseal sub_unseal. iIntros "[#TU _] !>/=" (????) "$ $ pre".
    rewrite etcx_extract. iIntros "[[% T] Γr] !>". iFrame "pre Γr".
    by iDestruct ("TU" with "T") as "$".
  Qed.
  Lemma sub_subty_frozen v {X Y T} U f `{!@Inj X Y (=) (=) f} {α β}
    `{!EtcxExtract (X:=X) (Yl:=Zl) (Zl:=Zl') (v ◁[†α] T) Γ Γr get getr} :
    subtyd T U f ⊢
      sub β Γ (v ◁[†α] U ᵖ:: Γr) (λ post zl, post (f (get zl), getr zl)').
  Proof.
    rewrite subty_unseal sub_unseal. iIntros "[#TU _] !>/=" (????) "$ $ pre".
    rewrite etcx_extract. iIntros "[→T Γr] !>". iFrame "pre Γr". iIntros "†".
    iMod ("→T" with "†") as (??) "[eqz T]". iExists _, _.
    iDestruct ("TU" with "T") as "$". iApply (proph_eqz_f with "eqz").
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

  (** ** Operations on lifetimes *)

  (** Allocate a new local lifetime *)
  Lemma type_lft_new {Xl Yl β Γi e Γo pre} :
    (∀ α, type β (^[α] ᵖ:: Γi) e Γo pre) ⊢
      type (Xl:=Xl) (Yl:=Yl) β Γi e Γo (λ post xl, pre post ((), xl)').
  Proof.
    rewrite type_unseal.
    iIntros "#type !>" (????) "β t pre Γi". iMod lft_alloc as (α ?) "α".
    iApply ("type" with "β t pre"). by iFrame.
  Qed.
  (** Use a local lifetime *)
  Lemma type_lft_use α
    `{!EtcxExtract (Yl:=Xl) (Zl:=Xl') ^[α] Γi Γr get getr} {Yl β e Γo pre} :
    type (Yl:=Yl) (α ⊓ β) Γr e Γo pre ⊢
      type β Γi e (λ v, ^[α] ᵖ:: Γo v)
        (λ post xl, pre (λ yl, post ((), yl)') (getr xl)).
  Proof.
    rewrite type_unseal. iIntros "#type !>/=" (q ???) "β t pre Γi".
    rewrite etcx_extract. iDestruct "Γi" as "[[% α] Γr]".
    case (Qp.lower_bound 1 q) as [?[?[?[->->]]]]. iDestruct "α" as "[α $]".
    iDestruct "β" as "[β $]".
    iDestruct ("type" with "[$α $β //] t pre Γr") as "twp".
    iApply (twp_wand with "twp"). by iIntros (?) ">(% & [$$] & $ & $ & $) !>".
  Qed.
  (** Eternalize a lifetime *)
  Lemma sub_lft_eternal α
    `{!EtcxExtract (Yl:=Xl) (Zl:=Xl') ^[α] Γi Γr get getr} {Yl β Γo pre} :
    □ ((∀ α', α' ⊑□ α) -∗ sub (Yl:=Yl) β Γr Γo pre) ⊢
      sub β Γi Γo (λ post xl, pre post (getr xl)).
  Proof.
    rewrite sub_unseal. iIntros "#sub !>/=" (????) "β t pre Γi".
    rewrite etcx_extract. iDestruct "Γi" as "[[% α] Γr]".
    iMod (lft_eternalize_sincl with "α") as "∞"=>//.
    iApply ("sub" with "∞ β t pre Γr").
  Qed.
  Lemma type_lft_eternal α
    `{!EtcxExtract (Yl:=Xl) (Zl:=Xl') ^[α] Γi Γr get getr}
    {Yl Zl β Γi' e Γo pre pre'} :
    □ ((∀ α', α' ⊑□ α) -∗ sub (Yl:=Yl) β Γr Γi' pre) -∗
    type (Yl:=Zl) β Γi' e Γo pre' -∗
      type β Γi e Γo (λ post xl, pre (pre' post) (getr xl)).
  Proof.
    iIntros "#sub #type". iApply type_pre; last first.
    { iApply type_in; [|done]. by iApply sub_lft_eternal. } { done. }
  Qed.
  (** End a lifetime *)
  Lemma sub_lft_end α
    `{!EtcxExtract (Yl:=Xl) (Zl:=Xl') ^[α] Γi Γr get getr} {Yl β Γo pre} :
    □ ([†α] -∗ sub (Yl:=Yl) β Γr Γo pre) ⊢
      sub β Γi Γo (λ post xl, pre post (getr xl)).
  Proof.
    rewrite sub_unseal. iIntros "#sub !>/=" (????) "β t pre Γi".
    rewrite etcx_extract. iDestruct "Γi" as "[[% α] Γr]".
    iMod (lft_kill with "α") as "†"=>//. iApply ("sub" with "† β t pre Γr").
  Qed.
  Lemma type_lft_end α
    `{!EtcxExtract (Yl:=Xl) (Zl:=Xl') ^[α] Γi Γr get getr}
    {Yl Zl β Γi' e Γo pre pre'} :
    □ ([†α] -∗ sub (Yl:=Yl) β Γr Γi' pre) -∗ type (Yl:=Zl) β Γi' e Γo pre' -∗
      type β Γi e Γo (λ post xl, pre (pre' post) (getr xl)).
  Proof.
    iIntros "#sub #type". iApply type_pre; last first.
    { iApply type_in; [|done]. by iApply sub_lft_end. } { done. }
  Qed.
  (** Retrieve a frozen object *)
  Lemma sub_retrieve v α
    `{!EtcxExtract (X:=X) (Yl:=Yl) (Zl:=Zl) (v ◁[†α] T) Γ Γr get getr,
      !TyOp T β} :
    [†α] -∗ sub β Γ (v ◁ T ᵖ:: Γr) (λ post yl, post (get yl, getr yl)').
  Proof.
    rewrite sub_unseal. iIntros "#† !>/=" (????) "β $ pre".
    rewrite etcx_extract /=. iIntros "[→T Γr]".
    iMod ("→T" with "†") as (? xπ') "[eqz T]".
    iMod (ty_own_proph with "β T") as (???) "[ξl cl]".
    iMod ("eqz" with "[//] ξl") as "[ξl eq]". iMod ("cl" with "ξl") as "[$ T]".
    iModIntro. iExists (λ π, (xπ' π, _)')=>/=. iFrame "T Γr".
    by iApply (proph_obs_impl2 with "pre eq")=> ??<-.
  Qed.
End type.

(** ** Tactics for binding *)
Ltac type_reshape e tac :=
  lazymatch goal with
  | |- envs_entails _ (type _ _ ?eglob _ _) =>
        reshape_expr eglob ltac:(fun K e' => unify e' e; tac K)
  end.
Tactic Notation "type_bind" open_constr(e) :=
  type_reshape e ltac:(fun K => iApply (type_bind K e)).
Tactic Notation "type_bind" open_constr(e) "with" open_constr(H) :=
  type_reshape e ltac:(fun K => iApply (type_bind K e with H)).
