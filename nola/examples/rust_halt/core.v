(** * Core features *)

From nola.examples.rust_halt Require Export type.

Implicit Type X Y : xty.

Section type.
  Context `{!rust_haltGS CON Σ, !rust_haltC CON, !rust_haltJ CON JUDG Σ,
    !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ), !rust_haltCS CON JUDG Σ}.

  (** ** Operations on type contexts *)

  (** Leak *)
  Lemma sub_leak {Xl} Γ
    `(!TcxExtract (Xl:=Xl) (Yl:=Yl) (Zl:=Zl) Γ Γg Γr get getr,
      !ResolTcx Γ κ postr) :
    ⊢ sub κ Γg Γr (λ post yl, postr (get yl) → post (getr yl))%type.
  Proof.
    rewrite sub_unseal. iIntros (????) "!>/= κ t pre". rewrite tcx_extract.
    iIntros "[Γ $]". iMod (resol_tcx with "κ t Γ") as "($ & $ & post)".
    iModIntro. iApply (proph_obs_impl2 with "post pre")=> ?? to. by apply to.
  Qed.
  Lemma sub_leak_rest {Xl} Γ
    `(!TcxExtract (Xl:=Xl) (Yl:=Yl) (Zl:=Zl) Γ Γg Γr get getr,
      !ResolTcx Γr κ postr) :
    ⊢ sub κ Γg Γ (λ post yl, postr (getr yl) → post (get yl))%type.
  Proof.
    rewrite sub_unseal. iIntros (????) "!>/= κ t pre". rewrite tcx_extract.
    iIntros "[$ Γr]". iMod (resol_tcx with "κ t Γr") as "($ & $ & post)".
    iModIntro. iApply (proph_obs_impl2 with "post pre")=> ?? to. by apply to.
  Qed.

  (** Modify by subtyping *)
  Lemma sub_subty p {X} T
    `(!EtcxExtract (X:=X) (Yl:=Zl) (Zl:=Zl') (p ◁ T) Γ Γr get getr)
    {Y} U f {κ} :
    subtyd' X Y T U f ⊢
      sub κ Γ (p ◁ U ᵖ:: Γr) (λ post zl, post (f (get zl), getr zl)').
  Proof.
    rewrite subty_unseal sub_unseal. iIntros "[_[#TU _]] !>/=" (????) "$ $ pre".
    rewrite etcx_extract /=. iIntros "[(% & % & $ & T) Γr] !>". iFrame "pre Γr".
    by iDestruct ("TU" with "T") as "$".
  Qed.
  Lemma sub_subty_frozen p {X} T
    `(!EtcxExtract (X:=X) (Yl:=Zl) (Zl:=Zl') (p ◁[†α] T) Γ Γr get getr)
    {Y} U f `(!@Inj X Y (=) (=) f) {κ} :
    subtyd T U f ⊢
      sub κ Γ (p ◁[†α] U ᵖ:: Γr) (λ post zl, post (f (get zl), getr zl)').
  Proof.
    rewrite subty_unseal sub_unseal. iIntros "[_[#TU _]] !>/=" (????) "$ $ pre".
    rewrite etcx_extract /=. iIntros "[(% & $ & →T) Γr] !>". iFrame "pre Γr".
    iIntros "†". iMod ("→T" with "†") as (??) "[eqz T]". iExists _, _.
    iDestruct ("TU" with "T") as "$". iApply (proph_eqz_f with "eqz").
  Qed.

  (** ** Basic typing rules *)

  (** Pure execution *)
  Lemma type_pure {Xl Yl κ Γi e e' Γo pre n φ} :
    PureExec φ n e e' → φ →
    type (Xl:=Xl) (Yl:=Yl) κ Γi e' Γo pre ⊢ type κ Γi e Γo pre.
  Proof.
    rewrite type_unseal=> ??. iIntros "#type !>" (????) "κ t pre Γ".
    wp_pure _. iApply ("type" with "κ t pre Γ").
  Qed.

  (** Binding *)
  Lemma type_bind {Xl Yl Zl κ Γ Γ' Γ'' pre pre'} K e :
    type (Yl:=Yl) κ Γ e Γ' pre -∗
    (∀ p, type κ (Γ' p) (fill K (of_val p)) Γ'' pre') -∗
      type (Xl:=Xl) (Yl:=Zl) κ Γ (fill K e) Γ'' (pre ∘ pre').
  Proof.
    rewrite type_unseal. iIntros "#type #type' !>" (????) "κ t pre Γ".
    iApply twp_bind. iDestruct ("type" with "κ t pre Γ") as "big".
    iApply (twp_wand with "big"). iIntros (?) ">(% & κ & t & pre & Γ')".
    iApply ("type'" with "κ t pre Γ'").
  Qed.

  (** Let expression *)
  Lemma type_let {Xl Yl Zl κ Γ Γ' Γ'' x e e' pre pre'}
    `{!Closed (x :b: []) e'} :
    type (Yl:=Yl) κ Γ e Γ' pre -∗
    (∀ p, type κ (Γ' p) (subst' x p e') Γ'' pre') -∗
      type (Xl:=Xl) (Yl:=Zl) κ Γ (let: x := e in e') Γ'' (pre ∘ pre').
  Proof.
    iIntros "#type #type'". iApply (type_bind [LetCtx x e'] with "type")=>/=.
    iIntros (?). by iApply (type_pure with "type'").
  Qed.

  (** ** Operations on lifetimes *)

  (** Allocate a new local lifetime *)
  Lemma type_lft_new {Xl Yl κ Γi e Γo pre} :
    (∀ α, type κ (^[α] ᵖ:: Γi) e Γo pre) ⊢
      type (Xl:=Xl) (Yl:=Yl) κ Γi e Γo (λ post xl, pre post ((), xl)').
  Proof.
    rewrite type_unseal.
    iIntros "#type !>" (????) "κ t pre Γi". iMod lft_alloc as (α ?) "α".
    iApply ("type" with "κ t pre"). by iFrame.
  Qed.

  (** Use a local lifetime *)
  Lemma type_lft_use α
    `(!EtcxExtract (Yl:=Xl) (Zl:=Xl') ^[α] Γi Γr get getr) {Yl κ e Γo pre} :
    type (Yl:=Yl) (α ⊓ κ) Γr e Γo pre ⊢
      type κ Γi e (λ p, ^[α] ᵖ:: Γo p)
        (λ post xl, pre (λ yl, post ((), yl)') (getr xl)).
  Proof.
    rewrite type_unseal. iIntros "#type !>/=" (q ???) "κ t pre Γi".
    rewrite etcx_extract /=. iDestruct "Γi" as "[[% α] Γr]".
    case: (Qp.lower_bound 1 q)=> [?[?[?[->->]]]]. iDestruct "α" as "[α $]".
    iDestruct "κ" as "[κ $]".
    iDestruct ("type" with "[$α $κ //] t pre Γr") as "twp".
    iApply (twp_wand with "twp"). by iIntros (?) ">(% & [$$] & $ & $ & $) !>".
  Qed.

  (** Eternalize a lifetime *)
  Lemma type_lft_eternal α
    `(!EtcxExtract (Yl:=Xl) (Zl:=Yl) ^[α] Γi Γr get getr) {Zl κ e Γo pre} :
    □ ((∀ β, β ⊑□ α) -∗ type (Yl:=Zl) κ Γr e Γo pre) ⊢
      type κ Γi e Γo (λ post xl, pre post (getr xl)).
  Proof.
    rewrite type_unseal. iIntros "#type !>/=" (????) "κ t pre".
    rewrite etcx_extract /=. iIntros "[[% α] Γr]".
    iMod (lft_eternalize_sincl with "α") as "∞"=>//.
    iApply ("type" with "∞ κ t pre Γr").
  Qed.

  (** End a lifetime *)
  Lemma type_lft_end α
    `(!EtcxExtract (Yl:=Xl) (Zl:=Yl) ^[α] Γi Γr get getr) {Zl κ e Γo pre} :
    □ ([†α] -∗ type (Yl:=Zl) κ Γr e Γo pre) ⊢
      type κ Γi e Γo (λ post xl, pre post (getr xl)).
  Proof.
    rewrite type_unseal. iIntros "#type !>/=" (????) "κ t pre".
    rewrite etcx_extract /=. iIntros "[[% α] Γr]".
    iMod (lft_kill with "α") as "†"=>//. iApply ("type" with "† κ t pre Γr").
  Qed.

  (** Retrieve from a frozen object *)
  Lemma sub_retrieve p α
    `(!EtcxExtract (X:=X) (Yl:=Yl) (Zl:=Zl) (p ◁[†α] T) Γ Γr get getr,
      !TyOp T κ) :
    [†α] -∗ sub κ Γ (p ◁ T ᵖ:: Γr) (λ post yl, post (get yl, getr yl)').
  Proof.
    rewrite sub_unseal. iIntros "#† !>/=" (????) "κ $ #pre".
    rewrite etcx_extract /=. iIntros "[(% & peq & →T) Γr]".
    iMod ("→T" with "†") as (? xπ') "[eqz T]".
    iMod (ty_own_proph with "κ T") as (???) "[ξl →T]".
    iMod ("eqz" with "[//] ξl") as "[ξl #eq]". iMod ("→T" with "ξl") as "[$ T]".
    iModIntro. iExists (λ π, (xπ' π, _)'). iFrame "Γr T peq".
    by iApply (proph_obs_impl2 with "pre eq")=> ??<-.
  Qed.
  Lemma type_retrieve p α
    `(!EtcxExtract (X:=X) (Yl:=Yl) (Zl:=Zl) (p ◁[†α] T) Γ Γr get getr,
      !TyOp T κ) {e Zl' Γo pre} :
    [†α] -∗ type (Yl:=Zl') κ (p ◁ T ᵖ:: Γr) e Γo pre -∗
      type κ Γ e Γo (λ post yl, pre post (get yl, getr yl)').
  Proof.
    iIntros "#† type". iApply (type_in (prei:=λ post _, post _) with "[] type").
    by iApply sub_retrieve.
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
