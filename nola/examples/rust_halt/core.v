(** * Core features *)

From nola.examples.rust_halt Require Export type.

Implicit Type (X Y : xty) (v : val).

Section type.
  Context `{!rust_haltGS CON Σ, !rust_haltC CON, !rust_haltJ CON JUDG Σ,
    !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ), !rust_haltCS CON JUDG Σ}.

  (** ** Basic typing rules *)

  (** Value that is discarded *)
  Lemma type_value `(!AsVal e) {Xl κ Γ} : ⊢ type (Xl:=Xl) κ Γ e (λ _, Γ) id.
  Proof.
    rewrite type_unseal. case: as_val=>/= ? <-. iIntros (????) "!> $$ pre Γ".
    wp_value_head. by iFrame.
  Qed.

  (** Pure execution *)
  Lemma type_pure {Xl Yl κ Γi e e' Γo pre n φ} :
    PureExec φ n e e' → φ →
    type (Xl:=Xl) (Yl:=Yl) κ Γi e' Γo pre ⊢ type κ Γi e Γo pre.
  Proof.
    rewrite type_unseal=> ??. iIntros "#type !>" (????) "κ t pre Γi".
    wp_pure _. iApply ("type" with "κ t pre Γi").
  Qed.

  (** Binding *)
  Lemma type_bind {Xl Yl Zl κ Γi Γm Γo pre pre'} K e :
    type (Yl:=Yl) κ Γi e Γm pre -∗
    (∀ v, type κ (Γm v) (fill K (of_val v)) Γo pre') -∗
      type (Xl:=Xl) (Yl:=Zl) κ Γi (fill K e) Γo (pre ∘ pre').
  Proof.
    rewrite type_unseal. iIntros "#type #type' !>" (????) "κ t pre Γi".
    iApply twp_bind. iDestruct ("type" with "κ t pre Γi") as "big".
    iApply (twp_wand with "big"). iIntros (?) ">(% & κ & t & pre & Γm)".
    iApply ("type'" with "κ t pre Γm").
  Qed.

  (** Let expression *)
  Lemma type_let `(!Closed (x :b: []) e') {Xl Yl Zl κ Γi Γm Γo e pre pre'} :
    type (Yl:=Yl) κ Γi e Γm pre -∗
    (∀ v, type κ (Γm v) (subst' x v e') Γo pre') -∗
      type (Xl:=Xl) (Yl:=Zl) κ Γi (let: x := e in e') Γo (pre ∘ pre').
  Proof.
    iIntros "type type'". iApply (type_bind [LetCtx x e'] with "type")=>/=.
    iIntros (?). by iApply (type_pure with "type'").
  Qed.

  (** Sequential execution *)
  Lemma type_seq `(!Closed [] e') {Xl Yl Zl κ Γi Γm Γo e pre pre'} :
    type (Yl:=Yl) κ Γi e Γm pre -∗ (∀ v, type κ (Γm v) e' Γo pre') -∗
      type (Xl:=Xl) (Yl:=Zl) κ Γi (e;; e') Γo (pre ∘ pre').
  Proof. iIntros "#? #?". by iApply type_let. Qed.

  (** Evaluate a path to a value *)
  Lemma type_path p
    `(!EtcxExtract (X:=X) (Yl:=Yl) (Zl:=Zl) (p ◁ T) Γ Γr get getr) {κ} :
    ⊢ type κ Γ p (λ v, v ◁ T ᵖ:: Γr) (λ post zl, post (get zl, getr zl)').
  Proof.
    rewrite type_unseal. iIntros (????) "!> $$ pre". rewrite etcx_extract /=.
    iIntros "[(% & % & % & T) Γr]". wp_path p. wp_value_head. iModIntro.
    iExists _. iFrame "pre". iFrame. by rewrite of_path_val.
  Qed.
  Lemma type_path_frozen p
    `(!EtcxExtract (X:=X) (Yl:=Yl) (Zl:=Zl) (p ◁[†α] T) Γ Γr get getr) {κ} :
    ⊢ type κ Γ p (λ v, v ◁[†α] T ᵖ:: Γr) (λ post zl, post (get zl, getr zl)').
  Proof.
    rewrite type_unseal. iIntros (????) "!> $$ pre". rewrite etcx_extract /=.
    iIntros "[(% & % & →T) Γr]". wp_path p. wp_value_head. iModIntro.
    iExists _. iFrame "pre". iFrame. by rewrite of_path_val.
  Qed.
  Lemma type_path_bind K p
    `(!EtcxExtract (X:=X) (Yl:=Yl) (Zl:=Yl') (p ◁ T) Γi Γr get getr)
    {Zl Γo pre κ} :
    (∀ v, type κ (v ◁ T ᵖ:: Γr) (fill K (of_val v)) Γo pre) ⊢
      type (Yl:=Zl) κ Γi (fill K p) Γo
        (λ post zl, pre post (get zl, getr zl)').
  Proof.
    iIntros "type". iApply (type_bind (pre:=λ post _, post _) with "[] type").
    iApply type_path.
  Qed.
  Lemma type_path_frozen_bind K p
    `(!EtcxExtract (X:=X) (Yl:=Yl) (Zl:=Yl') (p ◁[†α] T) Γi Γr get getr)
    {Zl Γo pre κ} :
    (∀ v, type κ (v ◁[†α] T ᵖ:: Γr) (fill K (of_val v)) Γo pre) ⊢
      type (Yl:=Zl) κ Γi (fill K p) Γo
        (λ post zl, pre post (get zl, getr zl)').
  Proof.
    iIntros "type". iApply (type_bind (pre:=λ post _, post _) with "[] type").
    iApply type_path_frozen.
  Qed.

  (** Function call, where the arguments have been evaluated to values *)
  Lemma type_call
    `(!AsRec e f xl erec, !TCForall AsVal vl, !Closed (f :b: xl +b+ []) erec,
      !DoSubstL (f :: xl) (e :: vl) erec erec') {Xl Yl κ Γi Γo pre} :
    type (Xl:=Xl) (Yl:=Yl) κ Γi erec' Γo pre ⊢ type κ Γi (e vl) Γo pre.
  Proof. by iApply type_pure. Qed.

  (** Forking a new thread *)
  Lemma type_fork `(!SendTcx (Xl:=Xl) Γ) {κ e} :
    type (Xl:=Xl) ⊤ Γ e (λ _, ᵖ[]) (λ post _, post ᵖ[])%type ⊢
      type κ Γ (Fork e) (λ _, ᵖ[]) (λ post _, post ᵖ[])%type.
  Proof.
    rewrite type_unseal. iIntros "#type !>" (????) "$$ #obs Γ".
    iApply (twp_fork with "[Γ]"); last first.
    {  iIntros "_ !>/=". iExists (λ _, ()). by iSplit. }
    iMod na_alloc as (?) "t'". rewrite send_tcx.
    iDestruct ("type" $! 1%Qp with "[//] t' obs Γ") as "?".
    rewrite twp_mono //=. by iIntros.
  Qed.

  (** ** Basic structural rules *)

  (** Copy a path *)
  Lemma sub_copy p
    `(!EtcxExtract (X:=X) (Yl:=Yl) (Zl:=Zl) (p ◁ T) Γi Γr get getr, !Copy T)
    {κ} :
    ⊢ sub κ Γi (p ◁ T ᵖ:: p ◁ T ᵖ:: Γr)
        (λ post yl, post (get yl, get yl, getr yl)').
  Proof.
    rewrite sub_unseal. iIntros "!>" (????) "/= $ $ pre". rewrite etcx_extract.
    iIntros "[#T Γr] !>". iFrame "pre T Γr".
  Qed.
  Lemma type_copy p
    `(!EtcxExtract (X:=X) (Yl:=Yl) (Zl:=Yl') (p ◁ T) Γi Γr get getr, !Copy T)
    {κ Zl Γo e pre} :
    type (Yl:=Zl) κ (p ◁ T ᵖ:: p ◁ T ᵖ:: Γr) e Γo pre ⊢
      type κ Γi e Γo (λ post yl, pre post (get yl, get yl, getr yl)').
  Proof.
    iIntros "type". iApply (type_in (prei:=λ post _, post _) with "[] type").
    iApply sub_copy.
  Qed.

  (** Framing on [sub] *)
  Lemma sub_frame {Xl} Γ
    `(!TcxExtract (Xl:=Xl) (Yl:=Yl) (Zl:=Yl') Γ Γi Γr get getr)
    {κ Zl Γo pre} :
    sub (Yl:=Zl) κ Γr Γo pre ⊢
      sub κ Γi (Γ ᵖ++ Γo)
        (λ post yl, pre (λ zl, post (get yl ᵖ++ zl)) (getr yl)).
  Proof.
    rewrite sub_unseal. iIntros "#sub !>" (????) "/= κ t pre".
    rewrite tcx_extract. iIntros "[Γ Γr]".
    iMod ("sub" with "κ t pre Γr") as (?) "($ & $ & $ & Γo)". iModIntro.
    rewrite sem_tcx_app. iFrame.
  Qed.
  Lemma sub_frame_rest {Xl} Γ
    `(!TcxExtract (Xl:=Xl) (Yl:=Yl) (Zl:=Yl') Γ Γi Γr get getr)
    {κ Zl Γo pre} :
    sub (Yl:=Zl) κ Γ Γo pre ⊢
      sub κ Γi (Γr ᵖ++ Γo)
        (λ post yl, pre (λ zl, post (getr yl ᵖ++ zl)) (get yl)).
  Proof. apply: sub_frame. split=> ??. rewrite comm. exact: tcx_extract. Qed.

  (** Framing on [type] *)
  Lemma type_frame {Xl} Γ
    `(!TcxExtract (Xl:=Xl) (Yl:=Yl) (Zl:=Yl') Γ Γi Γr get getr)
    {κ Zl Γo e pre} :
    type (Yl:=Zl) κ Γr e Γo pre ⊢
      type κ Γi e (λ v, Γ ᵖ++ Γo v)
        (λ post yl, pre (λ zl, post (get yl ᵖ++ zl)) (getr yl)).
  Proof.
    rewrite type_unseal. iIntros "#type !>" (????) "/= κ t pre".
    rewrite tcx_extract. iIntros "[Γ Γr]".
    iDestruct ("type" with "κ t pre Γr") as "twp". iApply (twp_wand with "twp").
    iIntros (?) ">(% & $ & $ & $ & Γo)". iModIntro. rewrite sem_tcx_app. iFrame.
  Qed.
  Lemma type_frame_rest {Xl} Γ
    `(!TcxExtract (Xl:=Xl) (Yl:=Yl) (Zl:=Yl') Γ Γi Γr get getr)
    {κ Zl Γo e pre} :
    type (Yl:=Zl) κ Γ e Γo pre ⊢
      type κ Γi e (λ v, Γr ᵖ++ Γo v)
        (λ post yl, pre (λ zl, post (getr yl ᵖ++ zl)) (get yl)).
  Proof. apply: type_frame. split=> ??. rewrite comm. exact: tcx_extract. Qed.

  (** Swapping over [ᵖ++] *)
  Lemma sub_app_swap {Xl Yl} Γ Γ' {κ} :
    ⊢ sub (Xl:=Xl++Yl) κ (Γ ᵖ++ Γ') (Γ' ᵖ++ Γ)
      (λ post xyl, let '(xl, yl)' := plist_sep xyl in post (yl ᵖ++ xl)).
  Proof.
    rewrite sub_unseal. iIntros (????) "!> $$ pre". rewrite sem_tcx_app_sep.
    iIntros "[Γ Γ'] !>". iFrame "pre". rewrite sem_tcx_app. iFrame.
  Qed.
  Lemma type_in_app_swap {Xl Yl} Γi Γi' {Zl Γo κ e pre} :
    type (Xl:=Xl++Yl) (Yl:=Zl) κ (Γi' ᵖ++ Γi) e Γo pre ⊢
      type κ (Γi ᵖ++ Γi') e Γo
        (λ post xyl, let '(xl, yl)' := plist_sep xyl in pre post (yl ᵖ++ xl)).
  Proof.
    iIntros "type". iApply (type_in (prei:=λ post _, post _) with "[] type").
    iApply sub_app_swap.
  Qed.
  Lemma type_out_app_swap {Xl Γi Yl Zl} Γo Γo' {κ e pre} :
    type (Xl:=Xl) (Yl:=Yl++Zl) κ Γi e (λ v, Γo' v ᵖ++ Γo v) pre ⊢
      type κ Γi e (λ v, Γo v ᵖ++ Γo' v) (λ post,
        pre (λ yzl, let '(yl, zl)' := plist_sep yzl in post (zl ᵖ++ yl))).
  Proof.
    iIntros "type". iApply (type_out with "type"). iIntros (?).
    iApply sub_app_swap.
  Qed.

  (** ** Basic ghost operations *)

  (** Leak on [sub] *)
  Lemma sub_leak {Xl} Γ
    `(!TcxExtract (Xl:=Xl) (Yl:=Yl) (Zl:=Zl) Γ Γg Γr get getr,
      !ResolTcx Γ κ postr) :
    ⊢ sub κ Γg Γr (λ post yl, postr (get yl) → post (getr yl))%type.
  Proof.
    rewrite sub_unseal. iIntros (????) "!>/= κ t pre". rewrite tcx_extract.
    iIntros "[Γ $]". iMod (resol_tcx with "κ t Γ") as "($ & $ & post)".
    iModIntro. iApply (proph_obs_impl2 with "post pre")=> ?? to. exact: to.
  Qed.
  Lemma sub_leak_rest {Xl} Γ
    `(!TcxExtract (Xl:=Xl) (Yl:=Yl) (Zl:=Zl) Γ Γg Γr get getr,
      !ResolTcx Γr κ postr) :
    ⊢ sub κ Γg Γ (λ post yl, postr (getr yl) → post (get yl))%type.
  Proof. apply: sub_leak=>//. split=> >. rewrite comm. exact: tcx_extract. Qed.

  (** Leak on [type] *)
  Lemma type_leak {Xl} Γ
    `(!TcxExtract (Xl:=Xl) (Yl:=Yl) (Zl:=Yl') Γ Γi Γr get getr,
      !ResolTcx Γ κ postr) {e Zl Γo pre} :
    type (Yl:=Zl) κ Γr e Γo pre ⊢
      type κ Γi e Γo (λ post yl, postr (get yl) → pre post (getr yl))%type.
  Proof.
    iIntros "type".
    iApply (type_in (prei:=λ post _, _ → post _) with "[] type").
    iApply sub_leak.
  Qed.
  Lemma type_leak_rest {Xl} Γ
    `(!TcxExtract (Xl:=Xl) (Yl:=Yl) (Zl:=Yl') Γ Γi Γr get getr,
      !ResolTcx Γr κ postr) {e Zl Γo pre} :
    type (Yl:=Zl) κ Γ e Γo pre ⊢
      type κ Γi e Γo (λ post yl, postr (getr yl) → pre post (get yl))%type.
  Proof.
    iIntros "type".
    iApply (type_in (prei:=λ post _, _ → post _) with "[] type").
    iApply sub_leak_rest.
  Qed.

  (** Modify by subtyping *)
  Lemma sub_subty p {X} T {Y} U f
    `(!EtcxExtract (X:=X) (Yl:=Zl) (Zl:=Zl') (p ◁ T) Γ Γr get getr) {κ} :
    subtyd' X Y T U f ⊢
      sub κ Γ (p ◁ U ᵖ:: Γr) (λ post zl, post (f (get zl), getr zl)').
  Proof.
    rewrite subty_unseal sub_unseal. iIntros "[_[#TU _]] !>/=" (????) "$$ pre".
    rewrite etcx_extract /=. iIntros "[(% & % & $ & T) Γr] !>". iFrame "pre Γr".
    by iDestruct ("TU" with "T") as "$".
  Qed.
  Lemma type_subty p {X} T {Y} U f
    `(!EtcxExtract (X:=X) (Yl:=Zl) (Zl:=Zl') (p ◁ T) Γi Γr get getr)
    {κ Zl'' Γo e pre} :
    subtyd' X Y T U f -∗ type (Yl:=Zl'') κ (p ◁ U ᵖ:: Γr) e Γo pre -∗
      type κ Γi e Γo (λ post zl, pre post (f (get zl), getr zl)').
  Proof.
    iIntros "#sub type".
    iApply (type_in (prei:=λ post _, post _) with "[] type").
    by iApply sub_subty.
  Qed.
  Lemma sub_subty_frozen p {X} T {Y} U f
    `(!EtcxExtract (X:=X) (Yl:=Zl) (Zl:=Zl') (p ◁[†α] T) Γ Γr get getr,
      !@Inj X Y (=) (=) f) {κ} :
    subtyd T U f ⊢
      sub κ Γ (p ◁[†α] U ᵖ:: Γr) (λ post zl, post (f (get zl), getr zl)').
  Proof.
    rewrite subty_unseal sub_unseal. iIntros "[_[#TU _]] !>/=" (????) "$$ pre".
    rewrite etcx_extract /=. iIntros "[(% & $ & →T) Γr] !>". iFrame "pre Γr".
    iIntros "†". iMod ("→T" with "†") as (??) "[eqz T]". iExists _, _.
    iDestruct ("TU" with "T") as "$". iApply (proph_eqz_f with "eqz").
  Qed.
  Lemma type_subty_frozen p {X} T {Y} U f
    `(!EtcxExtract (X:=X) (Yl:=Zl) (Zl:=Zl') (p ◁[†α] T) Γi Γr get getr,
      !@Inj X Y (=) (=) f) {κ Zl'' Γo e pre} :
    subtyd T U f -∗ type (Yl:=Zl'') κ (p ◁[†α] U ᵖ:: Γr) e Γo pre -∗
      type κ Γi e Γo (λ post zl, pre post (f (get zl), getr zl)').
  Proof.
    iIntros "#sub type".
    iApply (type_in (prei:=λ post _, post _) with "[] type").
    by iApply sub_subty_frozen.
  Qed.

  (** Take out the real part of an object *)
  Lemma type_real p A {X Yl' Zl} (pre : _ → xpred _)
    `(!EtcxExtract (X:=X) (Yl:=Yl) (Zl:=Yl') (p ◁ T) Γi Γr get' getr)
    `(!Real' X A T κ get) {e Γo} :
    (∀ a, type (Yl:=Zl) κ (p ◁ T ᵖ:: Γr) e Γo
      (λ post '(x, yl')', get x = a ∧ pre post (x ᵖ:: yl'))%type) ⊢
      type κ Γi e Γo (λ post yl, pre post (get' yl, getr yl)').
  Proof.
    rewrite type_unseal. iIntros "#type !>" (????) "κ t pre".
    rewrite etcx_extract /=. iIntros "[(% & % & % & T) Γr]".
    iMod (real_own with "κ t T") as ([a eq]) "(κ & t & T)".
    iApply ("type" $! a _ _ _ (λ _, (_,_)') with "κ t [pre] [$Γr $T //]").
    iApply (proph_obs_impl with "pre")=> π ?. by rewrite -(eq π).
  Qed.

  (** ** Ghost operations on lifetimes *)

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
    type (Yl:=Yl) (κ ⊓ α) Γr e Γo pre ⊢
      type κ Γi e (λ p, ^[α] ᵖ:: Γo p)
        (λ post xl, pre (λ yl, post ((), yl)') (getr xl)).
  Proof.
    rewrite type_unseal. iIntros "#type !>/=" (????) "κ t pre Γi".
    rewrite etcx_extract /=. iDestruct "Γi" as "[[% α] Γr]".
    iDestruct (lft_live_fuse with "κ α") as (?) "[κα →κα]".
    iDestruct ("type" with "κα t pre Γr") as "twp".
    iApply (twp_wand with "twp"). iIntros (?) ">(% & κα & $ & $ & $) !>".
    by iDestruct ("→κα" with "κα") as "[$$]".
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
    iMod (lft_end with "α") as "†"=>//. iApply ("type" with "† κ t pre Γr").
  Qed.

  (** Retrieve from a frozen object *)
  Lemma sub_retrieve p
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
  Lemma type_retrieve p
    `(!EtcxExtract (X:=X) (Yl:=Yl) (Zl:=Zl) (p ◁[†α] T) Γi Γr get getr,
      !TyOp T κ) {e Zl' Γo pre} :
    [†α] -∗ type (Yl:=Zl') κ (p ◁ T ᵖ:: Γr) e Γo pre -∗
      type κ Γi e Γo (λ post yl, pre post (get yl, getr yl)').
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
  type_reshape e ltac:(fun K => iApply (type_bind K e)=>/=).
Tactic Notation "type_bind" open_constr(e) "with" open_constr(H) :=
  type_reshape e ltac:(fun K => iApply (type_bind K e with H)=>/=).
Tactic Notation "type_path"
  open_constr(p) "as" "(" simple_intropattern(v) ")" :=
  type_reshape p ltac:(fun K =>
    iApply (type_path_bind K p)=>/=; try solve_extract; iIntros (v)).
Tactic Notation "type_path_frozen"
  open_constr(p) "as" "(" simple_intropattern(v) ")" :=
  type_reshape p ltac:(fun K =>
    iApply (type_path_frozen_bind K p)=>/=; try solve_extract; iIntros (v)).
