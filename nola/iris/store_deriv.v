(** * Stored propositions relaxed with derivability *)

From nola.util Require Import tagged.
From nola.bi Require Export deriv.
From nola.iris Require Export store.
From iris.proofmode Require Import proofmode.
Import iPropAppNotation ModwNotation DsemNotation CsemNotation.

Implicit Type (Σ : gFunctors) (FM : ofe).

(** ** Judgment *)

(* [storeJT]: Judgment type for [store] *)
Variant storeJT_id FM := .
Definition storeJT FM : ofe :=
  (** Accessor judgment *) tagged (storeJT_id FM) FM.
(** [storeJ]: [storeJT] registered *)
Notation storeJ FM JUDG := (inJ (storeJT FM) JUDG).

Section storeJ.
  Context `{store_j : !storeJ FM JUDG} {Σ}.
  Implicit Type (δ : JUDG -n> iProp Σ) (Px : FM).

  (** Accessor judgment *)
  Local Definition store_jacsr Px : JUDG := store_j (Tagged Px).
  Local Instance store_jacsr_ne : NonExpansive store_jacsr.
  Proof. solve_proper. Qed.

  (** [store]: Relaxed stored proposition *)
  Local Definition store_def δ (Px : FM) : iProp Σ := δ (store_jacsr Px).
  Local Lemma store_aux : seal store_def. Proof. by eexists. Qed.
  Definition store := store_aux.(unseal).
  Local Lemma store_unseal : store = store_def. Proof. exact: seal_eq. Qed.

  (** [store] is non-expansive *)
  #[export] Instance store_ne {δ} : NonExpansive (store δ).
  Proof. rewrite store_unseal. solve_proper. Qed.
  #[export] Instance store_proper {δ} : Proper ((≡) ==> (⊣⊢)) (store δ).
  Proof. apply ne_proper, _. Qed.
End storeJ.

(** Notation *)
Notation stored := (store der).

Section storeJ.
  Context `{!dinvGS FML Σ, !storeJ (FML $oi Σ) JUDG,
    !Dsem JUDG (FML $oi Σ) (iProp Σ)}.
  Implicit Type δ : JUDG -n> iProp Σ.

  (** [storeJT_sem]: Semantics of [storeJT] *)
  Definition storeJT_sem δ (J : storeJT (FML $oi Σ)) : iProp Σ :=
    |->[dinv_wsat ⟦⟧(δ)]◇ (⟦ J.(untag) ⟧(δ)).
  (** [storeJT_sem] is non-expansive *)
  #[export] Instance storeJT_sem_ne {δ} : NonExpansive (storeJT_sem δ).
  Proof. solve_proper. Qed.
  (** [Dsem] over [storeJT] *)
  #[export] Instance storeJT_dsem : Dsem JUDG (storeJT (FML $oi Σ)) (iProp Σ) :=
    DSEM storeJT_sem _.
End storeJ.
Arguments storeJT_sem {_ _ _ _} _ _ /.
(** [storeJS]: Semantics of [storeJT] registered *)
Notation storeJS FML JUDG Σ := (inJS (storeJT (FML $oi Σ)) JUDG (iProp Σ)).

Section store_deriv.
  Context `{!dinvGS (cifOF CON) Σ, !storeJ (cifO CON Σ) JUDG,
    !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ), !storeJS (cifOF CON) JUDG Σ}.
  Implicit Type Px Qx Rx : cif CON Σ.

  (** Access using [stored] *)
  Lemma stored_acc {Px} : stored Px -∗[dinv_wsat ⟦⟧ᶜ]◇ ⟦ Px ⟧ᶜ.
  Proof.
    rewrite store_unseal. iIntros "accPx".
    iDestruct (der_sound with "accPx") as "accPx". by rewrite in_js.
  Qed.

  Context `{!Deriv (JUDG:=JUDG) ih δ, !tokenG Σ}.

  (** Turn an accessor into [store] *)
  Lemma store_acsr_store {Px} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      |->[dinv_wsat ⟦⟧ᶜ(δ')]◇ ⟦ Px ⟧ᶜ(δ')) ⊢
      store δ Px.
  Proof.
    rewrite store_unseal. iIntros "big". iApply Deriv_factor. iIntros (????).
    rewrite in_js /=. by iApply "big".
  Qed.

  (** Turn [store_tok] into [store] *)
  Lemma store_tok_store {Px} : store_tok Px ⊢ store δ Px.
  Proof.
    rewrite -store_acsr_store. iIntros "?" (????). by iApply store_tok_acc.
  Qed.
  (** Turn [dinv_tok] over a persistent proposition into [□ store] *)
  Lemma dinv_tok_persistent_store {Px} :
    (∀ δ', Deriv ih δ' → Persistent ⟦ Px ⟧ᶜ(δ')) →
    dinv_tok Px ⊢ □ store δ Px.
  Proof.
    rewrite -store_acsr_store=> ?. iIntros "#i !>" (????).
    by iMod (dinv_tok_acc_persistent with "i") as "$".
  Qed.

  (** Allocate [store] *)
  Lemma store_alloc Px : ⟦ Px ⟧ᶜ(δ) =[dinv_wsat ⟦⟧ᶜ(δ)]=∗ store δ Px.
  Proof. rewrite -store_tok_store. exact: store_tok_alloc. Qed.
  (** Allocate [□ store] *)
  Lemma store_alloc_pers Px :
    (∀ δ', Deriv ih δ' → Persistent ⟦ Px ⟧ᶜ(δ')) →
    ⟦ Px ⟧ᶜ(δ) =[dinv_wsat ⟦⟧ᶜ(δ)]=∗ □ store δ Px.
  Proof.
    move=> ?. rewrite -dinv_tok_persistent_store. exact: dinv_tok_alloc.
  Qed.

  (** Convert [store] with [-∗] *)
  Lemma store_wand {Px Qx} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Px ⟧ᶜ(δ') -∗[dinv_wsat ⟦⟧ᶜ(δ')]◇ ⟦ Qx ⟧ᶜ(δ')) -∗
      store δ Px -∗ store δ Qx.
  Proof.
    rewrite store_unseal. iIntros "PQ accPx". iApply Deriv_factor.
    iIntros (??? to). rewrite /store_def to !in_js /=. iMod "accPx" as "Px".
    by iApply "PQ".
  Qed.

  (** Merge [store]s *)
  Lemma store_merge {Px Qx Rx} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Px ⟧ᶜ(δ') -∗ ⟦ Qx ⟧ᶜ(δ') -∗[dinv_wsat ⟦⟧ᶜ(δ')]◇ ⟦ Rx ⟧ᶜ(δ')) -∗
      store δ Px -∗ store δ Qx -∗ store δ Rx.
  Proof.
    rewrite store_unseal. iIntros "PQR accPx accQx". iApply Deriv_factor.
    iIntros (??? to). rewrite /store_def !to !in_js /=.
    iMod "accPx" as "Px". iMod "accQx" as "Qx".
    iApply ("PQR" with "[//] [//] [//] Px Qx").
  Qed.
End store_deriv.

(** ** Constructor *)

(** [storeCT]: Constructor for [store] *)
Variant storeCT_id := .
Definition storeCT :=
  Cifcon storeCT_id unit (λ _, Empty_set) (λ _, unit) (λ _, unitO) _.
(** [storeC]: [storeCT] registered *)
Notation storeC := (inC storeCT).

Section storeC.
  Context `{!storeC CON} {Σ}.
  Implicit Type Px : cif CON Σ.
  (** [cif_store]: Formula for [store] *)
  Definition cif_store Px : cif CON Σ :=
    cif_in storeCT () nullary (unary Px) ().
  (** [cif_store] is non-expansive *)
  #[export] Instance cif_store_ne : NonExpansive cif_store.
  Proof. solve_proper. Qed.
  #[export] Instance cif_store_proper : Proper ((≡) ==> (≡)) cif_store.
  Proof. apply ne_proper, _. Qed.
  (** [cif_store] is productive *)
  #[export] Instance cif_store_productive : Productive cif_store.
  Proof.
    move=> ????. apply cif_in_preserv_productive=>//. by apply fun_proeq_later.
  Qed.

  Context `{!storeGS (cifOF CON) Σ, !storeJ (cifO CON Σ) JUDG}.
  #[export] Program Instance storeCT_ecsem : Ecsem storeCT CON JUDG Σ :=
    ECSEM (λ _ δ _ _ Φx _, store δ (Φx ())) _.
  Next Obligation. solve_proper. Qed.
End storeC.
(** [storeC] semantics registered *)
Notation storeCS := (inCS storeCT).

(** Reify [store] *)
Section storeC.
  Context `{!Csem CON JUDG Σ, !Jsem JUDG (iProp Σ), !dinvGS (cifOF CON) Σ,
    !storeC CON, !storeJ (cifO CON Σ) JUDG, !storeCS CON JUDG Σ,
    !storeJS (cifOF CON) JUDG Σ}.

  #[export] Program Instance store_as_cif {Px} :
    AsCif CON (λ δ, store δ Px) := AS_CIF (cif_store Px) _.
  Next Obligation. move=>/= >. by rewrite sem_cif_in. Qed.
End storeC.
