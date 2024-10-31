(** * Stored propositions *)

From nola.util Require Import tagged.
From nola.bi Require Export deriv.
From nola.iris Require Export store.
From iris.proofmode Require Import proofmode.
Import iPropAppNotation ModwNotation DsemNotation.

Implicit Type (Σ : gFunctors) (FM : ofe) (b : bool).

(** ** Judgment *)

(* [storeJT]: Judgment type for [store] *)
Variant storeJT_id FM := .
Definition storeJT (FM : ofe) : ofe :=
  (** Accessor judgment *) tagged (storeJT_id FM) (bool * FM).
(** [storeJ]: [storeJT] registered *)
Notation storeJ FM JUDG := (inJ (storeJT FM) JUDG).

Section storeJ.
  Context `{store_j : !storeJ FM JUDG} {Σ}.
  Implicit Type (δ : JUDG -n> iProp Σ) (Px : FM).

  (** Accessor judgment *)
  Local Definition store_jacsr b Px : JUDG := store_j (Tagged (b, Px)).
  Local Instance store_jacsr_ne {N} : NonExpansive (store_jacsr N).
  Proof. unfold store_jacsr=> ????. f_equiv. by split. Qed.

  (** [store]: Relaxed exclsuive stored proposition *)
  Local Definition store_def δ (Px : FM) : iProp Σ := δ (store_jacsr true Px).
  Local Lemma store_aux : seal store_def. Proof. by eexists. Qed.
  Definition store := store_aux.(unseal).
  Local Lemma store_unseal : store = store_def. Proof. exact: seal_eq. Qed.

  (** [pstore]: Relaxed persistent stored proposition *)
  Local Definition pstore_def δ (Px : FM) : iProp Σ :=
    □ δ (store_jacsr false Px).
  Local Lemma pstore_aux : seal pstore_def. Proof. by eexists. Qed.
  Definition pstore := pstore_aux.(unseal).
  Local Lemma pstore_unseal : pstore = pstore_def. Proof. exact: seal_eq. Qed.

  (** [pstore] is persistent *)
  #[export] Instance pstore_persistent {δ Px} : Persistent (pstore δ Px).
  Proof. rewrite pstore_unseal. exact _. Qed.

  (** [store] and [pstore] are non-expansive *)
  #[export] Instance store_ne {δ} : NonExpansive (store δ).
  Proof. rewrite store_unseal. solve_proper. Qed.
  #[export] Instance store_proper {δ} : Proper ((≡) ==> (⊣⊢)) (store δ).
  Proof. apply ne_proper, _. Qed.
  #[export] Instance pstore_ne {δ} : NonExpansive (pstore δ).
  Proof. rewrite pstore_unseal. solve_proper. Qed.
  #[export] Instance pstore_proper {δ} : Proper ((≡) ==> (⊣⊢)) (pstore δ).
  Proof. apply ne_proper, _. Qed.
End storeJ.

(** Notation *)
Notation stored := (store der).
Notation pstored := (pstore der).

Section storeJ.
  Context `{!storeGS FML Σ}.
  Implicit Type (P : iProp Σ) (Px : FML $oi Σ).

  Context `{!storeJ (FML $oi Σ) JUDG, !Dsem JUDG (FML $oi Σ) (iProp Σ),
    !Jsem JUDG (iProp Σ)}.
  Implicit Type δ : JUDG -n> iProp Σ.

  (** [storeJT_sem]: Semantics of [storeJT] *)
  Definition storeJT_sem δ (bPx : storeJT (FML $oi Σ)) : iProp Σ :=
    |->[store_wsat ⟦⟧(δ)] (□?(negb bPx.(untag).1) ⟦ bPx.(untag).2 ⟧(δ)).
  (** [storeJT_sem] is non-expansive *)
  #[export] Instance storeJT_sem_ne {δ} : NonExpansive (storeJT_sem δ).
  Proof. move=> ?[[??]][[??]][/=/leibniz_equiv_iff<-?]. solve_proper. Qed.
  (** [Dsem] over [storeJT] *)
  #[export] Instance storeJT_dsem : Dsem JUDG (storeJT (FML $oi Σ)) (iProp Σ) :=
    DSEM storeJT_sem _.
End storeJ.
Arguments storeJT_sem {_ _ _ _} _ _ /.
(** [storeJS]: Semantics of [storeJT] registered *)
Notation storeJS FML JUDG Σ := (inJS (storeJT (FML $oi Σ)) JUDG (iProp Σ)).

Section store_deriv.
  Context `{!storeGS FML Σ, !storeJ (FML $oi Σ) JUDG,
    !Dsem JUDG (FML $oi Σ) (iProp Σ), !Jsem JUDG (iProp Σ),
    !storeJS FML JUDG Σ}.
  Implicit Type Px Qx Rx : FML $oi Σ.

  (** Access using [stored] *)
  Lemma stored_acc {Px} : stored Px -∗[store_wsat ⟦⟧] ⟦ Px ⟧.
  Proof.
    rewrite store_unseal. iIntros "accPx".
    iDestruct (der_sound with "accPx") as "accPx". by rewrite in_js.
  Qed.
  (** Access using [pstored] *)
  Lemma pstored_acc {Px} : pstored Px -∗[store_wsat ⟦⟧] □ ⟦ Px ⟧.
  Proof.
    rewrite pstore_unseal. iIntros "accPx".
    iDestruct (der_sound with "accPx") as "accPx". by rewrite in_js.
  Qed.

  Context `{!Deriv (JUDG:=JUDG) ih δ}.

  (** Turn an accessor into [store] *)
  Lemma store_acsr_store {Px} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      |->[store_wsat ⟦⟧(δ')] ⟦ Px ⟧(δ')) ⊢
      store δ Px.
  Proof.
    rewrite store_unseal. iIntros "big". iApply Deriv_factor. iIntros (????).
    rewrite in_js /=. by iApply "big".
  Qed.
  (** Turn [store_acsr] into [pstore] *)
  Lemma store_acsr_pstore {Px} :
    □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      |->[store_wsat ⟦⟧(δ')] □ ⟦ Px ⟧(δ')) ⊢
      pstore δ Px.
  Proof.
    rewrite pstore_unseal. iIntros "#big !>". iApply Deriv_factor.
    iIntros (????). rewrite in_js /=. by iApply "big".
  Qed.

  (** Turn [store_tok] into [store] *)
  Lemma store_tok_store {Px} : store_tok Px ⊢ store δ Px.
  Proof.
    rewrite -store_acsr_store. iIntros "?" (????). by iApply store_tok_acc.
  Qed.
  (** Turn [pstore_tok] into [pstore] *)
  Lemma pstore_tok_pstore {Px} : pstore_tok Px ⊢ pstore δ Px.
  Proof.
    rewrite -store_acsr_pstore. iIntros "#?" (????) "!>".
    by iApply pstore_tok_acc.
  Qed.

  (** Allocate [store] *)
  Lemma store_alloc Px : ⟦ Px ⟧(δ) =[store_wsat ⟦⟧(δ)]=∗ store δ Px.
  Proof. rewrite -store_tok_store. exact: store_tok_alloc. Qed.
  (** Allocate [pstore] suspending the world satisfaction *)
  Lemma pstore_alloc_suspend Px :
    store_wsat ⟦⟧(δ) ==∗ pstore δ Px ∗ (□ ⟦ Px ⟧(δ) -∗ store_wsat ⟦⟧(δ)).
  Proof. rewrite -pstore_tok_pstore. exact: pstore_tok_alloc_suspend. Qed.
  Lemma pstore_alloc Px : □ ⟦ Px ⟧(δ) =[store_wsat ⟦⟧(δ)]=∗ pstore δ Px.
  Proof. rewrite -pstore_tok_pstore. exact: pstore_tok_alloc. Qed.

  (** Convert [store] with [-∗] *)
  Lemma store_wand {Px Qx} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Px ⟧(δ') -∗[store_wsat ⟦⟧(δ')] ⟦ Qx ⟧(δ')) -∗
      store δ Px -∗ store δ Qx.
  Proof.
    rewrite store_unseal. iIntros "PQ accPx". iApply Deriv_factor.
    iIntros (??? to). rewrite /store_def to !in_js /=. iMod "accPx" as "Px".
    by iApply "PQ".
  Qed.
  (** Convert [pstore] with [-∗] *)
  Lemma pstore_wand {Px Qx} :
    □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      □ ⟦ Px ⟧(δ') -∗[store_wsat ⟦⟧(δ')] □ ⟦ Qx ⟧(δ')) -∗
      pstore δ Px -∗ pstore δ Qx.
  Proof.
    rewrite pstore_unseal. iIntros "#PQ #accPx !>". iApply Deriv_factor.
    iIntros (??? to). rewrite /store_def to !in_js /=. iMod "accPx" as "Px".
    by iApply "PQ".
  Qed.

  (** Merge [store]s *)
  Lemma store_merge {Px Qx Rx} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Px ⟧(δ') -∗ ⟦ Qx ⟧(δ') -∗[store_wsat ⟦⟧(δ')] ⟦ Rx ⟧(δ')) -∗
      store δ Px -∗ store δ Qx -∗ store δ Rx.
  Proof.
    rewrite store_unseal. iIntros "PQR accPx accQx". iApply Deriv_factor.
    iIntros (??? to). rewrite /store_def !to !in_js /=.
    iMod "accPx" as "Px". iMod "accQx" as "Qx".
    iApply ("PQR" with "[//] [//] [//] Px Qx").
  Qed.
  (** Merge [pstore]s *)
  Lemma pstore_merge {Px Qx Rx} :
    □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      □ ⟦ Px ⟧(δ') -∗ □ ⟦ Qx ⟧(δ') -∗[store_wsat ⟦⟧(δ')] □ ⟦ Rx ⟧(δ')) -∗
      pstore δ Px -∗ pstore δ Qx -∗ pstore δ Rx.
  Proof.
    rewrite pstore_unseal. iIntros "#PQR #accPx #accQx !>". iApply Deriv_factor.
    iIntros (??? to). rewrite /store_def !to !in_js /=.
    iMod "accPx" as "Px". iMod "accQx" as "Qx".
    iApply ("PQR" with "[//] [//] [//] Px Qx").
  Qed.
End store_deriv.

(** ** Constructor *)

From nola.iris Require Import cif.

(** [storeCT]: Constructor for [store] *)
Variant storeCT_id := .
Definition storeCT :=
  Cifcon storeCT_id bool (λ _, Empty_set) (λ _, unit) (λ _, unitO) _.
(** [storeC]: [storeCT] registered *)
Notation storeC := (inC storeCT).

Section storeC.
  Context `{!storeC CON} {Σ}.
  Implicit Type Px : cif CON Σ.
  (** Formulas *)
  Definition cif_store Px : cif CON Σ :=
    cif_ecustom storeCT true nullary (unary Px) ().
  Definition cif_pstore Px : cif CON Σ :=
    cif_ecustom storeCT false nullary (unary Px) ().
  (** The formulas are non-expansive *)
  #[export] Instance cif_store_ne : NonExpansive cif_store.
  Proof. move=> ????. apply cif_ecustom_ne; solve_proper. Qed.
  #[export] Instance cif_store_proper : Proper ((≡) ==> (≡)) cif_store.
  Proof. apply ne_proper, _. Qed.
  #[export] Instance cif_pstore_ne : NonExpansive cif_pstore.
  Proof. move=> ????. apply cif_ecustom_ne; solve_proper. Qed.
  #[export] Instance cif_pstore_proper : Proper ((≡) ==> (≡)) cif_pstore.
  Proof. apply ne_proper, _. Qed.
  (** The formulas are productive *)
  #[export] Instance cif_store_productive : Productive cif_store.
  Proof.
    move=> ????. apply cif_ecustom_preserv_productive=>//.
    by apply fun_proeq_later.
  Qed.
  #[export] Instance cif_pstore_productive : Productive cif_pstore.
  Proof.
    move=> ????. apply cif_ecustom_preserv_productive=>//.
    by apply fun_proeq_later.
  Qed.

  Context `{!storeGS (cifOF CON) Σ, !storeJ (cifO CON Σ) JUDG}.
  (** Semantics of [storeCT] *)
  Definition storeCT_sem δ b : cif CON Σ → iProp Σ :=
    if b then store δ else pstore δ.
  #[export] Program Instance storeCT_ecsem : Ecsem storeCT CON JUDG Σ :=
    ECSEM (λ _ δ b _ Φx _, storeCT_sem δ b (Φx ())) _.
  Next Obligation.
    move=>/= ??*? b ?*?? eqv ?*. case b=>/=; f_equiv; apply eqv.
  Qed.
End storeC.
(** [storeC] semantics registered *)
Notation storeCS := (inCS storeCT).

(** Reify into formulas *)
Section storeC.
  Context `{!Csem CON JUDG Σ, !Jsem JUDG (iProp Σ), !storeGS (cifOF CON) Σ,
    !storeC CON, !storeJ (cifO CON Σ) JUDG, !storeCS CON JUDG Σ,
    !storeJS (cifOF CON) JUDG Σ}.

  #[export] Program Instance store_as_cif {Px} :
    AsCif CON (λ δ, store δ Px) := AS_CIF (cif_store Px) _.
  Next Obligation. move=>/= *. by rewrite sem_ecustom. Qed.
  #[export] Program Instance pstore_as_cif {Px} :
    AsCif CON (λ δ, pstore δ Px) := AS_CIF (cif_pstore Px) _.
  Next Obligation. move=>/= *. by rewrite sem_ecustom. Qed.
End storeC.
