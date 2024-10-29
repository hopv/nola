(** * Stored propositions *)

From nola.bi Require Export internal modw.
From nola.iris Require Export iprop.
From nola.iris Require Import sinv.
From iris.base_logic Require Import lib.token.
From iris.proofmode Require Import proofmode.
Import iPropAppNotation ModwNotation.

Implicit Type (FML : oFunctor) (i : positive).

(** Formula for stored propositions *)
Local Definition store_fml FML : oFunctor := boolO * FML.

(** Formula for stored propositions *)
Class storeGpreS FML Σ := StoreGpreS {
  storeGpreS_sinv : sinvGpreS (store_fml FML) Σ;
  storeGpreS_token : tokenG Σ;
}.
Local Existing Instance storeGpreS_sinv.
Local Existing Instance storeGpreS_token.
Class storeGS FML Σ := StoreGS {
  storeGS_sinv : sinvGS (store_fml FML) Σ;
  storeGS_token : tokenG Σ;
}.
Local Existing Instance storeGS_sinv. Local Existing Instance storeGS_token.
Definition storeΣ FML `{!oFunctorContractive FML} :=
  #[sinvΣ (store_fml FML); tokenΣ].
#[export] Instance subG_storeΣ
  `{!oFunctorContractive FML, !subG (storeΣ FML) Σ} : storeGpreS FML Σ.
Proof. solve_inG. Qed.

Section store.
  Context `{!storeGS FML Σ}.
  Implicit Type (Px : FML $oi Σ) (bPx : store_fml FML $oi Σ).

  (** [store_tok]: Exclusive stored proposition token *)
  Local Definition store_tok_def (Px : FML $oi Σ) : iProp Σ :=
    ∃ i, token i ∗ sinv_tok i (true, Px).
  Local Definition store_tok_aux : seal store_tok_def. Proof. by eexists. Qed.
  Definition store_tok := store_tok_aux.(unseal).
  Local Lemma store_tok_unseal : store_tok = store_tok_def.
  Proof. exact: seal_eq. Qed.

  (** [pstore_tok]: Persistent stored proposition token *)
  Local Definition pstore_tok_def (Px : FML $oi Σ) : iProp Σ :=
    ∃ i, sinv_tok i (false, Px).
  Local Definition pstore_tok_aux : seal pstore_tok_def. Proof. by eexists. Qed.
  Definition pstore_tok := pstore_tok_aux.(unseal).
  Local Lemma pstore_tok_unseal : pstore_tok = pstore_tok_def.
  Proof. exact: seal_eq. Qed.

  (** [store_tok] and [pstore_tok] are non-expansive *)
  #[export] Instance store_tok_ne : NonExpansive store_tok.
  Proof. rewrite store_tok_unseal. solve_proper. Qed.
  #[export] Instance store_tok_proper : Proper ((≡) ==> (⊣⊢)) store_tok.
  Proof. apply ne_proper, _. Qed.
  #[export] Instance pstore_tok_ne : NonExpansive pstore_tok.
  Proof. rewrite pstore_tok_unseal. solve_proper. Qed.
  #[export] Instance pstore_tok_proper : Proper ((≡) ==> (⊣⊢)) pstore_tok.
  Proof. apply ne_proper, _. Qed.
  (** [pstore_tok] is persistent *)
  #[export] Instance pstore_tok_persistent {Px} : Persistent (pstore_tok Px).
  Proof. rewrite pstore_tok_unseal. exact _. Qed.
  (** [store_tok] and [pstore_tok] are timeless for discrete formulas *)
  #[export] Instance store_tok_timeless `{!Discrete Px} :
    Timeless (store_tok Px).
  Proof. rewrite store_tok_unseal. exact _. Qed.
  #[export] Instance pstore_tok_timeless `{!Discrete Px} :
    Timeless (pstore_tok Px).
  Proof. rewrite pstore_tok_unseal. exact _. Qed.

  (** Semantics *)
  Local Definition store_sem (sm : FML $oi Σ → iProp Σ) i bPx : iProp Σ :=
    (if bPx.1 then sm bPx.2 ∨ token i else □ sm bPx.2)%I.
  Arguments store_sem _ _ _ /.
  (** [store_sem sm] is non-expansive when [sm] is *)
  Local Lemma store_sem_ne {sm} :
    internal_ne sm ⊢@{iProp Σ} ∀ i, internal_ne (store_sem sm i).
  Proof.
    iIntros "#Ne" (?[b ?][??]). rewrite prod_equivI /= discrete_eq.
    rewrite leibniz_equiv_iff. iIntros "[%eq ≡]". move: eq=> <-.
    case: b; by iRewrite ("Ne" with "≡").
  Qed.

  (** World satisfaction *)
  Local Definition store_wsat_def (sm : FML $oi Σ -d> iProp Σ) : iProp Σ :=
    sinv_wsat (store_sem sm).
  Local Definition store_wsat_aux : seal store_wsat_def. Proof. by eexists. Qed.
  Definition store_wsat := store_wsat_aux.(unseal).
  Local Lemma store_wsat_unseal : store_wsat = store_wsat_def.
  Proof. exact: seal_eq. Qed.

  (** [store_wsat] is non-expansive *)
  #[export] Instance store_wsat_ne : NonExpansive store_wsat.
  Proof.
    rewrite store_wsat_unseal. unfold store_wsat_def, store_sem. solve_proper.
  Qed.
  #[export] Instance store_wsat_proper : Proper ((≡) ==> (≡)) store_wsat.
  Proof. apply ne_proper, _. Qed.

  (** Allocate [store_tok] *)
  Lemma store_tok_alloc {sm} Px : sm Px =[store_wsat sm]=∗ store_tok Px.
  Proof.
    rewrite store_tok_unseal store_wsat_unseal. iIntros "Px W".
    iDestruct (sinv_tok_alloc (FML:=store_fml _) (true, Px) with "W")
      as (I) "big".
    iMod (token_alloc_strong (.∉ I)) as (??) "$".
    { apply (pred_infinite_set (C:=gset positive))=> X. exists (fresh (I ∪ X)).
      apply not_elem_of_union, is_fresh. }
    iMod ("big" with "[//]") as "[$ →W]". iModIntro. iApply "→W". by iLeft.
  Qed.

  (** Allocate [pstore_tok] suspending the world satisfaction *)
  Lemma pstore_tok_alloc_suspend {sm} Px :
    store_wsat sm ==∗ pstore_tok Px ∗ (□ sm Px -∗ store_wsat sm).
  Proof.
    rewrite pstore_tok_unseal store_wsat_unseal. iIntros "W".
    iDestruct (sinv_tok_alloc (FML:=store_fml _) (false, Px) with "W")
      as (I) "big".
    iMod ("big" $! (fresh I) with "[%]") as "[#inv →W]". { apply is_fresh. }
    iModIntro. iFrame "inv". iIntros "?". by iApply "→W".
  Qed.
  (** Allocate [pstore_tok] *)
  Lemma pstore_tok_alloc {sm} Px : □ sm Px =[store_wsat sm]=∗ pstore_tok Px.
  Proof.
    iIntros "? W". iMod (pstore_tok_alloc_suspend with "W") as "[$ →W]". iModIntro.
    by iApply "→W".
  Qed.

  (** Access the content of [store_tok] *)
  Lemma store_tok_acc {sm} Px : store_tok Px -∗[store_wsat sm] sm Px.
  Proof.
    rewrite store_tok_unseal store_wsat_unseal. iIntros "[%[tok inv]] W".
    iDestruct (sinv_tok_acc with "inv W") as "/=[[$|tok'] →W]"; last first.
    { iDestruct (token_exclusive with "tok tok'") as %[]. }
    iApply "→W". by iRight.
  Qed.
  (** Access the content of [pstore_tok] *)
  Lemma pstore_tok_acc {sm} Px : pstore_tok Px -∗[store_wsat sm] □ sm Px.
  Proof.
    rewrite pstore_tok_unseal store_wsat_unseal. iIntros "[% inv] W".
    iDestruct (sinv_tok_acc with "inv W") as "/=[#Px →W]". iFrame "Px".
    by iApply "→W".
  Qed.
End store.

(** Allocate [store_wsat] *)
Lemma store_wsat_alloc `{!storeGpreS FML Σ} :
  ⊢ |==> ∃ _ : storeGS FML Σ, ∀ sm, internal_ne sm -∗ store_wsat sm.
Proof.
  iMod sinv_wsat_alloc as (γ) "W". iModIntro. iExists (StoreGS _ _ _ _).
  iIntros (?) "Ne". rewrite store_wsat_unseal. iApply "W".
  by iApply store_sem_ne.
Qed.
