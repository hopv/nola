(** * Stored propositions *)

From nola.bi Require Export internal modw.
From nola.iris Require Export cif dinv.
From iris.base_logic.lib Require Export token.
From iris.proofmode Require Import proofmode.
Import iPropAppNotation ModwNotation CsemNotation.

Implicit Type FML : oFunctor.

Section store.
  Context `{!dinvGS (cifOF CON) Σ, tokenG Σ, !Csem CON JUDG Σ}.
  Implicit Type Px : cif CON Σ.

  (** [store_tok]: Exclusive stored proposition token *)
  Local Definition store_tok_def Px : iProp Σ :=
    ∃ γ, token γ ∗ dinv_tok (Px ∨ ▷ token γ)%cif.
  Local Definition store_tok_aux : seal store_tok_def. Proof. by eexists. Qed.
  Definition store_tok := store_tok_aux.(unseal).
  Local Lemma store_tok_unseal : store_tok = store_tok_def.
  Proof. exact: seal_eq. Qed.

  (** [store_tok] is non-expansive *)
  #[export] Instance store_tok_ne : NonExpansive store_tok.
  Proof. rewrite store_tok_unseal. solve_proper. Qed.
  #[export] Instance store_tok_proper : Proper ((≡) ==> (⊣⊢)) store_tok.
  Proof. apply ne_proper, _. Qed.

  (** Allocate [store_tok] *)
  Lemma store_tok_alloc {δ} Px : ⟦ Px ⟧ᶜ(δ) =[dinv_wsat ⟦⟧ᶜ(δ)]=∗ store_tok Px.
  Proof.
    rewrite store_tok_unseal. iIntros "Px W". iMod token_alloc as (γ) "$".
    iMod (dinv_tok_alloc_suspend (FML:=cifOF _) (Px ∨ ▷ token γ)%cif
      with "W") as "/=[$ cl]".
    iModIntro. iApply "cl". iFrame.
  Qed.

  (** Access the content of [store_tok] *)
  Lemma store_tok_acc {δ} Px : store_tok Px -∗[dinv_wsat ⟦⟧ᶜ(δ)]◇ ⟦ Px ⟧ᶜ(δ).
  Proof.
    rewrite store_tok_unseal. iIntros "[%[t i]] W".
    iDestruct (dinv_tok_acc with "i W") as "/=[[$|>t'] →W]"; last first.
    { iDestruct (token_exclusive with "t t'") as %[]. }
    iModIntro. iApply "→W". by iRight.
  Qed.
End store.
