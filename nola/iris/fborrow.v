
(** * Fractured borrowing *)

From nola.iris Require Export borrow.
From nola.iris Require Import sinv.
From iris.bi Require Import fractional.
From iris.proofmode Require Import proofmode.

(** State of a fractured borrower *)
Local Definition fbor_st PROP : Type := lft *' (Qp → PROP).

(** Ghost state for fractured borrowing *)
Class fborrowGS PROP Σ := fborrowGS_in : sinvGS (fbor_st PROP) Σ.
Local Existing Instance fborrowGS_in.
Class fborrowGpreS PROP Σ := fborrowGpreS_in : sinvGpreS (fbor_st PROP) Σ.
Local Existing Instance fborrowGpreS_in.
Definition fborrowΣ PROP : gFunctors := sinvΣ (fbor_st PROP).
#[export] Instance subG_fborrow `{!subG (fborrowΣ PROP) Σ} :
  fborrowGpreS PROP Σ.
Proof. solve_inG. Qed.

Section fborrow.
  Context `{!fborrowGS PROP Σ, !borrowGS PROP Σ}.
  Implicit Type (c : bool) (Φ : Qp → PROP).

  (** Fractional borrower token *)
  Local Definition fbor_tok_def α Φ : iProp Σ :=
    ∃ α', α ⊑□ α' ∗ sinv_tok (α', Φ)'.
  Local Lemma fbor_tok_aux : seal fbor_tok_def. Proof. by eexists. Qed.
  Definition fbor_tok := fbor_tok_aux.(unseal).
  Local Lemma fbor_tok_unseal : fbor_tok = fbor_tok_def.
  Proof. exact: seal_eq. Qed.

  (** [fbor_tok] is persistent and timeless *)
  #[export] Instance fbor_tok_persistent {α Φ} : Persistent (fbor_tok α Φ).
  Proof. rewrite fbor_tok_unseal. exact _. Qed.
  #[export] Instance fbor_tok_timeless {α Φ} : Timeless (fbor_tok α Φ).
  Proof. rewrite fbor_tok_unseal. exact _. Qed.

  (** Modify the lifetime of [fbor_tok] *)
  Lemma fbor_tok_lft {α α' Φ} : α' ⊑□ α -∗ fbor_tok α Φ -∗ fbor_tok α' Φ.
  Proof.
    rewrite fbor_tok_unseal. iIntros "#? [%α''[#? f]]". iExists _. iFrame "f".
    by iApply lft_sincl_trans.
  Qed.

  (** Choice between [bor_ctok] and [bor_tok] *)
  Definition bor_xtok c := if c then bor_ctok else bor_tok.
  Lemma bor_xtok_tok {c α P} : bor_xtok c α P ⊢ bor_tok α P.
  Proof. case: c; [exact bor_ctok_tok|done]. Qed.
  Lemma bor_ctok_xtok {c α P} : bor_ctok α P ⊢ bor_xtok c α P.
  Proof. case: c; [done|exact bor_ctok_tok]. Qed.
  #[export] Instance bor_xtok_timeless {c α P} : Timeless (bor_xtok c α P).
  Proof. case: c; exact _. Qed.

  (** World satisfaction for the fractional borrowing machinery *)
  Definition fborrow_wsat_def c : iProp Σ :=
    sinv_wsat (λ '(α, Φ)', ∃ q, bor_xtok c α (Φ q))%I.
  Local Lemma fborrow_wsat_aux : seal fborrow_wsat_def. Proof. by eexists. Qed.
  Definition fborrow_wsat := fborrow_wsat_aux.(unseal).
  Local Lemma fborrow_wsat_unseal : fborrow_wsat = fborrow_wsat_def.
  Proof. exact: seal_eq. Qed.

  (** [fborrow_wsat] is timeless *)
  #[export] Instance fborrow_wsat_timeless {c} : Timeless (fborrow_wsat c).
  Proof. rewrite fborrow_wsat_unseal. exact _. Qed.

  (** Turn [bor_ctok] into [fbor_tok] *)
  Lemma bor_fbor_tok {α q} c Φ :
    bor_xtok c α (Φ q) =[fborrow_wsat c]=∗ fbor_tok α Φ.
  Proof.
    rewrite fborrow_wsat_unseal. iIntros "b W".
    iMod (sinv_alloc (_,_)' with "W") as "[#t →W]". iModIntro. iSplitL.
    { iApply "→W". by iExists _. }
    rewrite fbor_tok_unseal. iExists _. iSplit; by [iApply lft_sincl_refl|].
  Qed.
  Lemma bor_fbor_toks {α} c Φql :
    ([∗ list] '(Φ, q)' ∈ Φql, bor_xtok c α (Φ q)) =[fborrow_wsat c]=∗
      [∗ list] Φ ∈ Φql.*1', fbor_tok α Φ.
  Proof.
    elim: Φql; [by iIntros|]=>/= [[Φ q]Φql] IH.
    iIntros "[b bl]". iMod (IH with "bl") as "$". by iApply bor_fbor_tok.
  Qed.

  (** Open [fbor_tok] *)
  Lemma fbor_tok_take' `{!GenUpd M} {intp α q Φ} :
    □ (∀ r s, intp (Φ (r + s)%Qp) ∗-∗ intp (Φ r) ∗ intp (Φ s)) -∗
    q.[α] -∗ fbor_tok α Φ =[fborrow_wsat true ∗ borrow_wsat M intp]=∗
      q.[α] ∗ ∃ r, bor_ctok α (Φ r).
  Proof.
    rewrite fbor_tok_unseal fborrow_wsat_unseal.
    iIntros "#fr α [%α'[#⊑ i]] [F B]".
    iDestruct (sinv_acc with "i F") as "[[%r c] →F]".
    iMod (lft_sincl_tok_acc with "⊑ α") as (s) "[α' →α]".
    iMod (bor_ctok_open with "α' c B") as "[B [o Φ]]".
    rewrite -(Qp.div_2 r). iDestruct ("fr" with "Φ") as "[Φ Φ']".
    iMod (obor_tok_subdiv [_;_] with "o [Φ Φ'] [] B") as "[$ [α'[c[c' _]]]]".
    { by iFrame. } { iIntros "_ [Φ[Φ' _]]". iModIntro. iApply "fr". iFrame. }
    iModIntro. iDestruct ("→α" with "α'") as "$". iSplitL "→F c".
    { iApply "→F". by iExists _. } { iExists _. by iApply bor_ctok_lft. }
  Qed.
  Lemma fbor_tok_open' `{!GenUpd M} {intp α q Φ} :
    □ (∀ r s, intp (Φ (r + s)%Qp) ∗-∗ intp (Φ r) ∗ intp (Φ s)) -∗
    q.[α] -∗ fbor_tok α Φ =[fborrow_wsat true ∗ borrow_wsat M intp]=∗
      ∃ r, obor_tok α (Φ r) q ∗ intp (Φ r).
  Proof.
    iIntros "fr α f". iMod (fbor_tok_take' with "fr α f") as "[α[% c]]".
    iMod (bor_ctok_open with "α c") as "?". iModIntro. by iExists _.
  Qed.
  Lemma fbor_tok_take `{!GenUpd M} {c intp α q Φ} :
    □ (∀ r s, intp (Φ (r + s)%Qp) ∗-∗ intp (Φ r) ∗ intp (Φ s)) -∗
    q.[α] -∗ fbor_tok α Φ -∗ modw M (fborrow_wsat c ∗ borrow_wsat M intp)
      (q.[α] ∗ ∃ r, bor_ctok α (Φ r)).
  Proof.
    rewrite fbor_tok_unseal fborrow_wsat_unseal.
    iIntros "#fr α [%α'[#⊑ i]] [F B]".
    iDestruct (sinv_acc with "i F") as "[[%r b] →F]". rewrite bor_xtok_tok.
    iMod (lft_sincl_tok_acc with "⊑ α") as (s) "[α' →α]".
    iMod (bor_tok_open with "α' b B") as "[B [o Φ]]". rewrite -(Qp.div_2 r).
    iDestruct ("fr" with "Φ") as "[Φ Φ']".
    iMod (obor_tok_subdiv [_;_] with "o [Φ Φ'] [] B") as "[$ [α'[c[c' _]]]]".
    { by iFrame. } { iIntros "_ [Φ[Φ' _]]". iModIntro. iApply "fr". iFrame. }
    iModIntro. iDestruct ("→α" with "α'") as "$". iSplitL "→F c".
    { iApply "→F". iExists _. by rewrite bor_ctok_xtok. }
    { iExists _. by iApply bor_ctok_lft. }
  Qed.
  Lemma fbor_tok_open `{!GenUpd M} {c intp α q Φ} :
    □ (∀ r s, intp (Φ (r + s)%Qp) ∗-∗ intp (Φ r) ∗ intp (Φ s)) -∗
    q.[α] -∗ fbor_tok α Φ -∗ modw M (fborrow_wsat c ∗ borrow_wsat M intp)
      (∃ r, obor_tok α (Φ r) q ∗ intp (Φ r)).
  Proof.
    iIntros "fr α f". iMod (fbor_tok_take with "fr α f") as "[α[% c]]".
    iMod (bor_ctok_open with "α c") as "?". iModIntro. by iExists _.
  Qed.
End fborrow.

(** Allocate [fborrow_wsat] *)
Lemma fborrow_wsat_alloc `{!fborrowGpreS PROP Σ, !borrowGS PROP Σ} :
  ⊢ |==> ∃ _ : fborrowGS PROP Σ, ∀ c, fborrow_wsat c.
Proof.
  iMod sinv_wsat_alloc as (?) "W". iModIntro. iExists _. iIntros (?).
  rewrite fborrow_wsat_unseal. iApply "W".
Qed.
