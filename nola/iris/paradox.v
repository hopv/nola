(** * Paradoxes *)

From nola Require Export prelude.
From iris.proofmode Require Import proofmode.
Local Set Warnings "-notation-overridden".

(** ** Paradox of the later-eliminating total weakest precondition *)
Module twp. Section twp.
  Context {PROP : bi} `{!BiAffine PROP, !BiLöb PROP}.

  Context {expr : Type}.

  (** Pure execution *)
  Context (pure_exec : expr → expr → Prop).
  Local Infix "→p" := pure_exec (at level 70, no associativity).

  (** Total weakest precondition *)
  Context (twp : expr → PROP → PROP).
  (** Later-elimination *)
  Hypothesis twp_step : ∀{e e' P}, e →p e' → ▷ twp e' P ⊢ twp e P.

  (** Loop expression *)
  Context (loop : expr).
  Hypotheses loop_loop : loop →p loop.

  (** Paradox, saying that [loop] terminates bringing [False] *)
  Lemma twp_loop : ⊢ twp loop False.
  Proof. iLöb as "IH". by iApply twp_step; [apply loop_loop|]. Qed.
End twp. End twp.

(** ** Paradox of later-free invariants with an unguarded fancy update

  This is a minimal construction, not using nested invariants or impredicative
  quantifiers, simplified from the known proof (published in Krebbers et al.'s
  ESOP 2017 paper). *)
Module inv. Section inv.
  Context {PROP : bi} `{!BiAffine PROP}.

  (** Update modalty with a binary mask *)
  Context {mask : Type} (mask_empty mask_full : mask).
  Local Notation "∅" := mask_empty. Local Notation "⊤" := mask_full.
  Context (fupd : mask → PROP → PROP).
  Local Notation "|={ E }=> P" := (fupd E P) : bi_scope.
  Hypothesis fupd_intro : ∀{E P}, P ⊢ |={E}=> P.
  Hypothesis fupd_mono : ∀{E P Q}, (P ⊢ Q) → (|={E}=> P) ⊢ |={E}=> Q.
  Hypothesis fupd_fupd : ∀{E P}, (|={E}=> |={E}=> P) ⊢ |={E}=> P.
  Hypothesis fupd_frame_l : ∀{E P} Q, (|={E}=> P) ∗ Q ⊢ |={E}=> P ∗ Q.
  Hypothesis fupd_mask_mono : ∀{P}, (|={∅}=> P) ⊢ |={⊤}=> P.

  (** Later-free invariant *)
  Context (inv : PROP → PROP).
  Hypothesis inv_persistent : ∀{P}, Persistent (inv P).
  Hypothesis inv_alloc : ∀ P, P ⊢ |={⊤}=> inv P.
  Hypothesis inv_acc : ∀ P Q R,
    (P ∗ Q ⊢ |={∅}=> P ∗ R) → (inv P ∗ Q ⊢ |={⊤}=> R).

  (** Two-state STS: [start] -> [finished],
    where the former is authoritative and the latter is persistent

    Whereas the original proof only assumed duplicability of [finished],
    our proof uses persistence, which is the key to simplicity. *)
  Context (gname : Type) (start finished : gname → PROP).
  Hypothesis start_alloc : ⊢ |={∅}=> ∃ γ, start γ.
  Hypotheses start_finish : ∀{γ}, start γ ⊢ |={∅}=> finished γ.
  Hypothesis start_finished_no : ∀{γ}, start γ ∗ finished γ ⊢ False.
  Hypothesis finished_persistent : ∀{γ}, Persistent (finished γ).

  (** Lemmas on [fupd] *)
  Lemma fupd_elim {E P Q} : (P ⊢ |={E}=> Q) → (|={E}=> P) ⊢ |={E}=> Q.
  Proof. iIntros (PQ) "P". iApply fupd_fupd. by iApply fupd_mono. Qed.
  Lemma fupd_elim_mask_mono {P Q} : (P ⊢ |={⊤}=> Q) → (|={∅}=> P) ⊢ |={⊤}=> Q.
  Proof. rewrite fupd_mask_mono. apply fupd_elim. Qed.

  (** Evil invariant *)
  Definition evil_body γ : PROP := start γ ∨ □ |={⊤}=> False.
  Definition evil γ : PROP := inv (evil_body γ).

  (** Allocate [evil] *)
  Lemma evil_alloc : ⊢ |={⊤}=> ∃ γ, evil γ.
  Proof.
    iApply fupd_elim_mask_mono; [|iApply start_alloc]. iDestruct 1 as (γ) "s".
    iApply fupd_mono; [|iApply (inv_alloc (evil_body γ))]; [|by iLeft].
    iIntros. by iExists γ.
  Qed.

  (** Contradiction from [evil] and [finished] *)
  Lemma evil_finished_no {γ} : evil γ ∗ finished γ ⊢ |={⊤}=> False.
  Proof.
    iIntros "P". iApply fupd_fupd. iApply (inv_acc _ (finished γ)); [|done].
    iIntros "[[s|#⊥] #f]".
    - iDestruct (start_finished_no with "[$s $f]") as "[]".
    - iApply fupd_intro. iFrame "⊥".
  Qed.

  (** Contradiction from [evil] *)
  Lemma evil_no {γ} : evil γ ⊢ |={⊤}=> False.
  Proof.
    iIntros "#e". iApply fupd_fupd.
    iApply (inv_acc _ (evil γ)); [|by iFrame "e"].
    iIntros "[[s|#⊥] #e]"; [|iApply fupd_intro; iFrame "⊥"].
    iApply fupd_elim; last first.
    { iApply (fupd_frame_l (evil γ)). iSplit; by [iApply start_finish|]. }
    iIntros "[#f #e]". iApply fupd_intro.
    iDestruct (evil_finished_no with "[$e $f]") as "$".
  Qed.

  (** Contradiction *)
  Lemma no : ⊢ |={⊤}=> False.
  Proof.
    iApply fupd_elim; [|iApply evil_alloc]. iDestruct 1 as (γ) "#e".
    by iApply evil_no.
  Qed.
End inv. End inv.
