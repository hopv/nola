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

  (** The bad proposition *)
  Definition bad γ : PROP := start γ ∨ □ |={⊤}=> False.

  (** Later-free invariant *)
  Context (inv_bad : gname → PROP).
  Hypothesis inv_bad_persistent : ∀{γ}, Persistent (inv_bad γ).
  Hypothesis inv_bad_alloc : ∀{γ}, bad γ ⊢ |={⊤}=> inv_bad γ.
  Hypothesis inv_bad_acc : ∀ {γ} Q R,
    (bad γ ∗ Q ⊢ |={∅}=> bad γ ∗ R) → (inv_bad γ ∗ Q ⊢ |={⊤}=> R).

  (** Allocate [inv_bad γ] *)
  Lemma inv_bad_init : ⊢ |={⊤}=> ∃ γ, inv_bad γ.
  Proof.
    iApply fupd_elim_mask_mono; [|by iApply start_alloc].
    iDestruct 1 as (γ) "s".
    iApply fupd_mono; [|iApply inv_bad_alloc]; [|by iLeft]. iIntros.
    by iExists γ.
  Qed.

  (** Contradiction from [inv_bad] and [finished] *)
  Lemma inv_bad_finished_no {γ} : inv_bad γ ∗ finished γ ⊢ |={⊤}=> False.
  Proof.
    iIntros "P". iApply fupd_fupd. iApply (inv_bad_acc (finished γ)); [|done].
    iIntros "[[s|#⊥] #f]".
    - iDestruct (start_finished_no with "[$s $f]") as "[]".
    - iApply fupd_intro. iFrame "⊥".
  Qed.

  (** Contradiction from [inv_bad] *)
  Lemma inv_bad_no {γ} : inv_bad γ ⊢ |={⊤}=> False.
  Proof.
    iIntros "#i". iApply fupd_fupd.
    iApply (inv_bad_acc (inv_bad γ)); [|by iSplit].
    iIntros "[[s|#⊥] #f]"; [|iApply fupd_intro; by iFrame "⊥"].
    iApply fupd_elim; last first.
    { iApply (fupd_frame_l (inv_bad γ)). iSplit; by [iApply start_finish|]. }
    iIntros "[#f #i]". iApply fupd_intro.
    iDestruct (inv_bad_finished_no with "[$i $f]") as "$".
  Qed.

  (** Contradiction *)
  Lemma no : ⊢ |={⊤}=> False.
  Proof.
    iApply fupd_elim; [|by iApply inv_bad_init]. iDestruct 1 as (γ) "#e".
    by iApply inv_bad_no.
  Qed.
End inv. End inv.
