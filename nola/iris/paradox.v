(** * Paradoxes *)

From nola Require Export prelude.
From iris.proofmode Require Import proofmode.
Local Set Warnings "-notation-overridden".

(** ** Paradox of the later-eliminating total weakest precondition *)
Module twp. Section twp.
  (** Step-indexed logic *)
  Context {PROP : bi} `{!BiLöb PROP}.
  (** Expression *)
  Context {expr : Type}.

  (** Pure execution *)
  Context (pure_exec : expr → expr → Prop).
  Local Infix "→p" := pure_exec (at level 70, no associativity).

  (** Total weakest precondition *)
  Context (twp : expr → PROP → PROP).
  (** Later-elimination for pure execution *)
  Hypothesis twp_step : ∀{e e' P}, e →p e' → ▷ twp e' P ⊢ twp e P.

  (** Loop expression *)
  Context (loop : expr).
  Hypothesis loop_loop : loop →p loop.

  (** Paradox, saying that [loop] terminates bringing [False] *)
  Lemma twp_loop : ⊢ twp loop False.
  Proof. iLöb as "IH". by iApply twp_step; [apply loop_loop|]. Qed.
End twp. End twp.

(** ** Paradox of the later-free invariant over an unguarded fancy update

  This is a minimal construction, not using nested invariants or impredicative
  quantifiers, simplifying the known paradox (published in Krebbers et al.'s
  ESOP 2017 paper).
  The construction is analogous to Landin's knot but at the logic level. *)
Module inv_fupd. Section inv_fupd.
  (** Separation logic *)
  Context {PROP : bi} `{!BiAffine PROP}.

  (** Binary mask *)
  Context {mask : Type} (mask_empty mask_full : mask).
  Local Notation "∅" := mask_empty. Local Notation "⊤" := mask_full.
  (** Update modality *)
  Context (fupd : mask → PROP → PROP).
  Local Notation "|={ E }=> P" := (fupd E P) : bi_scope.
  Hypothesis fupd_intro : ∀{E P}, P ⊢ |={E}=> P.
  Hypothesis fupd_mono : ∀{E P Q}, (P ⊢ Q) → (|={E}=> P) ⊢ |={E}=> Q.
  Hypothesis fupd_fupd : ∀{E P}, (|={E}=> |={E}=> P) ⊢ |={E}=> P.
  Hypothesis fupd_frame_l : ∀{E P} Q, (|={E}=> P) ∗ Q ⊢ |={E}=> P ∗ Q.
  Hypothesis fupd_mask_mono : ∀{P}, (|={∅}=> P) ⊢ |={⊤}=> P.

  (** Lemmas on [fupd] *)
  Lemma fupd_elim {E P Q} : (P ⊢ |={E}=> Q) → (|={E}=> P) ⊢ |={E}=> Q.
  Proof. iIntros (PQ) "P". iApply fupd_fupd. by iApply fupd_mono. Qed.
  Lemma fupd_elim_mask_mono {P Q} : (P ⊢ |={⊤}=> Q) → (|={∅}=> P) ⊢ |={⊤}=> Q.
  Proof. rewrite fupd_mask_mono. apply fupd_elim. Qed.

  (** Two-state STS: [start] -> [finished],
    where the former is authoritative and the latter is persistent

    Whereas the original proof only assumed duplicability of [finished],
    our proof uses persistence, which is the key to simplicity. *)
  Context {gname : Type} (start finished : gname → PROP).
  Hypothesis start_alloc : ⊢ |={∅}=> ∃ γ, start γ.
  Hypothesis start_finish : ∀{γ}, start γ ⊢ |={∅}=> finished γ.
  Hypothesis start_finished_no : ∀{γ}, start γ ∗ finished γ ⊢ False.
  Hypothesis finished_persistent : ∀{γ}, Persistent (finished γ).

  (** Bad proposition with an unguarded fancy update *)
  Definition bad γ : PROP := start γ ∨ □ |={⊤}=> False.

  (** Later-free invariant over [bad] *)
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
End inv_fupd. End inv_fupd.

(** ** Paradox of the later-free invariant over an unguarded total Hoare triple,
  via Landin's knot *)
Module inv_landin. Section inv_landin.
  (** Separation logic *)
  Context {PROP : bi} `{!BiAffine PROP}.

  (** Binary mask *)
  Context {mask : Type} (mask_empty mask_full : mask).
  Local Notation "∅" := mask_empty. Local Notation "⊤" := mask_full.

  (** Location, value, closed expression *)
  Context {loc val expr : Type}.
  Context (atomic : expr → Prop).

  (** Points-to token *)
  Context (pointsto : loc → val → PROP).
  Local Notation "l ↦ v" := (pointsto l v) (at level 20) : bi_scope.

  (** Total Hoare triple *)
  Context (thoare : mask → expr → PROP → (val → PROP) → PROP).
  Local Notation "[[{ P } ] ] e @ E [[{ Ψ } ] ]" := (thoare E e P%I Ψ%I)
    (at level 20, format "'[hv' [[{  '[' P  ']' } ] ]  '/  ' e  '/' @  E  '/' [[{  '[hv' Ψ  ']' } ] ] ']'")
    : bi_scope.
  Hypothesis thoare_persistent : ∀{E e P Ψ},
    Persistent ([[{ P }]] e @ E [[{ Ψ }]]).
  Hypothesis thoare_pre : ∀{E e P Ψ} P',
    (P ⊢ P') → [[{ P' }]] e @ E [[{ Ψ }]] ⊢ [[{ P }]] e @ E [[{ Ψ }]].
  Hypothesis thoare_post : ∀{E e P Ψ} Ψ',
    (∀ v, Ψ' v ⊢ Ψ v) → [[{ P }]] e @ E [[{ Ψ' }]] ⊢ [[{ P }]] e @ E [[{ Ψ }]].
  Hypothesis thoare_frame : ∀{E e P Ψ R},
    [[{ P }]] e @ E [[{ Ψ }]] ⊢ [[{ P ∗ R }]] e @ E [[{ λ v, Ψ v ∗ R }]].
  Hypothesis thoare_exists : ∀{A E e Φ Ψ},
    (∀ a : A, [[{ Φ a }]] e @ E [[{ Ψ }]]) ⊢ [[{ ∃ a, Φ a }]] e @ E [[{ Ψ }]].
  Hypothesis thoare_pure : ∀{E e φ P Ψ},
    (⌜φ⌝ → [[{ P }]] e @ E [[{ Ψ }]]) ⊢ [[{ ⌜φ⌝ ∗ P }]] e @ E [[{ Ψ }]].
  Hypothesis thoare_self : ∀{E e Ψ}, ⊢
    [[{ [[{ True }]] e @ E [[{ Ψ }]] }]] e @ E [[{ Ψ }]].
  Hypothesis thoare_apply : ∀{E e Ψ} P, Persistent P →
    P ∗ [[{ P }]] e @ E [[{ Ψ }]] ⊢ [[{ True }]] e @ E [[{ Ψ }]].

  (** Expression with a variable *)
  Context {expr_val : Type}.
  (** Substitution *)
  Context (subst_val : expr_val → val → expr).
  Local Coercion subst_val : expr_val >-> Funclass.

  Implicit Types (l : loc) (v : val) (ev : expr_val).

  (** Location value *)
  Context (locval : loc → val).
  Local Coercion locval : loc >-> val.
  (** Function value *)
  Context (funval : expr → val).
  Local Notation "λ(), e" := (funval e) (at level 90).

  (** Nop *)
  Context (nop : expr).
  Hypothesis thoare_nop : ∀{P E}, ⊢ [[{ P }]] nop @ E [[{ λ _, P }]].
  (** Sequential execution *)
  Context (bind : expr → expr_val → expr).
  Local Notation "e >>= ev" := (bind e ev) (at level 80, right associativity).
  Hypothesis thoare_bind : ∀{E e ev P Ψ} Φ,
    [[{ P }]] e @ E [[{ Φ }]] ∗ (∀ v, [[{ Φ v }]] ev v @ E [[{ Ψ }]]) ⊢
      [[{ P }]] e >>= ev @ E [[{ Ψ }]].
  Context (seq : expr → expr → expr).
  Local Notation "e >> e'" := (seq e e') (at level 80, right associativity).
  Hypothesis thoare_seq : ∀{E e e' P Ψ} Φ,
    [[{ P }]] e @ E [[{ Φ }]] ∗ (∀ v, [[{ Φ v }]] e' @ E [[{ Ψ }]]) ⊢
      [[{ P }]] e >> e' @ E [[{ Ψ }]].
  (** Allocation *)
  Context (ref : val → expr).
  Hypothesis thoare_ref : ∀{E v}, ⊢
    [[{ True }]] ref v @ E [[{ λ w, ∃ l, ⌜w = l⌝ ∗ l ↦ v }]].
  (** Store *)
  Context (store : loc → val → expr).
  Local Notation "l <- v" := (store l v) (at level 20).
  Hypothesis atomic_store : ∀{l v}, atomic (l <- v).
  Hypothesis thoare_store : ∀{E l v w}, ⊢
    [[{ l ↦ v }]] l <- w @ E [[{ λ _, l ↦ w }]].
  (** Load *)
  Context (load : loc → expr).
  Local Notation "! l" := (load l) (at level 20).
  Hypothesis atomic_load : ∀{l}, atomic (!l).
  Hypothesis thoare_load : ∀{E l v}, ⊢
    [[{ l ↦ v }]] !l @ E [[{ λ v', ⌜v' = v⌝ ∗ l ↦ v }]].
  (** Function call *)
  Context (call : expr_val).
  Hypothesis thoare_call : ∀{E e P Ψ},
    [[{ P }]] e @ E [[{ Ψ }]] ⊢ [[{ P }]] call (λ(), e) @ E [[{ Ψ }]].

  (** Termination of [call] *)
  Definition termin_call f : PROP :=
    [[{ True }]] call f @ ⊤ [[{ λ _, True }]].
  (** Bad proposition with an unguarded total Hoare triple *)
  Definition bad l : PROP := ∃ f, l ↦ f ∗ termin_call f.

  (** Later-free invariant on the bad proposition *)
  Context (inv_bad : loc → PROP).
  Hypothesis inv_bad_persistent : ∀{l}, Persistent (inv_bad l).
  Hypothesis thoare_inv_bad_alloc : ∀{l e P Ψ},
    [[{ inv_bad l ∗ P }]] e @ ⊤ [[{ Ψ }]] ⊢ [[{ bad l ∗ P }]] e @ ⊤ [[{ Ψ }]].
  Hypothesis thoare_inv_bad_acc : ∀{l e P Ψ}, atomic e →
    [[{ bad l ∗ P }]] e @ ∅ [[{ λ v, bad l ∗ Ψ v }]] ⊢
      [[{ inv_bad l ∗ P }]] e @ ⊤ [[{ Ψ }]].

  (** Bad call *)
  Definition badcall l := !l >>= call.
  (** Bad function value *)
  Definition badfun l := λ(), badcall l.

  (** Landin's knot *)
  Definition landin_body l := l <- badfun l >> badcall l.
  Context (landin_body' : expr_val).
  Hypothesis landin_body_subst : ∀{l}, landin_body l = landin_body' l.
  Definition landin := ref (λ(), nop) >>= landin_body'.

  (** [badcall] terminates under [inv_bad] *)
  Lemma thoare_badcall {l} : ⊢
    [[{ inv_bad l }]] badcall l @ ⊤ [[{ λ _, True }]].
  Proof.
    iApply (thoare_bind termin_call). iSplit; last first.
    { iIntros (f). iApply thoare_self. }
    iApply (thoare_pre (inv_bad l ∗ True)); [by iIntros "$"|].
    iApply thoare_inv_bad_acc; [by apply atomic_load|].
    iApply (thoare_pre (bad l)); [by iIntros "[$ _]"|]. iApply thoare_exists.
    iIntros (f).
    iApply thoare_post; [|iApply thoare_frame; by iApply thoare_load].
    iIntros (?) "[[-> $]#?]". by iSplit.
  Qed.

  (** Landin's knot is shown to terminate, which is contradictory because it
    actually loops infinitely in the expected operational semantics *)
  Lemma thoare_landin : ⊢ [[{ True }]] landin @ ⊤ [[{ λ _, True }]].
  Proof.
    iApply thoare_bind. iSplit; [iApply thoare_ref|]. iIntros (?).
    iApply thoare_exists. iIntros (l). iApply thoare_pure. iIntros (->).
    rewrite -landin_body_subst. iApply (thoare_pre (bad l)).
    { iIntros "$". iApply thoare_call. iApply thoare_nop. }
    iApply (thoare_pre (bad l ∗ True)); [by iIntros "$"|].
    iApply thoare_inv_bad_alloc. iApply thoare_seq.
    iSplit; [|iIntros (?); iApply thoare_badcall].
    iApply (thoare_pre (inv_bad l ∗ inv_bad l)); [iIntros "[#? _]"; by iSplit|].
    iApply thoare_inv_bad_acc; [by apply atomic_store|].
    iApply (thoare_pre (∃ f, l ↦ f ∗ inv_bad l)); [by iIntros "[[%[$ _]]$]"|].
    iApply thoare_exists. iIntros (g).
    iApply thoare_post; [|iApply thoare_frame; by iApply thoare_store].
    iIntros (?) "[$ #i]". iSplit; [|done]. iApply thoare_call.
    iApply (thoare_apply (inv_bad l)). iSplit; [done|].
    iApply thoare_badcall.
  Qed.
End inv_landin. End inv_landin.
