(** * Lifetime machinery *)

From nola Require Export prelude.
From iris.algebra Require Import csum frac.
From iris.bi Require Import fractional.
From iris.base_logic Require Import lib.invariants.
From iris.proofmode Require Import proofmode.

(** ** Lifetime *)

(** Atomic lifetime *)
Local Definition alft := positive.
(** Lifetime *)
Notation lft := (gmultiset alft).
Implicit Type α β : lft.

(** Static lifetime [⊤], empty [∅] as a multiset *)
#[export] Instance lft_top : Top lft := ∅ : gmultiset _.
(** Lifetime meet [⊓], sum [⊎] as a multiset *)
#[export] Instance lft_meet : Meet lft := disj_union.

(** [⊓] is unital over [⊤], commutative, and associative *)
Fact lft_meet_id_l : LeftId (=) ⊤ (meet (A:=lft)).
Proof. apply _. Qed.
Fact lft_meet_id_r : RightId (=) ⊤ (meet (A:=lft)).
Proof. apply _. Qed.
Fact lft_meet_comm : Comm (=) (meet (A:=lft)).
Proof. apply _. Qed.
Fact lft_meet_assoc : Assoc (=) (meet (A:=lft)).
Proof. apply _. Qed.

(** ** Ghost state *)

(** Algebra for an atomic lifetime *)
Definition lftR := csumR
  fracR (* Alive, fractionally owned *)
  unitR (* Dead *).

(** Ghost state *)
Class lftG Σ := LftG { lftG_inG : inG Σ lftR }.
Local Existing Instance lftG_inG.
Definition lftΣ : gFunctors := GFunctor lftR.
#[export] Instance subG_lft `{!subG lftΣ Σ} : lftG Σ.
Proof. solve_inG. Qed.

(** ** Lifetime tokens *)

(** Atomic lifetime token *)
Local Definition alft_tok `{!lftG Σ} (a : alft) (q : Qp) : iProp Σ :=
  own a (Cinl q).
(** Lifetime token *)
Notation lft_tok α q := ([∗ mset] a ∈ α, alft_tok a q)%I.
Notation "q .[ α ]" := (lft_tok α q)
  (format "q .[ α ]", at level 2, left associativity) : bi_scope.

(** Dead atomic lifetime token *)
Local Definition alft_dead `{!lftG Σ} (a : alft) : iProp Σ := own a (Cinr ()).
(** Dead lifetime token *)
Definition lft_dead `{!lftG Σ} (α : lft) : iProp Σ :=
  ∃ a, ⌜a ∈ α⌝ ∗ alft_dead a.
Notation "[† α ]" := (lft_dead α) (format "[† α ]") : bi_scope.

Section lft.
  Context `{!lftG Σ}.

  (** Dead lifetime token is persistent *)
  Fact lft_dead_persistent {α} : Persistent [†α].
  Proof. apply _. Qed.

  (** Lifetime and dead lifetime tokens are timeless *)
  Fact lft_tok_timeless {α q} : Timeless q.[α].
  Proof. apply _. Qed.
  Fact lft_dead_timeless {α} : Timeless [†α].
  Proof. apply _. Qed.

  (** Lifetime and dead lifetime tokens can't coexist *)
  Lemma lft_tok_dead {α q} : q.[α] -∗ [†α] -∗ False.
  Proof.
    iIntros "q". iDestruct 1 as (a) "[%e †]".
    rewrite big_sepMS_elem_of; [|done].
    by iDestruct (own_valid_2 with "q †") as "%".
  Qed.

  (** Create a full token and a killer for a fresh lifetime *)
  Lemma lft_tok_alloc : ⊢ |==> ∃ α, 1.[α] ∗ ■ (1.[α] ==∗ [†α]).
  Proof.
    iMod (own_alloc (Cinl 1%Qp)) as (a) "a"; [done|]. iExists {[+a+]}.
    rewrite big_sepMS_singleton. iFrame "a". iIntros "!>!> a".
    iMod (own_update _ _ (Cinr ()) with "a") as "†".
    { by apply cmra_update_exclusive. }
    iModIntro. iExists _. iFrame "†". iPureIntro. set_solver.
  Qed.

  (** Lifetime token is fractional *)
  #[export] Instance lft_tok_fract {α} : Fractional (λ q, q.[α])%I.
  Proof.
    move=> ??. rewrite -big_sepMS_sep. apply big_sepMS_proper.
    move=> ??. by rewrite -own_op -Cinl_op.
  Qed.
  #[export] Instance lft_tok_as_fract {α} q :
    AsFractional q.[α] (λ q, q.[α])%I q.
  Proof. split; [done|apply _]. Qed.
  #[export] Instance lft_tok_fract_frame {p α} `{!FrameFractionalQp q r s} :
    Frame p q.[α] r.[α] s.[α] | 5.
  Proof. apply: frame_fractional. Qed.

  (** Lifetime token over [⊤]/[⊓] *)
  Lemma lft_tok_top {q} : ⊢ q.[⊤].
  Proof. by apply big_sepMS_empty'. Qed.
  Lemma lft_tok_meet {q α β} : q.[α ⊓ β] ⊣⊢ q.[α] ∗ q.[β].
  Proof. by apply big_sepMS_disj_union. Qed.

  (** Dead lifetime token over [⊤]/[⊓] *)
  Lemma lft_dead_top : [†⊤] ⊢ False.
  Proof. iDestruct 1 as (?) "[% _]". set_solver. Qed.
  Lemma lft_dead_meet {α β} : [†α ⊓ β] ⊣⊢ [†α] ∨ [†β].
  Proof.
    iSplit.
    - iDestruct 1 as (a) "[%e †]". rewrite gmultiset_elem_of_disj_union in e.
      case e as [?|?]; [iLeft|iRight]; iExists _; by iFrame "†".
    - iDestruct 1 as "[(%a & % & †)|(%a & % & †)]"; iExists _; iFrame "†";
        iPureIntro; set_solver.
  Qed.
End lft.

(** ** Lifetime inclusion *)

(** Namespace for the lifetime machinery *)
Definition lftN : namespace := nroot .@ "lft".

(** Lifetime inclusion, defined semantically *)
Definition lft_incl `{!lftG Σ, !invGS_gen hlc Σ} (α β : lft) : iProp Σ :=
  □ ((∀ q, q.[α] ={↑lftN}=∗ ∃ r, r.[β] ∗ (r.[β] ={↑lftN}=∗ q.[α])) ∧
     ([†β] ={↑lftN}=∗ [†α])).
Infix "⊑" := lft_incl (at level 70) : bi_scope.

Section lft.
  Context `{!lftG Σ, !invGS_gen hlc Σ}.

  (** Lifetime inclusion is persistent *)
  Fact lft_incl_persistent {α β} : Persistent (α ⊑ β).
  Proof. apply _. Qed.

  (** Lifetime inclusion is reflexive, is transitive, has the maximum [⊤] *)
  Lemma lft_incl_refl {α} : ⊢ α ⊑ α.
  Proof.
    iModIntro. iSplit.
    - iIntros (q) "α !>". iExists q. iFrame "α". by iIntros.
    - by iIntros.
  Qed.
  Lemma lft_incl_trans {α β γ} : α ⊑ β -∗ β ⊑ γ -∗ α ⊑ γ.
  Proof.
    iIntros "#[αβα †βα] #[βγβ †γβ] !>". iSplit.
    - iIntros (q) "α". iMod ("αβα" with "α") as (r) "[β βα]".
      iMod ("βγβ" with "β") as (s) "[γ βγ]". iModIntro. iExists s. iFrame "γ".
      iIntros "γ". iMod ("βγ" with "γ") as "β". by iApply "βα".
    - iIntros "†γ". iMod ("†γβ" with "†γ") as "†β". by iApply "†βα".
  Qed.
  Lemma lft_incl_top {α} : ⊢ α ⊑ ⊤.
  Proof.
    iModIntro. iSplit.
    - iIntros (?) "$ !>". iExists 1%Qp. iSplit; by [|iIntros].
    - iDestruct 1 as (?) "[% _]". set_solver.
  Qed.

  (** [⊓] is the lub w.r.t. lifetime inclusion *)
  Lemma lft_incl_meet_l {α β} : ⊢ α ⊓ β ⊑ α.
  Proof.
    iModIntro. iSplit.
    - iIntros (q) "[α $] !>". iExists q. iFrame "α". by iIntros "$".
    - iDestruct 1 as (a) "[% †]". iModIntro. iExists a. iFrame "†".
      iPureIntro. set_solver.
  Qed.
  Lemma lft_incl_meet_r {α β} : ⊢ α ⊓ β ⊑ β.
  Proof. by rewrite comm -lft_incl_meet_l. Qed.
  Lemma lft_incl_meet_intro {α β γ} : α ⊑ β -∗ α ⊑ γ -∗ α ⊑ β ⊓ γ.
  Proof.
    iIntros "#[αβα †βα] #[αγα †γα] !>". iSplit.
    - iIntros (q) "[α α']". iMod ("αβα" with "α") as (r) "[β βα]".
      iMod ("αγα" with "α'") as (s) "[γ γα']". iModIntro.
      case (Qp.lower_bound r s)=> [t[?[?[->->]]]].
      iDestruct "β" as "[β β']". iDestruct "γ" as "[γ γ']". iExists t.
      iFrame "β γ". iIntros "[β γ]". iMod ("βα" with "[$β $β']") as "$".
      by iMod ("γα'" with "[$γ $γ']") as "$".
    - iDestruct 1 as (a) "[%e †]".
      move: e=> /gmultiset_elem_of_disj_union[?|?]; [iApply "†βα"|iApply "†γα"];
        iExists _; by iFrame.
  Qed.

  (** Eternalize a lifetime by consuming a token *)
  Lemma lft_tok_eternalize {α q E} : q.[α] ={E}=∗ ∀ β, β ⊑ α.
  Proof.
    iIntros "α". iMod (inv_alloc lftN _ (∃ q, q.[α]) with "[α]") as "#i".
    { by iExists _. } iIntros "!> %β !>". iSplit.
    - iIntros (?) "$". iInv "i" as (?) ">[α α']". iModIntro. iSplitL "α'".
      { by iExists _. } iModIntro. iExists _. iFrame "α". by iIntros.
    - iIntros "†". iInv "i" as (?) ">[α α']". iModIntro. iSplitL "α'".
      { by iExists _. } iDestruct (lft_tok_dead with "α †") as "[]".
  Qed.
End lft.
