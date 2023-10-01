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

(** ** Pure lifetime inclusion *)

Definition lft_incl (α β : lft) : Prop := ∀ a, a ∈ β → a ∈ α.
#[export] Instance sqsubseteq_lft : SqSubsetEq lft := lft_incl.

(** [⊑] is reflexive, transitive, has the maximum [⊤], has the lub [⊓] *)
Lemma lft_incl_refl {α} : α ⊑ α. Proof. by move=> ?. Qed.
Lemma lft_incl_trans {α β γ} : α ⊑ β → β ⊑ γ → α ⊑ γ. Proof. set_solver. Qed.
Lemma lft_incl_top {α} : α ⊑ ⊤. Proof. set_solver. Qed.
Lemma lft_incl_meet_l {α β} : α ⊓ β ⊑ α. Proof. set_solver. Qed.
Lemma lft_incl_meet_r {α β} : α ⊓ β ⊑ β. Proof. set_solver. Qed.
Lemma lft_incl_meet_intro {α β γ} : α ⊑ β → α ⊑ γ → α ⊑ β ⊓ γ.
Proof. set_solver. Qed.

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
  Local Instance alft_tok_fract {a} : Fractional (alft_tok a)%I.
  Proof. move=> ??. by rewrite -own_op -Cinl_op. Qed.
  Local Instance alft_tok_as_fract {a q} :
    AsFractional (alft_tok a q) (alft_tok a) q.
  Proof. split; [done|apply _]. Qed.
  #[export] Instance lft_tok_fract {α} : Fractional (λ q, q.[α])%I.
  Proof. apply _. Qed.
  #[export] Instance lft_tok_as_fract {α q} :
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
  Lemma lft_dead_meet_l {α β} : [†α] ⊢ [†α ⊓ β].
  Proof. iIntros. rewrite lft_dead_meet. by iLeft. Qed.
  Lemma lft_dead_meet_r {α β} : [†β] ⊢ [†α ⊓ β].
  Proof. iIntros. rewrite lft_dead_meet. by iRight. Qed.

  (** Access a lifetime token using [⊑] *)
  Local Lemma list_incl_tok_acc {α q} bl :
    (∀ a, a ∈ bl → a ∈ α) → q.[α] -∗ ∃ r,
      ([∗ list] b ∈ bl, alft_tok b r) ∗
      (([∗ list] b ∈ bl, alft_tok b r) -∗ q.[α]).
  Proof.
    move: q. elim: bl=> /=[|b bl IH] q inc.
    { iIntros. iExists 1%Qp. iSplit; [done|]. by iFrame. }
    iIntros "[α α']". iDestruct (IH with "α'") as (r) "[bl →α']"; [set_solver|].
    iDestruct (big_sepMS_elem_of_acc _ _ b with "α") as "[b →α]"; [set_solver|].
    case: (Qp.lower_bound r (q/2)%Qp)=> [s[t[t'[->eq]]]].
    have ->: alft_tok b (q / 2) ⊣⊢ alft_tok b s ∗ alft_tok b t'.
    { by rewrite eq fractional. }
    iExists _. iDestruct "b" as "[$ b']". setoid_rewrite fractional.
    rewrite big_sepL_sep. iDestruct "bl" as "[$ bl']". iIntros "[b bl]".
    iDestruct ("→α" with "[$b $b']") as "$". iApply "→α'". iFrame.
  Qed.
  Lemma lft_incl_tok_acc {α β q} :
    α ⊑ β → q.[α] -∗ ∃ r, r.[β] ∗ (r.[β] -∗ q.[α]).
  Proof.
    move=> βα. iIntros "α".
    iDestruct (list_incl_tok_acc (elements β) with "α") as (r) "[bl →α]".
    { move=> ? /gmultiset_elem_of_elements. set_solver. }
    iExists _. rewrite -big_opMS_elements. iFrame.
  Qed.

  (** Access a dead lifetime token using [⊑] *)
  Lemma lft_incl_dead_acc {α β} : α ⊑ β → [†β] -∗ [†α].
  Proof.
    move=> βα. iDestruct 1 as (a) "[%i †]". iExists a. iFrame "†". iPureIntro.
    set_solver.
  Qed.
End lft.

(** ** Semantic lifetime inclusion *)

(** Namespace for the lifetime machinery *)
Definition lftN : namespace := nroot .@ "lft".

(** Semantic lifetime inclusion *)
Section lft.
  Context `{!lftG Σ, !invGS_gen hlc Σ}.
  Definition lft_sincl_def  (α β : lft) : iProp Σ :=
    □ ((∀ q, q.[α] ={↑lftN}=∗ ∃ r, r.[β] ∗ (r.[β] -∗ q.[α])) ∧
      ([†β] ={↑lftN}=∗ [†α])).
  Lemma lft_sincl_aux : seal lft_sincl_def. Proof. by eexists. Qed.
  Definition lft_sincl := lft_sincl_aux.(unseal).
  Lemma lft_sincl_unseal : lft_sincl = lft_sincl_def. Proof. exact: seal_eq. Qed.
End lft.
Infix "⊑s" := lft_sincl (at level 70) : bi_scope.

Section lft.
  Context `{!lftG Σ, !invGS_gen hlc Σ}.

  (** [⊑s] is persistent *)
  Fact lft_sincl_persistent {α β} : Persistent (α ⊑s β).
  Proof. rewrite lft_sincl_unseal. apply _. Qed.

  (** Access a lifetime token by [⊑s] *)
  Lemma lft_sincl_tok_acc {α β q} :
    α ⊑s β -∗ q.[α] ={↑lftN}=∗ ∃ r, r.[β] ∗ (r.[β] -∗ q.[α]).
  Proof. rewrite lft_sincl_unseal. by iIntros "#[? _]". Qed.

  (** Access a dead lifetime token by [⊑s] *)
  Lemma lft_sincl_dead_acc {α β} : α ⊑s β -∗ [†β] ={↑lftN}=∗ [†α].
  Proof. rewrite lft_sincl_unseal. by iIntros "#[_ ?]". Qed.

  (** [⊑] entails [⊑s] *)
  Lemma lft_incl_sincl {α β} : α ⊑ β → ⊢ α ⊑s β.
  Proof.
    move=> βα. rewrite lft_sincl_unseal. iModIntro. iSplit.
    - iIntros "% ? !>". by iApply lft_incl_tok_acc.
    - iIntros "? !>". by iApply lft_incl_dead_acc.
  Qed.

  (** [⊑s] is reflexive, is transitive, has the maximum [⊤] *)
  Lemma lft_sincl_refl {α} : ⊢ α ⊑s α.
  Proof.
    rewrite lft_sincl_unseal. iModIntro. iSplit; [|by iIntros].
    iIntros (q) "α !>". iExists q. iFrame "α". by iIntros.
  Qed.
  Lemma lft_sincl_trans {α β γ} : α ⊑s β -∗ β ⊑s γ -∗ α ⊑s γ.
  Proof.
    rewrite lft_sincl_unseal. iIntros "#[αβα †βα] #[βγβ †γβ] !>". iSplit.
    - iIntros "%q α". iMod ("αβα" with "α") as (r) "[β βα]".
      iMod ("βγβ" with "β") as (s) "[γ βγ]". iModIntro. iExists s. iFrame "γ".
      iIntros "γ". iDestruct ("βγ" with "γ") as "β". by iApply "βα".
    - iIntros "†γ". iMod ("†γβ" with "†γ") as "†β". by iApply "†βα".
  Qed.
  Lemma lft_sincl_top {α} : ⊢ α ⊑s ⊤.
  Proof. apply lft_incl_sincl, lft_incl_top. Qed.

  (** A dead lifetime is the minimum w.r.t. [⊑s] *)
  Lemma lft_sincl_dead {α} : [†α] ⊢ ∀ β, α ⊑s β.
  Proof.
    rewrite lft_sincl_unseal. iIntros "#† %β !>". iSplit; [|by iIntros].
    iIntros (?) "α". iDestruct (lft_tok_dead with "α †") as "[]".
  Qed.

  (** [⊓] is the lub w.r.t. [⊑s] *)
  Lemma lft_sincl_meet_l {α β} : ⊢ α ⊓ β ⊑s α.
  Proof. apply lft_incl_sincl, lft_incl_meet_l. Qed.
  Lemma lft_sincl_meet_r {α β} : ⊢ α ⊓ β ⊑s β.
  Proof. apply lft_incl_sincl, lft_incl_meet_r. Qed.
  Lemma lft_sincl_meet_intro {α β γ} : α ⊑s β -∗ α ⊑s γ -∗ α ⊑s β ⊓ γ.
  Proof.
    rewrite lft_sincl_unseal. iIntros "#[αβα †βα] #[αγα †γα] !>".
    iSplit; last first.
    { rewrite lft_dead_meet. iIntros "[?|?]"; by [iApply "†βα"|iApply "†γα"]. }
    iIntros (q) "[α α']". iMod ("αβα" with "α") as (r) "[β βα]".
    iMod ("αγα" with "α'") as (s) "[γ γα']". iModIntro.
    case (Qp.lower_bound r s)=> [t[?[?[->->]]]].
    iDestruct "β" as "[β β']". iDestruct "γ" as "[γ γ']". iExists t.
    iFrame "β γ". iIntros "[β γ]". iDestruct ("βα" with "[$β $β']") as "$".
    iApply ("γα'" with "[$γ $γ']").
  Qed.

  (** Eternalize a lifetime by consuming a token *)
  Lemma lft_tok_eternalize {α q E} : q.[α] ={E}=∗ ∀ β, β ⊑s α.
  Proof.
    rewrite lft_sincl_unseal. iIntros "α".
    iMod (inv_alloc lftN _ (∃ q, q.[α]) with "[α]") as "#i".
    { by iExists _. } iIntros "!> %β !>". iSplit.
    - iIntros (?) "$". iInv "i" as (?) ">[α α']". iModIntro. iSplitL "α'".
      { by iExists _. } iModIntro. iExists _. iFrame "α". by iIntros.
    - iIntros "†". iInv "i" as (?) ">[α α']". iModIntro. iSplitL "α'".
      { by iExists _. } iDestruct (lft_tok_dead with "α †") as "[]".
  Qed.
End lft.
