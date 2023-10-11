(** * Lifetime machinery *)

From nola Require Export prelude.
From nola.iris Require Import dfrac.
From iris.algebra Require Import csum dfrac.
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
Proof. exact _. Qed.
Fact lft_meet_id_r : RightId (=) ⊤ (meet (A:=lft)).
Proof. exact _. Qed.
Fact lft_meet_comm : Comm (=) (meet (A:=lft)).
Proof. exact _. Qed.
Fact lft_meet_assoc : Assoc (=) (meet (A:=lft)).
Proof. exact _. Qed.

(** ** Ghost state *)

(** Algebra for an atomic lifetime *)
Definition lftR := csumR
  dfracR (* Alive, fractionally owned *)
  unitR (* Dead *).

(** Ghost state *)
Class lftG Σ := lftG_inG : inG Σ lftR.
Local Existing Instance lftG_inG.
Definition lftΣ : gFunctors := GFunctor lftR.
#[export] Instance subG_lft `{!subG lftΣ Σ} : lftG Σ.
Proof. solve_inG. Qed.

(** ** Pure lifetime inclusion, as reverse set inclusion *)
Definition lft_incl (α β : lft) : Prop := elements β ⊆ elements α.
#[export] Instance sqsubseteq_lft : SqSubsetEq lft := lft_incl.

(** Unfold [⊑] *)
Lemma lft_incl_unfold {α β} : α ⊑ β ↔ elements β ⊆ elements α.
Proof. done. Qed.

(** [⊑] is decidable *)
#[export] Instance lft_incl_dec : RelDecision (⊑@{lft}) :=
  λ α β, decide (elements β ⊆ elements α).

(** [⊑] is reflexive, transitive, has the maximum [⊤], has the lub [⊓] *)
#[export] Instance lft_incl_refl : Reflexive (⊑@{lft}).
Proof. by move=> ??. Qed.
#[export] Instance lft_incl_trans : Transitive (⊑@{lft}).
Proof. move=> ???. set_solver. Qed.
Lemma lft_incl_top {α} : α ⊑ ⊤. Proof. apply list_subseteq_nil. Qed.
Lemma lft_incl_meet_l {α β} : α ⊓ β ⊑ α.
Proof. rewrite lft_incl_unfold gmultiset_elements_disj_union. set_solver. Qed.
Lemma lft_incl_meet_r {α β} : α ⊓ β ⊑ β.
Proof. rewrite lft_incl_unfold gmultiset_elements_disj_union. set_solver. Qed.
Lemma lft_incl_meet_intro {α β γ} : α ⊑ β → α ⊑ γ → α ⊑ β ⊓ γ.
Proof. rewrite !lft_incl_unfold gmultiset_elements_disj_union. set_solver. Qed.
Lemma lft_incl_meet_mono_l {α α' β} : α ⊑ α' → α ⊓ β ⊑ α' ⊓ β.
Proof. rewrite !lft_incl_unfold !gmultiset_elements_disj_union. set_solver. Qed.
Lemma lft_incl_meet_mono_r {α β β'} : β ⊑ β' → α ⊓ β ⊑ α ⊓ β'.
Proof. rewrite !lft_incl_unfold !gmultiset_elements_disj_union. set_solver. Qed.

(** ** Lifetime tokens *)

(** Atomic lifetime token *)
Local Definition alft_tok `{!lftG Σ} (a : alft) (q : Qp) : iProp Σ :=
  own a (Cinl (DfracOwn q)).
(** Lifetime token *)
Notation lft_tok α q := ([∗ mset] a ∈ α, alft_tok a q)%I.
Notation "q .[ α ]" := (lft_tok α q)
  (format "q .[ α ]", at level 2, left associativity) : bi_scope.

(** Dead atomic lifetime token *)
Local Definition alft_dead `{!lftG Σ} (a : alft) : iProp Σ := own a (Cinr ()).
(** Dead lifetime token *)
Local Definition lft_dead_def `{!lftG Σ} (α : lft) : iProp Σ :=
  ∃ a, ⌜a ∈ α⌝ ∗ alft_dead a.
Local Lemma lft_dead_aux : seal (@lft_dead_def). Proof. by eexists. Qed.
Definition lft_dead `{!lftG Σ} := lft_dead_aux.(unseal) _ _.
Local Lemma lft_dead_unseal `{!lftG Σ} : @lft_dead = @lft_dead_def.
Proof. exact: seal_eq. Qed.
Notation "[† α ]" := (lft_dead α) (format "[† α ]") : bi_scope.

(** Eternal atomic lifetime token *)
Local Definition alft_eter `{!lftG Σ} (a : alft) : iProp Σ :=
  own a (Cinl DfracDiscarded).
(** Eternal lifetime token *)
Notation lft_eter α := ([∗ mset] a ∈ α, alft_eter a)%I.
Notation "[∞ α ]" := (lft_eter α) (format "[∞ α ]") : bi_scope.

Section lft.
  Context `{!lftG Σ}.

  (** Dead and eternal lifetime tokens are persistent *)
  #[export] Instance lft_dead_persistent {α} : Persistent [†α].
  Proof. rewrite lft_dead_unseal. exact _. Qed.
  Fact lft_eter_persistent {α} : Persistent [∞α].
  Proof. exact _. Qed.

  (** Lifetime, dead, eternal lifetime tokens are timeless *)
  Fact lft_tok_timeless {α q} : Timeless q.[α].
  Proof. exact _. Qed.
  #[export] Instance lft_dead_timeless {α} : Timeless [†α].
  Proof. rewrite lft_dead_unseal. exact _. Qed.
  Fact lft_eter_timeless {α} : Timeless [∞α].
  Proof. exact _. Qed.

  (** Lifetime and dead lifetime tokens can't coexist *)
  Lemma lft_tok_dead {α q} : q.[α] -∗ [†α] -∗ False.
  Proof.
    rewrite lft_dead_unseal. iIntros "q". iDestruct 1 as (a) "[%e †]".
    rewrite big_sepMS_elem_of; [|done].
    by iDestruct (own_valid_2 with "q †") as "%".
  Qed.
  (** Eternal and dead lifetime tokens can't coexist *)
  Lemma lft_eter_dead {α} : [∞α] -∗ [†α] -∗ False.
  Proof.
    rewrite lft_dead_unseal. iIntros "∞". iDestruct 1 as (a) "[%e †]".
    rewrite big_sepMS_elem_of; [|done].
    by iDestruct (own_valid_2 with "∞ †") as "%".
  Qed.

  (** Lifetime token is fractional *)
  Local Instance alft_tok_fract {a} : Fractional (alft_tok a)%I.
  Proof. move=> ??. by rewrite -own_op -Cinl_op. Qed.
  Local Instance alft_tok_as_fract {a q} :
    AsFractional (alft_tok a q) (alft_tok a) q.
  Proof. split; [done|exact _]. Qed.
  #[export] Instance lft_tok_fract {α} : Fractional (λ q, q.[α])%I.
  Proof. exact _. Qed.
  #[export] Instance lft_tok_as_fract {α q} :
    AsFractional q.[α] (λ q, q.[α])%I q.
  Proof. split; [done|exact _]. Qed.
  #[export] Instance lft_tok_fract_frame {p α} `{!FrameFractionalQp q r s} :
    Frame p q.[α] r.[α] s.[α] | 5.
  Proof. apply: frame_fractional. Qed.

  (** Create a full token and a killer for a fresh lifetime *)
  Lemma lft_tok_alloc : ⊢ |==> ∃ α, 1.[α] ∗ ■ (1.[α] ==∗ [†α]).
  Proof.
    iMod (own_alloc (Cinl (DfracOwn 1))) as (a) "a"; [done|]. iExists {[+a+]}.
    rewrite big_sepMS_singleton. iFrame "a". iIntros "!>!> a".
    iMod (own_update _ _ (Cinr ()) with "a") as "†".
    { by apply cmra_update_exclusive. }
    iModIntro. rewrite lft_dead_unseal. iExists _. iFrame "†". iPureIntro.
    set_solver.
  Qed.

  (** Eternalize a lifetime *)
  Local Lemma alft_eternalize {a q} : alft_tok a q ==∗ alft_eter a.
  Proof.
    iIntros "a". iApply (own_update with "a").
    apply csum_update_l, dfrac_discard_update.
  Qed.
  Lemma lft_eternalize {α q} : q.[α] ==∗ [∞α].
  Proof.
    rewrite -big_sepMS_bupd. iApply big_sepMS_mono=> ? _.
    iApply alft_eternalize.
  Qed.

  (** Get a lifetime token out of an eternal lifetime token *)
  Local Lemma alft_eter_tok {a} : alft_eter a ==∗ ∃ q, alft_tok a q.
  Proof.
    iIntros "∞".
    iMod (own_updateP (λ a, ∃ q, a = Cinl (DfracOwn q)) with "∞") as
      (q[?->]) "?"; [|by iExists _].
    eapply csum_updateP_l; [exact dfrac_restore_update|]=>/= ?[?->].
    by eexists _.
  Qed.
  Local Lemma alftl_eter_tok {al} :
    ([∗ list] a ∈ al, alft_eter a) ==∗ ∃ q, [∗ list] a ∈ al, alft_tok a q.
  Proof.
    elim: al=> [|a al IH]/=; [iIntros "_"; by iExists 1%Qp|].
    iIntros "[∞ al]". iMod (alft_eter_tok with "∞") as (q) "a".
    iMod (IH with "al") as (r) "al". iModIntro.
    case: (Qp.lower_bound q r)=> [s[t[t'[->->]]]].
    iExists s. iDestruct "a" as "[$ _]". iStopProof. do 3 f_equiv.
    iDestruct 1 as "[$ ?]".
  Qed.
  Lemma lft_eter_tok {α} : [∞α] ==∗ ∃ q, q.[α].
  Proof. setoid_rewrite big_opMS_elements. apply alftl_eter_tok. Qed.

  (** Lifetime token over [⊤]/[⊓] *)
  Lemma lft_tok_top {q} : ⊢ q.[⊤].
  Proof. by apply big_sepMS_empty'. Qed.
  Lemma lft_tok_meet {q α β} : q.[α ⊓ β] ⊣⊢ q.[α] ∗ q.[β].
  Proof. by apply big_sepMS_disj_union. Qed.

  (** Dead lifetime token over [⊤]/[⊓] *)
  Lemma lft_dead_top : [†⊤] ⊢ False.
  Proof. rewrite lft_dead_unseal. iDestruct 1 as (?) "[% _]". set_solver. Qed.
  Lemma lft_dead_meet {α β} : [†α ⊓ β] ⊣⊢ [†α] ∨ [†β].
  Proof.
    rewrite lft_dead_unseal. iSplit.
    - iDestruct 1 as (a) "[%e †]". rewrite gmultiset_elem_of_disj_union in e.
      case e as [?|?]; [iLeft|iRight]; iExists _; by iFrame "†".
    - iDestruct 1 as "[(%a & % & †)|(%a & % & †)]"; iExists _; iFrame "†";
        iPureIntro; set_solver.
  Qed.
  Lemma lft_dead_meet_l {α β} : [†α] ⊢ [†α ⊓ β].
  Proof. iIntros. rewrite lft_dead_meet. by iLeft. Qed.
  Lemma lft_dead_meet_r {α β} : [†β] ⊢ [†α ⊓ β].
  Proof. iIntros. rewrite lft_dead_meet. by iRight. Qed.

  (** Eternal lifetime token over [⊤]/[⊓] *)
  Lemma lft_eter_top : ⊢ [∞⊤].
  Proof. by apply big_sepMS_empty'. Qed.
  Lemma lft_eter_meet {α β} : [∞α ⊓ β] ⊣⊢ [∞α] ∗ [∞β].
  Proof. by apply big_sepMS_disj_union. Qed.

  (** Access a lifetime token using [⊑] *)
  Local Lemma alftl_incl_tok_acc {α q} bl : bl ⊆ elements α →
    q.[α] ⊢ ∃ r, ([∗ list] b ∈ bl, alft_tok b r) ∗
      (([∗ list] b ∈ bl, alft_tok b r) -∗ q.[α]).
  Proof.
    move: q. elim: bl=> /=[|b bl IH] q inc.
    { iIntros. iExists 1%Qp. iSplit; [done|]. by iFrame. }
    iIntros "[α α']". iDestruct (IH with "α'") as (r) "[bl →α']"; [set_solver|].
    iDestruct (big_sepMS_elem_of_acc _ _ b with "α") as "[b →α]".
    { rewrite -gmultiset_elem_of_elements. set_solver. }
    case: (Qp.lower_bound r (q/2)%Qp)=> [s[t[t'[->eq]]]].
    have -> : alft_tok b (q / 2) ⊣⊢ alft_tok b s ∗ alft_tok b t'.
    { by rewrite eq fractional. }
    iExists _. iDestruct "b" as "[$ b']". setoid_rewrite fractional.
    rewrite big_sepL_sep. iDestruct "bl" as "[$ bl']". iIntros "[b bl]".
    iDestruct ("→α" with "[$b $b']") as "$". iApply "→α'". iFrame.
  Qed.
  Lemma lft_incl_tok_acc {α β q} :
    α ⊑ β → q.[α] ⊢ ∃ r, r.[β] ∗ (r.[β] -∗ q.[α]).
  Proof.
    move=> βα. iIntros "α".
    iDestruct (alftl_incl_tok_acc (elements β) with "α") as (r) "[bl →α]";
      [done|]. iExists _. rewrite -big_opMS_elements. iFrame.
  Qed.

  (** Modify a dead lifetime token using [⊑] *)
  Lemma lft_incl_dead {α β} : α ⊑ β → [†β] ⊢ [†α].
  Proof.
    rewrite lft_dead_unseal=> ?. iDestruct 1 as (a) "[%aβ †]". iExists a.
    iFrame "†". iPureIntro. move: aβ. rewrite -!gmultiset_elem_of_elements. set_solver.
  Qed.
  #[export] Instance lft_dead_mono : Proper (flip (⊑) ==> (⊢)) (λ α, [†α])%I.
  Proof. move=> >. exact lft_incl_dead. Qed.
  #[export] Instance lft_dead_mono' : Proper ((⊑) ==> flip (⊢)) (λ α, [†α])%I.
  Proof. solve_proper. Qed.

  (** Modify an eternal lifetime token using [⊑] *)
  Lemma lft_incl_eter {α β} : α ⊑ β → [∞α] ⊢ [∞β].
  Proof.
    rewrite !big_opMS_elements=> αβ. iIntros "α". iApply big_sepL_forall.
    iIntros (?? eq). apply elem_of_list_lookup_2 in eq.
    rewrite big_sepL_elem_of; [done|]. by apply αβ.
  Qed.
  #[export] Instance lft_eter_mono : Proper ((⊑) ==> (⊢)) (λ α, [∞α])%I.
  Proof. move=> >. exact lft_incl_eter. Qed.
  #[export] Instance lft_eter_mono' :
    Proper (flip (⊑) ==> flip (⊢)) (λ α, [∞α])%I.
  Proof. solve_proper. Qed.
End lft.

(** ** Persistent lifetime inclusion *)

Section lft.
  Context `{!lftG Σ}.
  Local Definition lft_sincl_def (α β : lft) : iProp Σ :=
    [†α] ∨ ∃ γ, ⌜α ⊓ γ ⊑ β⌝ ∗ [∞γ].
  Lemma lft_sincl_aux : seal lft_sincl_def. Proof. by eexists. Qed.
  Local Definition lft_sincl := lft_sincl_aux.(unseal).
  Local Lemma lft_sincl_unseal : lft_sincl = lft_sincl_def.
  Proof. exact: seal_eq. Qed.
End lft.
Infix "⊑□" := lft_sincl (at level 70) : bi_scope.

Section lft.
  Context `{!lftG Σ}.

  (** [⊑□] is persistent and timeless *)
  #[export] Instance lft_sincl_persistent {α β} : Persistent (α ⊑□ β).
  Proof. rewrite lft_sincl_unseal. exact _. Qed.
  #[export] Instance lft_sincl_timeless {α β} : Timeless (α ⊑□ β).
  Proof. rewrite lft_sincl_unseal. exact _. Qed.

  (** Access a lifetime token by [⊑□] *)
  Lemma lft_sincl_tok_acc {α β q} :
    α ⊑□ β -∗ q.[α] ==∗ ∃ r, r.[β] ∗ (r.[β] -∗ q.[α]).
  Proof.
    rewrite lft_sincl_unseal. iIntros "[†|[%[% γ]]] α".
    { iDestruct (lft_tok_dead with "α †") as "[]". }
    iMod (lft_eter_tok with "γ") as (r) "γ". iModIntro.
    case: (Qp.lower_bound q r)=> [s[t[t'[->->]]]].  iDestruct "α" as "[α α']".
    iDestruct "γ" as "[γ _]". iCombine "α γ" as "αγ". rewrite -lft_tok_meet.
    iDestruct (lft_incl_tok_acc with "αγ") as (?) "[β →α]"; [done|].
    iExists _. iFrame "β". iIntros "β". by iDestruct ("→α" with "β") as "[$_]".
  Qed.

  (** Modify a dead lifetime token by [⊑□] *)
  Lemma lft_sincl_dead {α β} : α ⊑□ β ⊢ [†β] -∗ [†α].
  Proof.
    rewrite lft_sincl_unseal. iIntros "[$|[%[% γ]]] †"; [done|].
    rewrite lft_incl_dead; [|done]. rewrite lft_dead_meet.
    iDestruct "†" as "[$|†]". iDestruct (lft_eter_dead with "γ †") as "[]".
  Qed.

  (** Modify an eternal lifetime token using [⊑□] *)
  Lemma lft_sincl_eter {α β} : α ⊑□ β ⊢ [∞α] -∗ [∞β].
  Proof.
    rewrite lft_sincl_unseal. iIntros "[†|[%γ[%inc γ]]] α".
    { iDestruct (lft_eter_dead with "α †") as "[]". }
    iApply lft_incl_eter; [done|]. by iSplit.
  Qed.

  (** [⊑] entails [⊑□] *)
  Lemma lft_incl_sincl {α β} : α ⊑ β → ⊢ α ⊑□ β.
  Proof.
    rewrite lft_sincl_unseal=> ?. iRight. iExists ⊤.
    iSplit; [|by iApply lft_eter_top]. iPureIntro. by rewrite right_id.
  Qed.

  (** [⊑□] is reflexive, is transitive, has the maximum [⊤] *)
  Lemma lft_sincl_refl {α} : ⊢ α ⊑□ α.
  Proof. by apply lft_incl_sincl. Qed.
  Lemma lft_sincl_trans {α β γ} : α ⊑□ β -∗ β ⊑□ γ -∗ α ⊑□ γ.
  Proof.
    rewrite lft_sincl_unseal. iIntros "[$|[%δ[% δ]]]"; [by iIntros|].
    iIntros "[†|[%δ'[% δ']]]".
    { iLeft. rewrite lft_incl_dead; [|done]. rewrite lft_dead_meet.
      iDestruct "†" as "[$|†]". iDestruct (lft_eter_dead with "δ †") as "[]". }
    iRight. iExists (δ ⊓ δ'). iFrame "δ δ'". iPureIntro. etrans; [|done].
    rewrite assoc. by apply lft_incl_meet_mono_l.
  Qed.
  Lemma lft_sincl_top {α} : ⊢ α ⊑□ ⊤.
  Proof. apply lft_incl_sincl, lft_incl_top. Qed.

  (** A dead lifetime is the minimum w.r.t. [⊑□] *)
  Lemma lft_sincl_by_dead {α} : [†α] ⊢ ∀ β, α ⊑□ β.
  Proof. rewrite lft_sincl_unseal. by iIntros "$". Qed.

  (** An eternal lifetime is the maximum w.r.t. [⊑□] *)
  Lemma lft_sincl_by_eter {α} : [∞α] ⊢ ∀ β, β ⊑□ α.
  Proof.
    rewrite lft_sincl_unseal. iIntros "#∞ %β". iRight. iExists _. iFrame "∞".
    iPureIntro. exact lft_incl_meet_r.
  Qed.
  Lemma lft_eternalize_sincl {α q} : q.[α] ==∗ ∀ β, β ⊑□ α.
  Proof. rewrite -lft_sincl_by_eter. apply lft_eternalize. Qed.

  (** [⊓] is the lub w.r.t. [⊑□] *)
  Lemma lft_sincl_meet_l {α β} : ⊢ α ⊓ β ⊑□ α.
  Proof. apply lft_incl_sincl, lft_incl_meet_l. Qed.
  Lemma lft_sincl_meet_r {α β} : ⊢ α ⊓ β ⊑□ β.
  Proof. apply lft_incl_sincl, lft_incl_meet_r. Qed.
  Lemma lft_sincl_meet_intro {α β γ} : α ⊑□ β -∗ α ⊑□ γ -∗ α ⊑□ β ⊓ γ.
  Proof.
    rewrite lft_sincl_unseal. iIntros "[$|[%δ[%iβ δ]]]"; [by iIntros|].
    iIntros "[$|[%δ'[%iγ δ']]]". iRight. iExists (δ ⊓ δ'). iFrame "δ δ'".
    iPureIntro. move: iβ iγ.
    rewrite !lft_incl_unfold !gmultiset_elements_disj_union. set_solver.
  Qed.
  Lemma lft_sincl_meet_mono_l {α α' β} : α ⊑□ α' ⊢ α ⊓ β ⊑□ α' ⊓ β.
  Proof.
    iIntros "#?". iApply lft_sincl_meet_intro; [|by iApply lft_sincl_meet_r].
    iApply lft_sincl_trans; [|done]. iApply lft_sincl_meet_l.
  Qed.
  Lemma lft_sincl_meet_mono_r {α β β'} : β ⊑□ β' ⊢ α ⊓ β ⊑□ α ⊓ β'.
  Proof. rewrite comm [α ⊓ β']comm. exact lft_sincl_meet_mono_l. Qed.
End lft.
