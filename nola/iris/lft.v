(** * Lifetime machinery *)

From nola Require Export prelude.
From nola.util Require Import set.
From nola.bi Require Export updw.
From nola.bi Require Import gen_upd.
From iris.algebra Require Import view gmap csum dfrac.
From iris.bi Require Import fractional.
From iris.base_logic.lib Require Export own.
From iris.proofmode Require Import proofmode.
Import UpdwNotation.

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
Fact lft_meet_id_l : LeftId (=) ⊤ (meet (A:=lft)). Proof. exact _. Qed.
Fact lft_meet_id_r : RightId (=) ⊤ (meet (A:=lft)). Proof. exact _. Qed.
Fact lft_meet_comm : Comm (=) (meet (A:=lft)). Proof. exact _. Qed.
Fact lft_meet_assoc : Assoc (=) (meet (A:=lft)). Proof. exact _. Qed.

(** [= ⊤] and [⊓] *)
Lemma lft_eqtop_meet_l {α β} : α ⊓ β = ⊤ → α = ⊤.
Proof. rewrite -!gmultiset_size_empty_iff gmultiset_size_disj_union. lia. Qed.
Lemma lft_eqtop_meet_r {α β} : α ⊓ β = ⊤ → β = ⊤.
Proof. rewrite [_ ⊓ _]comm. exact lft_eqtop_meet_l. Qed.
Lemma lft_neqtop_meet_l {α β} : α ≠ ⊤ → α ⊓ β ≠ ⊤.
Proof. by move=> ? /lft_eqtop_meet_l. Qed.
Lemma lft_neqtop_meet_r {α β} : β ≠ ⊤ → α ⊓ β ≠ ⊤.
Proof. by move=> ? /lft_eqtop_meet_r. Qed.

(** ** [⊑]: Pure lifetime inclusion *)

(** Pure lifetime inclusion, as reverse multiset inclusion *)
Definition lft_incl (α β : lft) : Prop := dom β ⊆ dom α.
#[export] Instance sqsubseteq_lft : SqSubsetEq lft := lft_incl.

(** [⊑] in terms of [∈] *)
Local Lemma lft_incl_elem_of_dom {α β} : (α ⊑ β) = (∀ a, a ∈ dom β → a ∈ dom α).
Proof. done. Qed.
Local Lemma lft_incl_elem_of {α β} : (α ⊑ β) ↔ (∀ a, a ∈ β → a ∈ α).
Proof.
  rewrite lft_incl_elem_of_dom. by setoid_rewrite gmultiset_elem_of_dom.
Qed.

(** [⊑] is decidable *)
#[export] Instance lft_incl_dec : RelDecision (⊑@{lft}) :=
  λ α β, decide (dom β ⊆ dom α).

(** [⊑] is reflexive, transitive, has the maximum [⊤], has the lub [⊓] *)
#[export] Instance lft_incl_refl : Reflexive (⊑@{lft}).
Proof. by move=> ??. Qed.
#[export] Instance lft_incl_trans : Transitive (⊑@{lft}).
Proof. move=> ???. set_solver. Qed.
Lemma lft_incl_top {α} : α ⊑ ⊤. Proof. done. Qed.
Lemma lft_incl_meet_l {α β} : α ⊓ β ⊑ α.
Proof. rewrite lft_incl_elem_of. set_solver. Qed.
Lemma lft_incl_meet_r {α β} : α ⊓ β ⊑ β.
Proof. rewrite lft_incl_elem_of. set_solver. Qed.
Lemma lft_incl_meet_intro {α β γ} : α ⊑ β → α ⊑ γ → α ⊑ β ⊓ γ.
Proof. rewrite !lft_incl_elem_of. set_solver. Qed.
Lemma lft_incl_meet_mono_l {α α' β} : α ⊑ α' → α ⊓ β ⊑ α' ⊓ β.
Proof. rewrite !lft_incl_elem_of. set_solver. Qed.
Lemma lft_incl_meet_mono_r {α β β'} : β ⊑ β' → α ⊓ β ⊑ α ⊓ β'.
Proof. rewrite !lft_incl_elem_of. set_solver. Qed.

(** ** Ghost state *)

(** State of an atomic lifetime *)
Variant alftst :=
| #[local] live_alft (* Live *)
| #[local] dead_alft (* Dead *)
| #[local] etern_alft (* Eternal *).
(** Equality on [alftst] is decidable *)
Local Instance alftst_eq_dec : EqDecision alftst.
Proof. solve_decision. Defined.

(** State of lifetimes *)
Local Definition lftst := gmap alft alftst.
#[warning="-redundant-canonical-projection"]
Local Canonical lftstO := leibnizO lftst.

(** Algebra for an atomic lifetime *)
Local Definition alftR := csumR
  dfracR (* Live, fractionally owned or eternal *)
  unitR (* Dead *).
(** Algebra for atomic lifetimes *)
Definition alftmR := gmapR alft alftR.

(** View relation between [option alftst] and [option alftR] *)
Definition view_alft' (s : alftst) (r : alftR) : Prop :=
  match s, r with
  | live_alft, Cinl (DfracOwn q) => (q ≤ 1)%Qp
  | dead_alft, Cinr _ => True
  | etern_alft, Cinl dq => ✓ dq
  | _, _ => False
  end.
Definition view_alft (os : option alftst) (or : option alftR) : Prop :=
  match or, os with
  | None, _ => True
  | Some _, None => False
  | Some r, Some s => view_alft' s r
  end.
(** [view_alft] entails [✓] *)
Local Lemma view_alft_valid os or : view_alft os or → ✓ or.
Proof. case: or=>// r. case: os=>// s. case: s; case: r=>//. by case. Qed.
(** [view_alft] is monotone *)
Local Lemma view_alft_mono os or or' :
  view_alft os or → or' ≼ or → view_alft os or'.
Proof.
  case: or'=>//= r'. case: or; [|by move=> _ /Some_included_is_Some[]]=>/= r.
  case: os=>// ++[[rf|] /leibniz_equiv_iff]; [|by move=> ??[<-]]=> ++[].
  case; case r=>//=.
  - case=>// q ?. case r'; case rf=>//. case=> [q'||?]; case=>// ? [eq].
    etrans; [|done]. rewrite eq. apply Qp.le_add_l.
  - move=> ? _. by case r'; case rf.
  - move=> dq val. case r'; case rf=>// ?? [eq]. move: val. rewrite eq.
    apply cmra_valid_op_l.
Qed.
(** View relation between [lftst] and [alftmR] *)
Local Definition view_lft_raw (σ : lftst) (m : alftmR) : Prop :=
  ∀ a, view_alft (σ !! a) (m !! a).
Local Program Canonical view_lft : view_rel lftst alftmR :=
  ViewRel (const view_lft_raw) _ _ _.
Next Obligation.
  move=>/= _ _ σ _ m m' view /discrete_iff/leibniz_equiv_iff<-
    /cmra_discrete_included_iff/lookup_included inc _ a.
  by eapply view_alft_mono.
Qed.
Next Obligation.
  move=> ????. apply cmra_discrete_valid_iff=> ?. by apply: view_alft_valid.
Qed.
Next Obligation. move=>/= _. by exists ∅. Qed.
(** [view_lft] is discrete *)
Local Instance view_lft_discrete : ViewRelDiscrete view_lft.
Proof. by move=> *. Qed.

(** Algebra for the lifetime machinery *)
Definition lftR := viewR view_lft.

(** Ghost state for lifetimes *)
Class lftGpreS Σ := lftGpreS_in : inG Σ lftR.
Local Existing Instance lftGpreS_in.
Class lftGS Σ := LftGS {
  lftGS_pre : lftGpreS Σ;
  lft_name : gname;
}.
Local Existing Instance lftGS_pre.
Definition lftΣ : gFunctors := GFunctor lftR.
#[export] Instance subG_lft `{!subG lftΣ Σ} : lftGpreS Σ. Proof. solve_inG. Qed.

(** ** Lifetime tokens *)

(** Atomic live lifetime token *)
Local Definition alft_live `{!lftGS Σ} (a : alft) (q : Qp) : iProp Σ :=
  own lft_name (◯V {[a := Cinl (DfracOwn q)]}).
(** Live lifetime token *)
Notation lft_live α q := ([∗ mset] a ∈ α, alft_live a q)%I.

(** Dead atomic lifetime token *)
Local Definition alft_dead `{!lftGS Σ} (a : alft) : iProp Σ :=
  own lft_name (◯V {[a := Cinr ()]}).
(** Dead lifetime token *)
Local Definition lft_dead_def `{!lftGS Σ} (α : lft) : iProp Σ :=
  ∃ a, ⌜a ∈ α⌝ ∗ alft_dead a.
Local Lemma lft_dead_aux : seal (@lft_dead_def). Proof. by eexists. Qed.
Definition lft_dead `{!lftGS Σ} := lft_dead_aux.(unseal) _ _.
Local Lemma lft_dead_unseal `{!lftGS Σ} : @lft_dead = @lft_dead_def.
Proof. exact: seal_eq. Qed.

(** Eternal atomic lifetime token *)
Local Definition alft_etern `{!lftGS Σ} (a : alft) : iProp Σ :=
  own lft_name (◯V {[a := Cinl DfracDiscarded]}).
(** Eternal lifetime token *)
Notation lft_etern α := ([∗ mset] a ∈ α, alft_etern a)%I.

(** Persistent token for [alftst] *)
Definition alftst_ptok `{!lftGS Σ} (a : alft) (s : alftst) : iProp Σ :=
  match s with
  | live_alft => True
  | etern_alft => alft_etern a
  | dead_alft => alft_dead a
  end.
#[export] Instance alftst_ptok_persistent `{!lftGS Σ} {a s} :
  Persistent (alftst_ptok a s).
(** Lifetime authoritative token *)
Definition lft_auth `{!lftGS Σ} (σ : lftst) : iProp Σ :=
  own lft_name (●V σ) ∗ [∗ map] a↦s ∈ σ, alftst_ptok a s.
Proof. case s; exact _. Qed.
(** Lifetime world satisfaction *)
Definition lft_wsat `{!lftGS Σ} : iProp Σ := ∃ σ, lft_auth σ.

Module LftNotation'.
  Notation "q .[ α ]" := (lft_live α q)
    (format "q .[ α ]", at level 2, left associativity) : bi_scope.
  Notation "[† α ]" := (lft_dead α) (format "[† α ]") : bi_scope.
  Notation "[∞ α ]" := (lft_etern α) (format "[∞ α ]") : bi_scope.
End LftNotation'.
Import LftNotation'.

(** Allocate [lft_wsat] *)
Lemma lft_wsat_alloc `{!lftGpreS Σ} : ⊢ |==> ∃ _ : lftGS Σ, lft_wsat.
Proof.
  iMod (own_alloc (●V ∅)) as (γ) "●"; [by apply view_auth_valid|]. iModIntro.
  iExists (LftGS _ _ γ), _. by iFrame.
Qed.

Section lft.
  Context `{!lftGS Σ}.

  (** Dead and eternal lifetime tokens are persistent *)
  #[export] Instance lft_dead_persistent {α} : Persistent [†α].
  Proof. rewrite lft_dead_unseal. exact _. Qed.
  Fact lft_etern_persistent {α} : Persistent [∞α].
  Proof. exact _. Qed.

  (** Live, dead, eternal lifetime tokens are timeless *)
  Fact lft_live_timeless {α q} : Timeless q.[α].
  Proof. exact _. Qed.
  #[export] Instance lft_dead_timeless {α} : Timeless [†α].
  Proof. rewrite lft_dead_unseal. exact _. Qed.
  Fact lft_etern_timeless {α} : Timeless [∞α].
  Proof. exact _. Qed.

  (** Live and dead lifetime tokens can't coexist *)
  Lemma lft_live_dead {α q} : q.[α] -∗ [†α] -∗ False.
  Proof.
    rewrite lft_dead_unseal. iIntros "q". iDestruct 1 as (a) "[%e †]".
    rewrite big_sepMS_elem_of; [|done].
    iDestruct (own_valid_2 with "q †") as %val.
    rewrite -view_frag_op singleton_op view_frag_valid in val.
    move: (val 0)=> [? view]. move: (view a). rewrite lookup_singleton.
    by move/view_alft_valid.
  Qed.
  (** Eternal and dead lifetime tokens can't coexist *)
  Lemma lft_etern_dead {α} : [∞α] -∗ [†α] -∗ False.
  Proof.
    rewrite lft_dead_unseal. iIntros "∞". iDestruct 1 as (a) "[%e †]".
    rewrite big_sepMS_elem_of; [|done].
    iDestruct (own_valid_2 with "∞ †") as %val.
    rewrite -view_frag_op singleton_op view_frag_valid in val.
    move: (val 0)=> [? view]. move: (view a). rewrite lookup_singleton.
    by move/view_alft_valid.
  Qed.
  (** The fraction of a live lifetime token is no more than [1] *)
  Lemma lft_live_valid {α q} : α ≠ ⊤ → q.[α] -∗ ⌜q ≤ 1⌝%Qp.
  Proof.
    case: (gmultiset_choose_or_empty α); [|done]=> [[a ?]_]. iIntros "α".
    iDestruct (big_sepMS_elem_of with "α") as "a"; [done|].
    iDestruct (own_valid with "a") as %val. rewrite view_frag_valid in val.
    move: (val 0)=> [? view]. move: (view a). rewrite lookup_singleton.
    by move/view_alft_valid.
  Qed.

  (** Live lifetime token is fractional *)
  Local Instance alft_live_fract {a} : Fractional (alft_live a)%I.
  Proof. move=> ??. by rewrite -own_op -view_frag_op singleton_op -Cinl_op. Qed.
  Local Instance alft_live_as_fract {a q} :
    AsFractional (alft_live a q) (alft_live a) q.
  Proof. split; [done|exact _]. Qed.
  #[export] Instance lft_live_fract {α} : Fractional (λ q, q.[α])%I.
  Proof. exact _. Qed.
  #[export] Instance lft_live_as_fract {α q} :
    AsFractional q.[α] (λ q, q.[α])%I q.
  Proof. split; [done|exact _]. Qed.
  #[export] Instance lft_live_fract_frame {p α} `{!FrameFractionalQp q r s} :
    Frame p q.[α] r.[α] s.[α] | 5.
  Proof. apply: frame_fractional. Qed.

  (** Combine live lifetime tokens *)
  Lemma lft_live_combine {α β q r} :
    q.[α] -∗ r.[β] -∗ ∃ s, s.[α ⊓ β] ∗ (s.[α ⊓ β] -∗ q.[α] ∗ r.[β]).
  Proof.
    case: (Qp.lower_bound q r)=> [s[t[t'[->->]]]]. iIntros "[α α'][β β']".
    iExists s. iFrame "α β α' β'". iIntros "[$$]".
  Qed.

  (** Allcate a fresh lifetime *)
  Lemma lft_alloc : ⊢ |=[lft_wsat]=> ∃ α, ⌜α ≠ ⊤⌝ ∗ 1.[α].
  Proof.
    iIntros "[%σ[● p]]". set a := fresh (dom σ).
    have σa: σ !! a = None by apply not_elem_of_dom, is_fresh.
    iMod (own_update _ _ (●V <[a := live_alft]> σ ⋅ ◯V _) with "●") as "[$ ?]";
      last first.
    { iModIntro. iSplit; [rewrite big_sepM_insert //=; by iSplit|].
      iExists {[+a+]}. rewrite big_sepMS_singleton. by iSplit. }
    apply view_update_alloc=>/= _ m view b. case (decide (a = b)); last first.
    { move=> ?. rewrite lookup_insert_ne; [|done].
      rewrite lookup_op lookup_singleton_ne; [|done]. by rewrite left_id. }
    move=> <-. rewrite lookup_insert lookup_op lookup_singleton. move: (view a).
    rewrite σa. by case: (m !! a).
  Qed.

  (** Kill a lifetime *)
  Lemma lft_kill {α} : α ≠ ⊤ → 1.[α] =[lft_wsat]=∗ [†α].
  Proof.
    case: (gmultiset_choose_or_empty α); [|done]=> [[a ?]_].
    rewrite big_sepMS_elem_of; [|done]. iIntros "a [%σ[● p]]".
    iMod (own_update_2 _ _ _ (●V <[a := dead_alft]> σ ⋅ ◯V {[a := Cinr ()]})
      with "● a") as "[$ #?]"; last first.
    { iModIntro. iAssert [†α]%I as "†".
      { rewrite lft_dead_unseal. iExists a. by iSplit. }
      iSplit; by [iApply big_sepM_insert_2|]. }
    apply view_update=>/= _ m view b. case (decide (a = b)); last first.
    { move=> ?. rewrite lookup_insert_ne; [|done]. move: (view b).
      by rewrite !lookup_op !lookup_singleton_ne; [|done..]. }
    move=> <-. move: (view a).
    rewrite lookup_insert !lookup_op !lookup_singleton.
    by case: (m !! a)=>// ? /view_alft_valid/Some_valid/exclusive_l.
  Qed.

  (** Eternalize a lifetime *)
  Local Lemma alft_eternalize {a q} :
    alft_live a q ⊢ |=[lft_wsat]=> alft_etern a.
  Proof.
    iIntros "a [%σ[● p]]".
    iMod (own_update_2 _ _ _
      (●V <[a := etern_alft]> σ ⋅ ◯V {[a := Cinl DfracDiscarded]}) with "● a")
      as "[$ #?]"; last first.
    { iModIntro. iSplit; by [iApply big_sepM_insert_2|]. }
    apply view_update=>/= _ m view b. case (decide (a = b)); last first.
    { move=> ?. rewrite lookup_insert_ne; [|done]. move: (view b).
      by rewrite !lookup_op !lookup_singleton_ne; [|done..]. }
    move=> <-. move: (view a).
    rewrite lookup_insert !lookup_op !lookup_singleton.
    case: (m !! a)=>// r /view_alft_valid/Some_valid. case: r=>// dq.
    case: dq=>//= q' /Cinl_valid val; rewrite dfrac_valid /=.
    - apply: Qp.lt_le_trans; [|exact val]. apply Qp.lt_add_r.
    - etrans; [|exact val]. apply Qp.lt_add_r.
  Qed.
  Lemma lft_eternalize {α q} : q.[α] =[lft_wsat]=∗ [∞α].
  Proof.
    setoid_rewrite alft_eternalize. apply bi.entails_wand, big_sepMS_gen_upd.
  Qed.

  (** Get a live lifetime token out of an eternal lifetime token *)
  Local Lemma alft_etern_live {a} : alft_etern a ==∗ ∃ q, alft_live a q.
  Proof.
    iIntros "∞".
    iMod (own_updateP (λ x, ∃ y, x = ◯V y ∧ ∃ q, y = {[a := Cinl (DfracOwn q)]})
      with "∞") as (q[?[->[?->]]]) "?"; [|by iExists _].
    apply view_updateP_frag=>/= σ _ m view.
    move: (view a). rewrite lookup_op lookup_singleton Some_op_opM.
    case eqσ: (σ !! a)=>/= [s|//]. move: eqσ.
    case: s=>/=. { case: (m !! a)=>//. case=>//. by case. }
    { case: (m !! a)=>//. by case. }
    move=> eqσ val. have [odq eqm]: ∃ odq, m !! a = Cinl <$> odq.
    { move: val.
      case: (m !! a); [case|]=>// *; by [eexists (Some _)|exists None]. }
    have {}val: ✓ (DfracDiscarded ⋅? odq).
    { move: val. rewrite eqm. by case odq. }
    move: dfrac_undiscard_update. rewrite cmra_discrete_updateP=> upd.
    move: (upd odq val)=> [_[[q ->]{}val]]. eexists _. split; [by exists q|].
    move=> b. rewrite lookup_op. case (decide (a = b)); last first.
    { move=> ?. move: (view b). by rewrite lookup_op !lookup_singleton_ne. }
    move=> <-. rewrite eqσ eqm lookup_singleton. move: val. by case odq.
  Qed.
  Local Lemma alftl_etern_live {al} :
    ([∗ list] a ∈ al, alft_etern a) ==∗ ∃ q, [∗ list] a ∈ al, alft_live a q.
  Proof.
    elim: al=> [|a al IH]/=; [iIntros "_"; by iExists 1%Qp|].
    iIntros "[∞ al]". iMod (alft_etern_live with "∞") as (q) "a".
    iMod (IH with "al") as (r) "al". iModIntro.
    case: (Qp.lower_bound q r)=> [s[t[t'[->->]]]].
    iExists s. iDestruct "a" as "[$ _]". iStopProof. do 3 f_equiv.
    iDestruct 1 as "[$ ?]".
  Qed.
  Lemma lft_etern_live {α} : [∞α] ==∗ ∃ q, q.[α].
  Proof. setoid_rewrite big_opMS_elements. apply alftl_etern_live. Qed.

  (** Live lifetime token over [⊤]/[⊓] *)
  Lemma lft_live_top {q} : ⊢ q.[⊤].
  Proof. by apply big_sepMS_empty'. Qed.
  Lemma lft_live_meet {α β q} : q.[α ⊓ β] ⊣⊢ q.[α] ∗ q.[β].
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
  Lemma lft_etern_top : ⊢ [∞⊤].
  Proof. by apply big_sepMS_empty'. Qed.
  Lemma lft_etern_meet {α β} : [∞α ⊓ β] ⊣⊢ [∞α] ∗ [∞β].
  Proof. by apply big_sepMS_disj_union. Qed.

  (** Access a live lifetime token using [⊑] *)
  Local Lemma alftl_incl_live_acc {α q} (bl : list alft) :
    bl ⊆ elements (dom α) →
    q.[α] ⊢ ∃ r, ([∗ list] b ∈ bl, alft_live b r) ∗
      (([∗ list] b ∈ bl, alft_live b r) -∗ q.[α]).
  Proof.
    elim: bl q=> /=[|b bl IH] q inc.
    { iIntros. iExists 1%Qp. iSplit; [done|]. by iFrame. }
    iIntros "[α α']". iDestruct (IH with "α'") as (r) "[bl →α']"; [set_solver|].
    iDestruct (big_sepMS_elem_of_acc _ _ b with "α") as "[b →α]".
    { rewrite -gmultiset_elem_of_dom -elem_of_elements. set_solver. }
    case: (Qp.lower_bound r (q/2)%Qp)=> [s[t[t'[->eq]]]].
    have -> : alft_live b (q / 2) ⊣⊢ alft_live b s ∗ alft_live b t'.
    { by rewrite eq fractional. }
    iExists _. iDestruct "b" as "[$ b']". setoid_rewrite fractional.
    rewrite big_sepL_sep. iDestruct "bl" as "[$ bl']". iIntros "[b bl]".
    iDestruct ("→α" with "[$b $b']") as "$". iApply "→α'". iFrame.
  Qed.
  Lemma lft_incl_live_acc {α β q} :
    α ⊑ β → q.[α] ⊢ ∃ r, r.[β] ∗ (r.[β] -∗ q.[α]).
  Proof.
    move=> ?. iIntros "α".
    iDestruct (alftl_incl_live_acc (elements β) with "α") as (r) "[bl →α]".
    { move=> ?. rewrite gmultiset_elem_of_elements -gmultiset_elem_of_dom.
      rewrite elem_of_elements. auto. }
    iExists _. rewrite -big_opMS_elements. iFrame.
  Qed.

  (** Modify a dead lifetime token using [⊑] *)
  Lemma lft_incl_dead {α β} : α ⊑ β → [†β] ⊢ [†α].
  Proof.
    rewrite lft_dead_unseal=>/lft_incl_elem_of ?. iDestruct 1 as (a) "[% †]".
    iExists a. iFrame "†". iPureIntro. auto.
  Qed.
  #[export] Instance lft_dead_mono : Proper (flip (⊑) ==> (⊢)) (λ α, [†α])%I.
  Proof. move=> >. exact lft_incl_dead. Qed.
  #[export] Instance lft_dead_flip_mono :
    Proper ((⊑) ==> flip (⊢)) (λ α, [†α])%I.
  Proof. solve_proper. Qed.

  (** Modify an eternal lifetime token using [⊑] *)
  Lemma lft_incl_etern {α β} : α ⊑ β → [∞α] ⊢ [∞β].
  Proof.
    rewrite !big_opMS_elements=> /lft_incl_elem_of inc. iIntros "α".
    iApply big_sepL_forall. iIntros (?? elem).
    apply elem_of_list_lookup_2 in elem. move: elem.
    rewrite gmultiset_elem_of_elements=> ?. rewrite big_sepL_elem_of; [done|].
    rewrite gmultiset_elem_of_elements. auto.
  Qed.
  #[export] Instance lft_etern_mono : Proper ((⊑) ==> (⊢)) (λ α, [∞α])%I.
  Proof. move=> >. exact lft_incl_etern. Qed.
  #[export] Instance lft_etern_flip_mono :
    Proper (flip (⊑) ==> flip (⊢)) (λ α, [∞α])%I.
  Proof. solve_proper. Qed.
End lft.

(** ** [⊑□]: Persistent lifetime inclusion *)

(** Lifetime difference *)
Local Definition lft_diff (α β : lft) : lft :=
  gset_to_gmultiset (dom α ∖ dom β).
(** Element of [lft_diff] *)
Local Lemma elem_of_lft_diff {a α β} : a ∈ lft_diff α β ↔ a ∈ α ∧ a ∉ β.
Proof.
  by rewrite elem_of_gset_to_gmultiset elem_of_difference
    !gmultiset_elem_of_dom.
Qed.
(** Meet with [lft_diff] *)
Local Lemma lft_meet_diff_incl {α β} : α ⊓ lft_diff β α ⊑ β.
Proof.
  apply lft_incl_elem_of=> a ?. rewrite gmultiset_elem_of_disj_union.
  rewrite elem_of_lft_diff. case: (decide (a ∈ α)); auto.
Qed.

Section lft_sincl.
  Context `{!lftGS Σ}.
  (** Persistent lifetime inclusion *)
  Local Definition lft_sincl_def (α β : lft) : iProp Σ :=
    [†α] ∨ [∞ lft_diff β α].
  Lemma lft_sincl_aux : seal lft_sincl_def. Proof. by eexists. Qed.
  Local Definition lft_sincl := lft_sincl_aux.(unseal).
  Local Lemma lft_sincl_unseal : lft_sincl = lft_sincl_def.
  Proof. exact: seal_eq. Qed.
End lft_sincl.

Module LftNotation.
  Export LftNotation'.
  Infix "⊑□" := lft_sincl (at level 70) : bi_scope.
End LftNotation.
Import LftNotation.

Section lft_sincl.
  Context `{!lftGS Σ}.

  (** [⊑□] is persistent and timeless *)
  #[export] Instance lft_sincl_persistent {α β} : Persistent (α ⊑□ β).
  Proof. rewrite lft_sincl_unseal. exact _. Qed.
  #[export] Instance lft_sincl_timeless {α β} : Timeless (α ⊑□ β).
  Proof. rewrite lft_sincl_unseal. exact _. Qed.

  (** Access a live lifetime token by [⊑□] *)
  Lemma lft_sincl_live_acc {α β q} :
    α ⊑□ β -∗ q.[α] ==∗ ∃ r, r.[β] ∗ (r.[β] -∗ q.[α]).
  Proof.
    rewrite lft_sincl_unseal. iIntros "[†|∞] α".
    { iDestruct (lft_live_dead with "α †") as %[]. }
    iMod (lft_etern_live with "∞") as (r) "δ". iModIntro.
    iDestruct (lft_live_combine with "α δ") as (s) "[αδ →]".
    iDestruct (lft_incl_live_acc with "αδ") as (?) "[β →α]";
      [exact lft_meet_diff_incl|].
    iExists _. iFrame "β". iIntros "β". iDestruct ("→α" with "β") as "αδ".
    iDestruct ("→" with "αδ") as "[$ _]".
  Qed.

  (** Modify a dead lifetime token by [⊑□] *)
  Lemma lft_sincl_dead {α β} : α ⊑□ β ⊢ [†β] -∗ [†α].
  Proof.
    rewrite lft_sincl_unseal. iIntros "[$|∞] †"; [done|].
    rewrite lft_incl_dead; [|eapply lft_meet_diff_incl]. rewrite lft_dead_meet.
    iDestruct "†" as "[$|†]". iDestruct (lft_etern_dead with "∞ †") as %[].
  Qed.

  (** Modify an eternal lifetime token using [⊑□] *)
  Lemma lft_sincl_etern {α β} : α ⊑□ β ⊢ [∞α] -∗ [∞β].
  Proof.
    rewrite lft_sincl_unseal. iIntros "[†|∞] α".
    { iDestruct (lft_etern_dead with "α †") as %[]. }
    iApply lft_incl_etern; [eapply lft_meet_diff_incl|]. by iSplit; [|done].
  Qed.

  (** [⊑] entails [⊑□] *)
  Lemma lft_incl_sincl {α β} : α ⊑ β → ⊢ α ⊑□ β.
  Proof.
    rewrite lft_sincl_unseal=> ?. iRight. iApply big_sepMS_intro.
    iIntros (a elem). move: elem=> /elem_of_gset_to_gmultiset. set_solver.
  Qed.

  (** [⊑□] is reflexive, is transitive, has the maximum [⊤] *)
  Lemma lft_sincl_refl {α} : ⊢ α ⊑□ α.
  Proof. by apply lft_incl_sincl. Qed.
  Lemma lft_sincl_trans {α β γ} : α ⊑□ β -∗ β ⊑□ γ -∗ α ⊑□ γ.
  Proof.
    rewrite lft_sincl_unseal. iIntros "[$|∞]"; [by iIntros|]. iIntros "[†|∞']".
    { iLeft. rewrite lft_incl_dead; [|eapply lft_meet_diff_incl].
      rewrite lft_dead_meet. iDestruct "†" as "[$|†]".
      iDestruct (lft_etern_dead with "∞ †") as %[]. }
    iRight. iCombine "∞ ∞'" as "∞". rewrite -lft_etern_meet.
    iApply (lft_incl_etern with "∞"). apply lft_incl_elem_of=> a.
    rewrite gmultiset_elem_of_disj_union !elem_of_lft_diff.
    case (decide (a ∈ β)); naive_solver.
  Qed.
  Lemma lft_sincl_top {α} : ⊢ α ⊑□ ⊤.
  Proof. apply lft_incl_sincl, lft_incl_top. Qed.

  (** A dead lifetime is the minimum w.r.t. [⊑□] *)
  Lemma lft_sincl_by_dead {α} : [†α] ⊢ ∀ β, α ⊑□ β.
  Proof. rewrite lft_sincl_unseal. by iIntros "$". Qed.

  (** An eternal lifetime is the maximum w.r.t. [⊑□] *)
  Lemma lft_sincl_by_etern {α} : [∞α] ⊢ ∀ β, β ⊑□ α.
  Proof.
    rewrite lft_sincl_unseal. iIntros "#∞ %β". iRight.
    iApply (lft_incl_etern with "∞"). apply lft_incl_elem_of=> ?.
    rewrite elem_of_lft_diff. set_solver.
  Qed.
  Lemma lft_eternalize_sincl {α q} : q.[α] =[lft_wsat]=∗ ∀ β, β ⊑□ α.
  Proof. rewrite -lft_sincl_by_etern. apply lft_eternalize. Qed.

  (** [⊓] is the lub w.r.t. [⊑□] *)
  Lemma lft_sincl_meet_l {α β} : ⊢ α ⊓ β ⊑□ α.
  Proof. apply lft_incl_sincl, lft_incl_meet_l. Qed.
  Lemma lft_sincl_meet_r {α β} : ⊢ α ⊓ β ⊑□ β.
  Proof. apply lft_incl_sincl, lft_incl_meet_r. Qed.
  Lemma lft_sincl_meet_intro {α β γ} : α ⊑□ β -∗ α ⊑□ γ -∗ α ⊑□ β ⊓ γ.
  Proof.
    rewrite lft_sincl_unseal. iIntros "[$|∞]"; [by iIntros|]. iIntros "[$|∞']".
    iRight. iCombine "∞ ∞'" as "∞". rewrite -lft_etern_meet.
    iApply (lft_incl_etern with "∞"). rewrite lft_incl_elem_of=> a.
    rewrite gmultiset_elem_of_disj_union !elem_of_lft_diff. set_solver.
  Qed.
  Lemma lft_sincl_meet_mono_l {α α' β} : α ⊑□ α' ⊢ α ⊓ β ⊑□ α' ⊓ β.
  Proof.
    iIntros "#?". iApply lft_sincl_meet_intro; [|by iApply lft_sincl_meet_r].
    iApply lft_sincl_trans; [|done]. iApply lft_sincl_meet_l.
  Qed.
  Lemma lft_sincl_meet_mono_r {α β β'} : β ⊑□ β' ⊢ α ⊓ β ⊑□ α ⊓ β'.
  Proof. rewrite comm [α ⊓ β']comm. exact lft_sincl_meet_mono_l. Qed.
End lft_sincl.

(** ** Decision based on [lft_auth] *)

(** [lft_stdead]: Lifetime death based on [lftst] *)
Definition lft_stdead (σ : lftst) (α : lft) : Prop :=
  set_Exists (λ a, σ !! a = Some dead_alft) (dom α).
(** [lft_stdead] is decidable *)
#[export] Instance lft_stdead_dec {σ α} : Decision (lft_stdead σ α) := _.

(** [lft_stetern]: Lifetime eternity based on [lftst] *)
Definition lft_stetern (σ : lftst) (α : lft) : Prop :=
  set_Forall (λ a, σ !! a = Some etern_alft) (dom α).
(** [lft_stdead] is decidable *)
#[export] Instance lft_stetern_dec {σ α} : Decision (lft_stetern σ α) := _.

(** [lft_stincl]: Lifetime inclusion based on [lftst] *)
Definition lft_stincl (σ : lftst) (α β : lft) : Prop :=
  lft_stdead σ α ∨ lft_stetern σ (lft_diff β α).
(** [lft_stincl] is decidable *)
#[export] Instance lft_stincl_dec {σ} : RelDecision (lft_stincl σ) :=
  λ _ _, _.

Section lft_auth.
  Context `{!lftGS Σ}.

  (** [lft_stdead] implies [lft_dead] under [lft_auth] *)
  Lemma lft_stdead_dead {σ α} : lft_stdead σ α → lft_auth σ ⊢ [†α].
  Proof.
    rewrite lft_dead_unseal. iIntros ([a[??]]) "[_ #p]". iExists a.
    rewrite big_sepM_lookup //=. iSplit; [|done].
    by rewrite -gmultiset_elem_of_dom.
  Qed.
  (** [lft_dead] implies [lft_stdead] under [lft_auth] *)
  Lemma lft_dead_stdead {σ α} : lft_auth σ -∗ [†α] -∗ ⌜lft_stdead σ α⌝.
  Proof.
    rewrite lft_dead_unseal. iIntros "[● _] [%a[% †]]". iExists a.
    iSplit; [by rewrite gmultiset_elem_of_dom|].
    iDestruct (own_valid_2 with "● †") as %val. iPureIntro.
    move: val=>/view_both_valid val. move: (val 0 a).
    rewrite lookup_singleton /=. case: (σ !! a)=>//. by case.
  Qed.

  (** [lft_stetern] implies [lft_etern] under [lft_auth] *)
  Lemma lft_stetern_etern {σ α} : lft_stetern σ α → lft_auth σ ⊢ [∞α].
  Proof.
    iIntros (all) "[_ #p]". iApply big_sepMS_intro. iIntros "!> %a %elem".
    rewrite -gmultiset_elem_of_dom in elem. move: (all _ elem)=> ?.
    by rewrite big_sepM_lookup //=.
  Qed.
  (** [lft_etern] implies [lft_stetern] under [lft_auth] *)
  Lemma lft_etern_stetern {σ α} : lft_auth σ -∗ [∞α] -∗ ⌜lft_stetern σ α⌝.
  Proof.
    iIntros "[● _] ∞ %a %elem". rewrite gmultiset_elem_of_dom in elem.
    rewrite big_sepMS_elem_of //. iDestruct (own_valid_2 with "● ∞") as %val.
    iPureIntro. move: val=> /view_both_valid val. move: (val 0 a).
    rewrite lookup_singleton. case: (σ !! a)=>//. by case.
  Qed.

  (** [lft_stincl] implies [⊑□] under [lft_auth] *)
  Lemma lft_stincl_sincl {σ α β} : lft_stincl σ α β → lft_auth σ ⊢ α ⊑□ β.
  Proof.
    rewrite lft_sincl_unseal. move=> [dead|etern]; iIntros "σ".
    { iLeft. by rewrite lft_stdead_dead. }
    iRight. by iApply (lft_stetern_etern with "σ").
  Qed.
  (** [⊑□] implies [lft_stincl] under [lft_auth] *)
  Lemma lft_sincl_stincl {σ α β} : lft_auth σ -∗ α ⊑□ β -∗ ⌜lft_stincl σ α β⌝.
  Proof.
    rewrite lft_sincl_unseal. iIntros "σ [†|∞]".
    - iLeft. by iApply (lft_dead_stdead with "σ").
    - iRight. by iApply (lft_etern_stetern with "σ").
  Qed.
End lft_auth.
