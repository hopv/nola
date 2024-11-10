(** This file proves the basic laws of the HeapLang program logic by applying
the Iris lifting lemmas. *)
From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import mono_nat.
From iris.base_logic.lib Require Export gen_heap proph_map gen_inv_heap.
From iris.program_logic Require Export weakestpre total_weakestpre.
From iris.program_logic Require Import ectx_lifting total_ectx_lifting.
From nola.bi Require Export wpw.
From nola.heap_lang Require Export class_instances definitions.
From nola.heap_lang Require Import tactics notation.
From iris.prelude Require Import options.
Import WpwNotation.

Section lifting.
Context `{!heapGS_gen hlc Σ}.
Implicit Types Φ Ψ : val → iProp Σ.
Implicit Types P Q : iProp Σ.
Implicit Types efs : list expr.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types l : loc.

Lemma wp_lb_init W s E e Φ :
  TCEq (to_val e) None →
  (steps_lb 0 -∗ WP[W] e @ s; E {{ v, Φ v }}) -∗
  WP[W] e @ s; E {{ Φ }}.
Proof.
  (** TODO: We should try to use a generic lifting lemma (and avoid [wp_unfold])
  here, since this breaks the WP abstraction. *)
  rewrite !wp_unfold /wp_pre /=. iIntros (->) "Hwp".
  iIntros (σ1 ns κ κs m) "(W & Hσ & Hκ & Hsteps)".
  iDestruct (steps_lb_get with "Hsteps") as "#Hlb".
  iDestruct (steps_lb_le _ 0 with "Hlb") as "Hlb0"; [lia|].
  iSpecialize ("Hwp" with "Hlb0"). iApply ("Hwp" $! σ1 ns κ κs m). iFrame.
Qed.

Lemma wp_lb_update W s n E e Φ :
  TCEq (to_val e) None →
  steps_lb n -∗
  WP[W] e @ s; E {{ v, steps_lb (S n) -∗ Φ v }} -∗
  WP[W] e @ s; E {{ Φ }}.
Proof.
  (** TODO: We should try to use a generic lifting lemma (and avoid [wp_unfold])
  here, since this breaks the WP abstraction. *)
  rewrite !wp_unfold /wp_pre /=. iIntros (->) "Hlb Hwp".
  iIntros (σ1 ns κ κs m) "(W & Hσ & Hκ & Hsteps)".
  iDestruct (steps_lb_valid with "Hsteps Hlb") as %?.
  iMod ("Hwp" $! σ1 ns κ κs m with "[$W $Hσ $Hκ $Hsteps]") as "[%Hs Hwp]".
  iModIntro. iSplit; [done|].
  iIntros (e2 σ2 efs Hstep) "Hcred".
  iMod ("Hwp" with "[//] Hcred") as "Hwp".
  iIntros "!> !>". iMod "Hwp" as "Hwp". iIntros "!>".
  iApply (step_fupdN_wand with "Hwp").
  iIntros "Hwp". iMod "Hwp" as "(($ & $ & $ & Hsteps)& Hwp & $)".
  iDestruct (steps_lb_get with "Hsteps") as "#HlbS".
  iDestruct (steps_lb_le _ (S n) with "HlbS") as "#HlbS'"; [lia|].
  iModIntro. iFrame "Hsteps".
  iApply (wp_wand with "Hwp"). iIntros (v) "HΦ". by iApply "HΦ".
Qed.

Lemma wp_step_fupdN_lb W s n E1 E2 e P Φ :
  TCEq (to_val e) None →
  E2 ⊆ E1 →
  steps_lb n -∗
  (|={E1∖E2,∅}=> |={∅}▷=>^(S n) |={∅,E1∖E2}=> P) -∗
  WP[W] e @ s; E2 {{ v, P ={E1}=∗ Φ v }} -∗
  WP[W] e @ s; E1 {{ Φ }}.
Proof.
  iIntros (He HE) "Hlb HP Hwp".
  iApply wp_step_fupdN; [done|].
  iSplit; [|by iFrame].
  iIntros (σ ns κs nt) "(? & ? & ? & Hsteps)".
  iDestruct (steps_lb_valid with "Hsteps Hlb") as %Hle.
  iApply fupd_mask_intro; [set_solver|].
  iIntros "_". iPureIntro. rewrite /num_laters_per_step /=. lia.
Qed.

(** Recursive functions: we do not use this lemmas as it is easier to use Löb
induction directly, but this demonstrates that we can state the expected
reasoning principle for recursive functions, without any visible ▷. *)
Lemma wp_rec_löb W s E f x e Φ Ψ :
  □ ( □ (∀ v, Ψ v -∗ WP[W] (rec: f x := e)%V v @ s; E {{ Φ }}) -∗
     ∀ v, Ψ v -∗ WP[W] (subst' x v (subst' f (rec: f x := e) e)) @ s; E {{ Φ }}) -∗
  ∀ v, Ψ v -∗ WP[W] (rec: f x := e)%V v @ s; E {{ Φ }}.
Proof.
  iIntros "#Hrec". iLöb as "IH". iIntros (v) "HΨ".
  iApply @lifting.wp_pure_step_later; first done.
  iIntros "!> _". iApply ("Hrec" with "[] HΨ"). iIntros "!>" (w) "HΨ".
  iApply ("IH" with "HΨ").
Qed.

(** Fork: Not using Texan triples to avoid some unnecessary [True] *)
Lemma wp_fork W s E e Φ :
  ▷ WP[W] e @ s; ⊤ {{ _, True }} -∗ ▷ Φ (LitV LitUnit) -∗ WP[W] Fork e @ s; E {{ Φ }}.
Proof.
  iIntros "He HΦ". iApply wp_lift_atomic_base_step; [done|].
  iIntros (σ1 ns κ κs nt) "(?&?&?&Hsteps) !>"; iSplit; first by eauto with base_step.
  iIntros "!>" (v2 σ2 efs Hstep) "_"; inv_base_step.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  by iFrame.
Qed.

Lemma twp_fork W s E e Φ :
  WP[W] e @ s; ⊤ [{ _, True }] -∗ Φ (LitV LitUnit) -∗ WP[W] Fork e @ s; E [{ Φ }].
Proof.
  iIntros "He HΦ". iApply twp_lift_atomic_base_step; [done|].
  iIntros (σ1 ns κs nt) "(?&?&?&Hsteps) !>"; iSplit; first by eauto with base_step.
  iIntros (κ v2 σ2 efs Hstep); inv_base_step.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  by iFrame.
Qed.

(** Heap *)

(** We need to adjust the [gen_heap] and [gen_inv_heap] lemmas because of our
value type being [option val]. *)

Lemma pointsto_valid l dq v : l ↦{dq} v -∗ ⌜✓ dq⌝.
Proof. apply pointsto_valid. Qed.
Lemma pointsto_valid_2 l dq1 dq2 v1 v2 :
  l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
Proof. iIntros "H1 H2". iCombine "H1 H2" gives %[? [= ?]]. done. Qed.
Lemma pointsto_agree l dq1 dq2 v1 v2 : l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ ⌜v1 = v2⌝.
Proof. iIntros "H1 H2". iCombine "H1 H2" gives %[_ [= ?]]. done. Qed.

Global Instance pointsto_combine_sep_gives l dq1 dq2 v1 v2 :
  CombineSepGives (l ↦{dq1} v1) (l ↦{dq2} v2) ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝ | 20.
  (* We provide an instance with lower cost than the gen_heap instance
     to avoid having to deal with Some v1 = Some v2 *)
Proof.
  rewrite /CombineSepGives. iIntros "[H1 H2]".
  iCombine "H1 H2" gives %[? [=->]]. eauto.
Qed.

Lemma pointsto_combine l dq1 dq2 v1 v2 :
  l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ l ↦{dq1 ⋅ dq2} v1 ∗ ⌜v1 = v2⌝.
Proof.
  iIntros "Hl1 Hl2". by iCombine "Hl1 Hl2" as "$" gives %[_ ->].
Qed.

Lemma pointsto_frac_ne l1 l2 dq1 dq2 v1 v2 :
  ¬ ✓(dq1 ⋅ dq2) → l1 ↦{dq1} v1 -∗ l2 ↦{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
Proof. apply pointsto_frac_ne. Qed.
Lemma pointsto_ne l1 l2 dq2 v1 v2 : l1 ↦ v1 -∗ l2 ↦{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
Proof. apply pointsto_ne. Qed.

Lemma pointsto_persist l dq v : l ↦{dq} v ==∗ l ↦□ v.
Proof. apply pointsto_persist. Qed.

Global Instance inv_pointsto_own_proper l v :
  Proper (pointwise_relation _ iff ==> (≡)) (inv_pointsto_own l v).
Proof.
  intros I1 I2 HI. rewrite /inv_pointsto_own. f_equiv=>-[w|]; last done.
  simpl. apply HI.
Qed.
Global Instance inv_pointsto_proper l :
  Proper (pointwise_relation _ iff ==> (≡)) (inv_pointsto l).
Proof.
  intros I1 I2 HI. rewrite /inv_pointsto. f_equiv=>-[w|]; last done.
  simpl. apply HI.
Qed.

Lemma make_inv_pointsto l v (I : val → Prop) E :
  ↑inv_heapN ⊆ E →
  I v →
  inv_heap_inv -∗ l ↦ v ={E}=∗ l ↦_I v.
Proof. iIntros (??) "#HI Hl". iApply make_inv_pointsto; done. Qed.
Lemma inv_pointsto_own_inv l v I : l ↦_I v -∗ l ↦_I □.
Proof. apply inv_pointsto_own_inv. Qed.

Lemma inv_pointsto_own_acc_strong E :
  ↑inv_heapN ⊆ E →
  inv_heap_inv ={E, E ∖ ↑inv_heapN}=∗ ∀ l v I, l ↦_I v -∗
    (⌜I v⌝ ∗ l ↦ v ∗ (∀ w, ⌜I w ⌝ → l ↦ w ==∗
      inv_pointsto_own l w I ∗ |={E ∖ ↑inv_heapN, E}=> True)).
Proof.
  iIntros (?) "#Hinv".
  iMod (inv_pointsto_own_acc_strong with "Hinv") as "Hacc"; first done.
  iIntros "!>" (l v I) "Hl". iDestruct ("Hacc" with "Hl") as "(% & Hl & Hclose)".
  iFrame "%∗". iIntros (w) "% Hl". iApply "Hclose"; done.
Qed.

Lemma inv_pointsto_own_acc E l v I:
  ↑inv_heapN ⊆ E →
  inv_heap_inv -∗ l ↦_I v ={E, E ∖ ↑inv_heapN}=∗
    (⌜I v⌝ ∗ l ↦ v ∗ (∀ w, ⌜I w ⌝ → l ↦ w ={E ∖ ↑inv_heapN, E}=∗ l ↦_I w)).
Proof.
  iIntros (?) "#Hinv Hl".
  iMod (inv_pointsto_own_acc with "Hinv Hl") as "(% & Hl & Hclose)"; first done.
  iFrame "%∗". iIntros "!>" (w) "% Hl". iApply "Hclose"; done.
Qed.

Lemma inv_pointsto_acc l I E :
  ↑inv_heapN ⊆ E →
  inv_heap_inv -∗ l ↦_I □ ={E, E ∖ ↑inv_heapN}=∗
    ∃ v, ⌜I v⌝ ∗ l ↦ v ∗ (l ↦ v ={E ∖ ↑inv_heapN, E}=∗ ⌜True⌝).
Proof.
  iIntros (?) "#Hinv Hl".
  iMod (inv_pointsto_acc with "Hinv Hl") as ([v|]) "(% & Hl & Hclose)"; [done| |done].
  iIntros "!>". iExists (v). iFrame "%∗".
Qed.

(** The usable rules for [allocN] stated in terms of the [array] proposition
are derived in te file [array]. *)
Lemma heap_array_to_seq_meta l vs (n : nat) :
  length vs = n →
  ([∗ map] l' ↦ _ ∈ heap_array l vs, meta_token l' ⊤) -∗
  [∗ list] i ∈ seq 0 n, meta_token (l +ₗ (i : nat)) ⊤.
Proof.
  iIntros (<-) "Hvs". iInduction vs as [|v vs] "IH" forall (l)=> //=.
  rewrite big_opM_union; last first.
  { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
    intros (j&w&?&Hjl&?&?)%heap_array_lookup.
    rewrite Loc.add_assoc -{1}[l']Loc.add_0 in Hjl. simplify_eq; lia. }
  rewrite Loc.add_0 -fmap_S_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-Loc.add_assoc.
  rewrite big_opM_singleton; iDestruct "Hvs" as "[$ Hvs]". by iApply "IH".
Qed.

Lemma heap_array_to_seq_pointsto l v (n : nat) :
  ([∗ map] l' ↦ ov ∈ heap_array l (replicate n v), gen_heap.pointsto l' (DfracOwn 1) ov) -∗
  [∗ list] i ∈ seq 0 n, (l +ₗ (i : nat)) ↦ v.
Proof.
  iIntros "Hvs". iInduction n as [|n] "IH" forall (l); simpl.
  { done. }
  rewrite big_opM_union; last first.
  { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
    intros (j&w&?&Hjl&_)%heap_array_lookup.
    rewrite Loc.add_assoc -{1}[l']Loc.add_0 in Hjl. simplify_eq; lia. }
  rewrite Loc.add_0 -fmap_S_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-Loc.add_assoc.
  rewrite big_opM_singleton; iDestruct "Hvs" as "[$ Hvs]". by iApply "IH".
Qed.

Lemma twp_allocN_seq W s E v n :
  (0 < n)%Z →
  [[{ True }]][W] AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; E
  [[{ l, RET LitV (LitLoc l); [∗ list] i ∈ seq 0 (Z.to_nat n),
      (l +ₗ (i : nat)) ↦ v ∗ meta_token (l +ₗ (i : nat)) ⊤ }]].
Proof.
  iIntros (Hn Φ) "_ HΦ". iApply twp_lift_atomic_base_step_no_fork; first done.
  iIntros (σ1 ns κs nt) "(W & Hσ & Hκs & Hsteps) !>"; iSplit; first by destruct n; auto with lia base_step.
  iIntros (κ v2 σ2 efs Hstep); inv_base_step.
  iMod (gen_heap_alloc_big _ (heap_array _ (replicate (Z.to_nat n) v)) with "Hσ")
    as "(Hσ & Hl & Hm)".
  { apply heap_array_map_disjoint.
    rewrite length_replicate Z2Nat.id; auto with lia. }
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iModIntro; do 2 (iSplit; first done). iFrame "W Hσ Hκs Hsteps". iApply "HΦ".
  iApply big_sepL_sep. iSplitL "Hl".
  - by iApply heap_array_to_seq_pointsto.
  - iApply (heap_array_to_seq_meta with "Hm"). by rewrite length_replicate.
Qed.
Lemma wp_allocN_seq W s E v n :
  (0 < n)%Z →
  {{{ True }}}[W] AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; E
  {{{ l, RET LitV (LitLoc l); [∗ list] i ∈ seq 0 (Z.to_nat n),
      (l +ₗ (i : nat)) ↦ v ∗ meta_token (l +ₗ (i : nat)) ⊤ }}}.
Proof.
  iIntros (Hn Φ) "_ HΦ". iApply (twp_wp_step with "HΦ").
  iApply twp_allocN_seq; [by auto..|]; iIntros (l) "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_alloc W s E v :
  [[{ True }]][W] Alloc (Val v) @ s; E [[{ l, RET LitV (LitLoc l); l ↦ v ∗ meta_token l ⊤ }]].
Proof.
  iIntros (Φ) "_ HΦ". iApply twp_allocN_seq; [auto with lia..|].
  iIntros (l) "/= (? & _)". rewrite Loc.add_0. iApply "HΦ"; iFrame.
Qed.
Lemma wp_alloc W s E v :
  {{{ True }}}[W] Alloc (Val v) @ s; E {{{ l, RET LitV (LitLoc l); l ↦ v ∗ meta_token l ⊤ }}}.
Proof.
  iIntros (Φ) "_ HΦ". iApply (twp_wp_step with "HΦ").
  iApply twp_alloc; [by auto..|]; iIntros (l) "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_free W s E l v :
  [[{ l ↦ v }]][W] Free (Val $ LitV $ LitLoc l) @ s; E
  [[{ RET LitV LitUnit; True }]].
Proof.
  iIntros (Φ) "Hl HΦ". iApply twp_lift_atomic_base_step_no_fork; first done.
  iIntros (σ1 ns κs nt) "(W & Hσ & Hκs & Hsteps) !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with base_step.
  iIntros (κ v2 σ2 efs Hstep); inv_base_step.
  iMod (gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iModIntro. iSplit; first done. iSplit; first done. iFrame. by iApply "HΦ".
Qed.
Lemma wp_free W s E l v :
  {{{ ▷ l ↦ v }}}[W] Free (Val $ LitV (LitLoc l)) @ s; E
  {{{ RET LitV LitUnit; True }}}.
Proof.
  iIntros (Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_free with "H"); [by auto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_load W s E l dq v :
  [[{ l ↦{dq} v }]][W] Load (Val $ LitV $ LitLoc l) @ s; E [[{ RET v; l ↦{dq} v }]].
Proof.
  iIntros (Φ) "Hl HΦ". iApply twp_lift_atomic_base_step_no_fork; first done.
  iIntros (σ1 ns κs nt) "(W & Hσ & Hκs & Hsteps) !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with base_step.
  iIntros (κ v2 σ2 efs Hstep); inv_base_step.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iModIntro. iSplit; [done|]. iSplit; [done|]. iFrame.
  by iApply "HΦ".
Qed.
Lemma wp_load W s E l dq v :
  {{{ ▷ l ↦{dq} v }}}[W] Load (Val $ LitV $ LitLoc l) @ s; E {{{ RET v; l ↦{dq} v }}}.
Proof.
  iIntros (Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_load with "H"). iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_store W s E l v' v :
  [[{ l ↦ v' }]][W] Store (Val $ LitV $ LitLoc l) (Val v) @ s; E
  [[{ RET LitV LitUnit; l ↦ v }]].
Proof.
  iIntros (Φ) "Hl HΦ". iApply twp_lift_atomic_base_step_no_fork; first done.
  iIntros (σ1 ns κs nt) "(W & Hσ & Hκs & Hsteps) !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with base_step.
  iIntros (κ v2 σ2 efs Hstep); inv_base_step.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iMod (gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit; first done. iSplit; first done. iFrame. by iApply "HΦ".
Qed.
Lemma wp_store W s E l v' v :
  {{{ ▷ l ↦ v' }}}[W] Store (Val $ LitV (LitLoc l)) (Val v) @ s; E
  {{{ RET LitV LitUnit; l ↦ v }}}.
Proof.
  iIntros (Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_store with "H"); [by auto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_xchg W s E l v' v :
  [[{ l ↦ v' }]][W] Xchg (Val $ LitV $ LitLoc l) (Val v) @ s; E
  [[{ RET v'; l ↦ v }]].
Proof.
  iIntros (Φ) "Hl HΦ". iApply twp_lift_atomic_base_step_no_fork; first done.
  iIntros (σ1 ns κs nt) "(W & Hσ & Hκs & Hsteps) !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with base_step.
  iIntros (κ v2 σ2 efs Hstep); inv_base_step.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iMod (gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit; first done. iSplit; first done. iFrame. by iApply "HΦ".
Qed.
Lemma wp_xchg W s E l v' v :
  {{{ ▷ l ↦ v' }}}[W] Xchg (Val $ LitV (LitLoc l)) (Val v) @ s; E
  {{{ RET v'; l ↦ v }}}.
Proof.
  iIntros (Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_xchg with "H"); [by auto..|]. iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_cmpxchg_fail W s E l dq v' v1 v2 :
  v' ≠ v1 → vals_compare_safe v' v1 →
  [[{ l ↦{dq} v' }]][W] CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  [[{ RET PairV v' (LitV $ LitBool false); l ↦{dq} v' }]].
Proof.
  iIntros (?? Φ) "Hl HΦ". iApply twp_lift_atomic_base_step_no_fork; first done.
  iIntros (σ1 ns κs nt) "(W & Hσ & Hκs & Hsteps) !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with base_step.
  iIntros (κ v2' σ2 efs Hstep); inv_base_step.
  rewrite bool_decide_false //.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iModIntro; iSplit; first done. iSplit; first done. iFrame. by iApply "HΦ".
Qed.
Lemma wp_cmpxchg_fail W s E l dq v' v1 v2 :
  v' ≠ v1 → vals_compare_safe v' v1 →
  {{{ ▷ l ↦{dq} v' }}}[W] CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  {{{ RET PairV v' (LitV $ LitBool false); l ↦{dq} v' }}}.
Proof.
  iIntros (?? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_cmpxchg_fail with "H"); [by auto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_cmpxchg_suc W s E l v1 v2 v' :
  v' = v1 → vals_compare_safe v' v1 →
  [[{ l ↦ v' }]][W] CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  [[{ RET PairV v' (LitV $ LitBool true); l ↦ v2 }]].
Proof.
  iIntros (?? Φ) "Hl HΦ". iApply twp_lift_atomic_base_step_no_fork; first done.
  iIntros (σ1 ns κs nt) "(W & Hσ & Hκs & Hsteps) !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with base_step.
  iIntros (κ v2' σ2 efs Hstep); inv_base_step.
  rewrite bool_decide_true //.
  iMod (gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iModIntro. iSplit; first done. iSplit; first done. iFrame. by iApply "HΦ".
Qed.
Lemma wp_cmpxchg_suc W s E l v1 v2 v' :
  v' = v1 → vals_compare_safe v' v1 →
  {{{ ▷ l ↦ v' }}}[W] CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  {{{ RET PairV v' (LitV $ LitBool true); l ↦ v2 }}}.
Proof.
  iIntros (?? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_cmpxchg_suc with "H"); [by auto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_faa W s E l i1 i2 :
  [[{ l ↦ LitV (LitInt i1) }]][W] FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i2) @ s; E
  [[{ RET LitV (LitInt i1); l ↦ LitV (LitInt (i1 + i2)) }]].
Proof.
  iIntros (Φ) "Hl HΦ". iApply twp_lift_atomic_base_step_no_fork; first done.
  iIntros (σ1 ns κs nt) "(W & Hσ & Hκs & Hsteps) !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with base_step.
  iIntros (κ e2 σ2 efs Hstep); inv_base_step.
  iMod (gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iModIntro. do 2 (iSplit; first done). iFrame. by iApply "HΦ".
Qed.
Lemma wp_faa W s E l i1 i2 :
  {{{ ▷ l ↦ LitV (LitInt i1) }}}[W] FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i2) @ s; E
  {{{ RET LitV (LitInt i1); l ↦ LitV (LitInt (i1 + i2)) }}}.
Proof.
  iIntros (Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_faa with "H"); [by auto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma wp_new_proph W s E :
  {{{ True }}}[W]
    NewProph @ s; E
  {{{ pvs p, RET (LitV (LitProphecy p)); proph p pvs }}}.
Proof.
  iIntros (Φ) "_ HΦ". iApply wp_lift_atomic_base_step_no_fork; first done.
  iIntros (σ1 ns κ κs nt) "(W & Hσ & HR & Hsteps) !>". iSplit; first by eauto with base_step.
  iIntros "!>" (v2 σ2 efs Hstep) "_". inv_base_step.
  rename select proph_id into p.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iMod (proph_map_new_proph p with "HR") as "[HR Hp]"; first done.
  iModIntro; iSplit; first done. iFrame. by iApply "HΦ".
Qed.

(* In the following, strong atomicity is required due to the fact that [e] must
be able to make a head step for [Resolve e _ _] not to be (head) stuck. *)

Lemma resolve_reducible e σ (p : proph_id) v :
  Atomic StronglyAtomic e → reducible e σ →
  reducible (Resolve e (Val (LitV (LitProphecy p))) (Val v)) σ.
Proof.
  intros A (κ & e' & σ' & efs & H).
  exists (κ ++ [(p, (default v (to_val e'), v))]), e', σ', efs.
  eapply (Ectx_step []); try done.
  assert (∃w, Val w = e') as [w <-].
  { unfold Atomic in A. apply (A σ e' κ σ' efs) in H. unfold is_Some in H.
    destruct H as [w H]. exists w. simpl in H. by apply (of_to_val _ _ H). }
  simpl. constructor. by apply prim_step_to_val_is_base_step.
Qed.

Lemma step_resolve e vp vt σ1 κ e2 σ2 efs :
  Atomic StronglyAtomic e →
  prim_step (Resolve e (Val vp) (Val vt)) σ1 κ e2 σ2 efs →
  base_step (Resolve e (Val vp) (Val vt)) σ1 κ e2 σ2 efs.
Proof.
  intros A [Ks e1' e2' Hfill -> step]. simpl in *.
  induction Ks as [|K Ks _] using rev_ind.
  + simpl in *. subst. inv_base_step. by constructor.
  + rewrite fill_app /= in Hfill. destruct K; inversion Hfill; subst; clear Hfill.
    - rename select ectx_item into Ki.
      assert (fill_item Ki (fill Ks e1') = fill (Ks ++ [Ki]) e1') as Eq1;
        first by rewrite fill_app.
      assert (fill_item Ki (fill Ks e2') = fill (Ks ++ [Ki]) e2') as Eq2;
        first by rewrite fill_app.
      rewrite fill_app /=. rewrite Eq1 in A.
      assert (is_Some (to_val (fill (Ks ++ [Ki]) e2'))) as H.
      { apply (A σ1 _ κ σ2 efs). eapply (Ectx_step (Ks ++ [Ki])); done. }
      destruct H as [v H]. apply to_val_fill_some in H. by destruct H, Ks.
    - rename select (of_val vp = _) into Hvp.
      assert (to_val (fill Ks e1') = Some vp) as Hfillvp by rewrite -Hvp //.
      apply to_val_fill_some in Hfillvp as [-> ->]. inv_base_step.
    - rename select (of_val vt = _) into Hvt.
      assert (to_val (fill Ks e1') = Some vt) as Hfillvt by rewrite -Hvt //.
      apply to_val_fill_some in Hfillvt as [-> ->]. inv_base_step.
Qed.

Lemma wp_resolve W s E e Φ (p : proph_id) v (pvs : list (val * val)) :
  Atomic StronglyAtomic e →
  to_val e = None →
  proph p pvs -∗
  WP[W] e @ s; E {{ r, ∀ pvs', ⌜pvs = (r, v)::pvs'⌝ → proph p pvs' -∗ Φ r }} -∗
  WP[W] Resolve e (Val $ LitV $ LitProphecy p) (Val v) @ s; E {{ Φ }}.
Proof.
  (* TODO we should try to use a generic lifting lemma (and avoid [wp_unfold])
     here, since this breaks the WP abstraction. *)
  iIntros (A He) "Hp WPe". rewrite !wp_unfold /wp_pre /= He. simpl in *.
  iIntros (σ1 ns κ κs nt) "(W & Hσ & Hκ & Hsteps)".
  destruct κ as [|[p' [w' v']] κ' _] using rev_ind.
  - iMod ("WPe" $! σ1 ns [] κs nt with "[$W $Hσ $Hκ $Hsteps]") as "[Hs WPe]".
    iModIntro. iSplit.
    { iDestruct "Hs" as "%". iPureIntro. destruct s; [ by apply resolve_reducible | done]. }
    iIntros (e2 σ2 efs step). exfalso. apply step_resolve in step; last done.
    inv_base_step. match goal with H: ?κs ++ [_] = [] |- _ => by destruct κs end.
  - rewrite -assoc.
    iMod ("WPe" $! σ1 ns _ _ nt with "[$W $Hσ $Hκ $Hsteps]") as "[Hs WPe]". iModIntro. iSplit.
    { iDestruct "Hs" as %?. iPureIntro. destruct s; [ by apply resolve_reducible | done]. }
    iIntros (e2 σ2 efs step) "Hcred". apply step_resolve in step; last done.
    inv_base_step; simplify_list_eq.
    iMod ("WPe" $! (Val w') σ2 efs with "[%] Hcred") as "WPe".
    { by eexists [] _ _. }
    iModIntro. iNext. iMod "WPe" as "WPe". iModIntro.
    iApply (step_fupdN_wand with "WPe"); iIntros "> [($ & $ & Hκ & $) WPe]".
    iMod (proph_map_resolve_proph p' (w',v') κs with "[$Hκ $Hp]") as (vs' ->) "[$ HPost]".
    iModIntro. rewrite !wp_unfold /wp_pre /=. iDestruct "WPe" as "[HΦ $]".
    iMod "HΦ". iModIntro. by iApply "HΦ".
Qed.

Lemma twp_ndnat W s E :
  [[{ True }]][W] Ndnat @ s; E [[{ (n : nat), RET (LitV (LitInt n)); True }]].
Proof.
  iIntros (Φ) "_ HΦ". iApply twp_lift_atomic_base_step_no_fork; first done.
  iIntros (σ1 ns κs nt) "(W & Hσ & Hκs & Hsteps) !>".
  iSplit; [by auto with base_step|]. iIntros (κ v2 σ2 efs Hstep); inv_base_step.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iModIntro. do 2 (iSplit; [done|]). iFrame. by iApply "HΦ".
Qed.
Lemma wp_ndnat W s E :
  {{{ True }}}[W] Ndnat @ s; E {{{ (n : nat), RET (LitV (LitInt n)); True }}}.
Proof.
  iIntros (Φ) "_ HΦ". iApply (twp_wp_step with "HΦ").
  iApply twp_ndnat; [done|]. iIntros (n) "_ HΦ". by iApply "HΦ".
Qed.

End lifting.
