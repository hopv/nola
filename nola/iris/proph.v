(** * Prophecy *)

From nola.util Require Export proph.
From nola.util Require Import plist.
From nola.bi Require Import gmap.
From nola.iris Require Import own list option agree csum.
From iris.algebra Require Import gmap frac.
From iris.bi Require Import fractional.
From iris.base_logic.lib Require Import own.
From iris.proofmode Require Import proofmode.
Import EqNotations ProdNotation.

Implicit Type (TY : synty) (q : Qp).

(** ** Prophecy log *)

(** Prophecy log item *)
#[projections(primitive)]
Record proph_log_item TY := ProphLogItem {
  (* Prophecy variable *) pli_var : aprvar TY;
  (* Clairvoyant value *) pli_val : clair TY pli_var.(aprvar_ty);
}.
Arguments pli_var {_}. Arguments pli_val {_}.
Arguments ProphLogItem {_} _ _.
Local Notation ".{ ξ := aπ }" := (ProphLogItem ξ aπ) (format ".{ ξ  :=  aπ }").

(** Prophecy log *)
Local Notation proph_log TY := (list (proph_log_item TY)).

(** Prophecy variables of a prophecy log *)
Local Definition pl_vars {TY} (L : proph_log TY) : list (aprvar TY) :=
  pli_var <$> L.
(** Prophecy ids of a prophecy log *)
Local Definition pl_ids {TY} (L : proph_log TY) : gset positive :=
  list_to_set ((λ ξ, aprvar_id ξ) <$> pl_vars L).

(** Prophecy log item in a prophecy log *)

(** Prophecy dependency over the complement of a list set *)
Local Definition proph_dep_out {TY A}
  (aπ : clair TY A) (ξl : list (aprvar TY)) :=
  ∀ π π', proph_asn_eqv (.∉ ξl) π π' → aπ π = aπ π'.

(** Validity of a prophecy log *)
Local Fixpoint proph_log_valid {TY} (L : proph_log TY) :=
  match L with
  | [] => True
  | .{ξ := xπ} :: L' =>
      ξ ∉ pl_vars L' ∧ proph_dep_out xπ (pl_vars L) ∧ proph_log_valid L'
  end.
Local Notation ".✓ L" := (proph_log_valid L) (at level 20, format ".✓  L").

(** A prophecy assignment satisfying a prophecy log *)
Local Definition proph_sat {TY} (π : proph_asn TY) (L : proph_log TY) :=
  Forall (λ pli, π pli.(pli_var) = pli.(pli_val) π) L.
Local Notation "π ◁ L" := (proph_sat π L) (at level 70, format "π  ◁  L").

(** A prophecy assignment updated at a prophecy variable *)
Local Definition proph_upd {TY}
  (ξ : aprvar TY) (xπ : clair TY ξ.(aprvar_ty)) π : proph_asn TY := λ η,
  match decide (ξ = η) with
  | left eq => rew[aprvar_ty] eq in xπ π
  | right _ => π η
  end.
Local Notation ":<[ ξ := xπ ]>" := (proph_upd ξ xπ)
  (at level 5, format ":<[ ξ  :=  xπ ]>").

(** Applying [proph_upd] *)
Local Lemma proph_upd_self {TY} {π : proph_asn TY} {ξ xπ} :
  :<[ξ := xπ]> π ξ = xπ π.
Proof.
  unfold proph_upd. case: (decide (ξ = ξ)); [|done]=> eq.
  by rewrite (proof_irrel eq eq_refl).
Qed.
Local Lemma proph_upd_ne {TY} {π : proph_asn TY} {ξ xπ η} :
  ξ ≠ η → :<[ξ := xπ]> π η = π η.
Proof. unfold proph_upd. by case (decide (ξ = η)). Qed.

(** Prophecy assignment updated by a prophecy log *)
Local Fixpoint proph_upds {TY} L (π : proph_asn TY) :=
  match L with
  | [] => π
  | .{ξ := xπ} :: L' => proph_upds L' (:<[ξ := xπ]> π)
  end.
Local Notation ":<[ L ]>" := (proph_upds L) (at level 5, format ":<[ L ]>").

(** Equivalence out of [L] for [proph_upds] *)
Local Lemma proph_upds_eqv_out {TY} (L : proph_log TY) :
  ∀ π, proph_asn_eqv (.∉ pl_vars L) (:<[L]> π) π.
Proof.
  elim L=>/= [|[??]? IH]; [done|]=> > /not_elem_of_cons [??].
  rewrite IH; [|done]. by apply proph_upd_ne.
Qed.

(** [L] can by satisfied by [:<[L]>] for valid [L] *)
Local Lemma proph_valid_upds_sat {TY} {L : proph_log TY} :
  .✓ L → ∀ π, :<[L]> π ◁ L.
Proof.
  rewrite /proph_sat. elim: L=>/= [|[ξ xπ] L' IH]; [done|].
  move=> [?[? /IH ?]]?. apply Forall_cons=>/=. split; [|done].
  rewrite proph_upds_eqv_out; [|done]. rewrite proph_upd_self.
  set L := .{ξ := xπ} :: L'. have dep': proph_dep_out xπ (pl_vars L) by done.
  symmetry. apply dep', (proph_upds_eqv_out L).
Qed.
(** [L] can by satisfied for valid [L] *)
Local Lemma proph_valid_sat {TY} {L : proph_log TY} : .✓ L → ∃ π, π ◁ L.
Proof. exists (:<[L]> inhabitant). by apply proph_valid_upds_sat. Qed.

(** ** Prophecy resource algebra *)

(** Algebra for a prophecy variable *)
Local Definition proph_aitemR TY :=
  agreeR (leibnizO (anyty TY (λ A, clair TY A))).
Local Definition proph_itemR TY := csumR fracR (proph_aitemR TY).
(** Base algebra for the prophecy machinery *)
Local Definition proph_mapUR TY := gmapUR positive (proph_itemR TY).

(** Carrier of the algebra for the prophecy machinery *)
#[projections(primitive)]
Record proph_car TY := ProphCar { un_proph_car : proph_mapUR TY }.
Add Printing Constructor proph_car.
Arguments ProphCar {_}. Arguments un_proph_car {_}.

(** Equivalence *)
Local Instance proph_equiv_instance {TY} : Equiv (proph_car TY) :=
  λ '(ProphCar M) '(ProphCar M'), M ≡ M'.
Local Lemma proph_equiv {TY a a'} :
  (a ≡ a') = (a.(un_proph_car (TY:=TY)) ≡ a'.(un_proph_car)).
Proof. done. Qed.

(** Discrete [ofe] structure *)
Local Instance proph_equivalence {TY} : Equivalence (≡@{proph_car TY}).
Proof. split=> >; apply ofe_equivalence. Qed.
#[warning="-redundant-canonical-projection"]
Local Canonical prophO TY := discreteO (proph_car TY).

(** [ProphCar] and [un_proph_car] are proper *)
Local Instance ProphCar_proper {TY} : Proper ((≡) ==> (≡)) (ProphCar (TY:=TY)).
Proof. solve_proper. Qed.
Local Instance un_proph_car_proper {TY} :
  Proper ((≡) ==> (≡)) (un_proph_car (TY:=TY)).
Proof. solve_proper. Qed.

(** Core *)
Local Instance proph_pcore_instance {TY} : PCore (proph_car TY) :=
  λ '(ProphCar M), ProphCar <$> pcore M.
Local Lemma proph_pcore {TY a} :
  pcore a = ProphCar (TY:=TY) <$> pcore a.(un_proph_car).
Proof. done. Qed.
Local Lemma proph_core {TY a} :
  core a = ProphCar (TY:=TY) (core a.(un_proph_car)).
Proof. done. Qed.

(** Operation *)
Local Instance proph_op_instance {TY} : Op (proph_car TY) :=
  λ '(ProphCar M) '(ProphCar M'), ProphCar (M ⋅ M').
Local Lemma proph_op {TY a a'} :
  a ⋅ a' = ProphCar (TY:=TY) (a.(un_proph_car) ⋅ a'.(un_proph_car)).
Proof. done. Qed.
Local Lemma proph_included {TY a a'} :
  a ≼ a' ↔ a.(un_proph_car (TY:=TY)) ≼ a'.(un_proph_car).
Proof.
  unfold included=>/=. split.
  { move=> [[M]]. by exists M. } { move=> [M]. by exists (ProphCar M). }
Qed.
Local Lemma proph_included' {TY M M'} :
  M ≼ M' ↔ ProphCar (TY:=TY) M ≼ ProphCar M'.
Proof. by rewrite proph_included. Qed.

(** Fractional item *)
Local Definition fitem {TY} q : proph_itemR TY := Cinl q.
(** Agreement item *)
Local Definition aitem {TY X} xπ : proph_itemR TY :=
  Cinr (to_agree (Anyty X xπ)).

(** A prophecy map simulating a prophecy log *)
Local Definition proph_sim {TY} (M : proph_mapUR TY) L :=
  (∀ ξ, (∃ q, M !! aprvar_id ξ ≡ Some (fitem q)) → ξ ∉ pl_vars L) ∧
  (∀ ξ xπ, M !! aprvar_id ξ ≡ Some (aitem xπ) → .{ξ := xπ} ∈ L).
Local Notation "M :~ L" := (proph_sim M L) (at level 70, format "M  :~  L").

(** [proph_sim] is proper *)
Local Instance proph_sim_proper {TY} :
  Proper ((≡) ==> (=) ==> iff) (proph_sim (TY:=TY)).
Proof.
  have H (M M' : proph_mapUR TY) L : M ≡ M' → M :~ L → M' :~ L; last first.
  { move=> ?? eq ??<-. split; by apply H. }
  move=> eq [sim sim']. split.
  - move=> ?[q eq']. apply sim. exists q. by rewrite -eq'.
  - move=> ?? eq'. apply sim'. by rewrite -eq'.
Qed.

(** [proph_sim] is antitone over inclusion *)
Local Lemma proph_sim_op_l {TY M M'} {L : proph_log TY} :
  ✓ (M ⋅ M') → M ⋅ M' :~ L → M :~ L.
Proof.
  move=> val [sim sim']. split.
  - move=> ξ [q eq]. apply sim. move: (val ξ.(prvar_id)). rewrite lookup_op.
    setoid_rewrite eq. case: (M' !! ξ.(prvar_id)); last first.
    { move=> _. exists q. by rewrite right_id. }
    case; [|done..]=> q' _. by exists (q + q')%Qp.
  - move=> ξ xπ eq. apply sim'. move: (val ξ.(prvar_id)). rewrite lookup_op.
    setoid_rewrite eq. case: (M' !! ξ.(prvar_id)); [|by rewrite right_id].
    case; [done| |done]=> b /agree_op_inv <-.
    apply Some_proper, (Cinr_proper (B:=proph_aitemR TY)), agree_idemp.
Qed.
Local Lemma proph_sim_op_r {TY M M'} {L : proph_log TY} :
  ✓ (M ⋅ M') → M ⋅ M' :~ L → M' :~ L.
Proof. rewrite comm. exact proph_sim_op_l. Qed.

(** Validity *)
Local Instance proph_valid_instance {TY} : Valid (proph_car TY) :=
  λ '(ProphCar M), ✓ M ∧ ∃ L, M :~ L ∧ .✓ L.
Local Lemma proph_valid {TY a} :
  (✓ a) = (✓ a.(un_proph_car (TY:=TY)) ∧ ∃ L, a.(un_proph_car) :~ L ∧ .✓ L).
Proof. done. Qed.

(** Discrete [cmra] structure *)
Local Lemma proph_ra_mixin TY : RAMixin (proph_car TY).
Proof.
  split.
  - move=> ???. rewrite !proph_equiv. solve_proper.
  - move=> [?][?][?]. rewrite !proph_equiv !proph_pcore /=.
    move=> eq [<-]. eexists _. split; [done|]. solve_proper.
  - move=> [?][?]. rewrite proph_equiv !proph_valid /==> eq.
    f_equiv. { by rewrite eq. } do 3 f_equiv. by rewrite eq.
  - move=> [?][?][?]. rewrite !proph_op proph_equiv /=. apply assoc, _.
  - move=> [?][?]. rewrite !proph_op proph_equiv /=. apply comm, _.
  - move=> [?][?]. rewrite proph_pcore proph_op proph_equiv /==> [=<-].
    apply (cmra_core_l (A:=proph_mapUR TY)).
  - move=> [?][?]. rewrite !proph_pcore /==> [=<-]. do 2 f_equiv.
    apply (cmra_core_idemp (A:=proph_mapUR TY)).
  - move=> [M][M'][?]. rewrite proph_included proph_pcore /==> inc [=<-].
    exists (ProphCar (omap pcore M')). rewrite proph_included proph_pcore /=.
    split; [done|]. exact (cmra_core_mono _ _ inc).
  - move=> [M][M']. rewrite proph_op !proph_valid /=.
    move=> [val[L[[sim sim'] ?]]]. split. { by eapply cmra_valid_op_l. }
    exists L. split; [|done]. by eapply proph_sim_op_l.
Qed.
#[warning="-redundant-canonical-projection"]
Local Canonical prophR TY : cmra :=
  discreteR (proph_car TY) (proph_ra_mixin TY).
Local Instance prophR_discrete {TY} : CmraDiscrete (prophR TY).
Proof. apply discrete_cmra_discrete. Qed.

(** Unit *)
Local Instance proph_unit_instance {TY} : Unit (proph_car TY) := ProphCar ∅.
Local Lemma proph_unit {TY} : ε = ProphCar (TY:=TY) ∅. Proof. done. Qed.

(** [ucmra] structure *)
Local Lemma proph_ucmra_mixin TY : UcmraMixin (proph_car TY).
Proof.
  split.
  - split; [done|]. exists []. split; [|done].
    split; [move=> ?[?+]|move=> ??]; by rewrite lookup_empty=> /option_equiv'.
  - move=> [?]. by rewrite proph_unit proph_op proph_equiv /= left_id.
  - done.
Qed.
#[warning="-redundant-canonical-projection"]
Local Canonical prophUR TY : ucmra :=
  Ucmra (proph_car TY) (proph_ucmra_mixin TY).
Local Instance ProphCar_core_id {TY} `{!CoreId M} :
  CoreId (ProphCar (TY:=TY) M).
Proof. rewrite core_id_total proph_core. f_equiv. by apply core_id_total. Qed.

(** Item for observing [proph_log_item] *)
Local Definition pli_item {TY} (pli : proph_log_item TY) : proph_mapUR TY :=
  {[aprvar_id (pli_var pli) := aitem (TY:=TY) (pli_val pli)]}.
Local Instance pli_item_core_id {TY pli} :
  CoreId (pli_item (TY:=TY) pli).
Proof. rewrite core_id_total /=. by apply singleton_core'. Qed.

(** Ghost state *)
Class prophGS TY Σ := ProphGS {
  prophG_in : inG Σ (prophR TY);
  proph_name : gname;
}.
Local Existing Instance prophG_in.
Class prophGpreS TY Σ := prophGpreS_in : inG Σ (prophR TY).
Local Existing Instance prophGpreS_in.
Definition prophΣ TY := GFunctor (prophR TY).
#[export] Instance subG_prophPreG `{!subG (prophΣ TY) Σ} : prophGpreS TY Σ.
Proof. solve_inG. Qed.

(** ** Iris propositions *)

Section defs.
  Context `{!prophGS TY Σ}.
  Implicit Type (X : TY) (pli : proph_log_item TY).

  (** Prophecy token *)
  Local Definition proph_tok_def (ξ : aprvar TY) q : iProp Σ :=
    own proph_name (ProphCar {[ξ.(prvar_id) := fitem q]}).
  Lemma proph_tok_aux : seal proph_tok_def. Proof. by eexists. Qed.
  Definition proph_tok := proph_tok_aux.(unseal).
  Lemma proph_tok_unseal : proph_tok = proph_tok_def.
  Proof. exact: seal_eq. Qed.

  (** Prophecy observation *)
  Local Definition proph_obs_def (φπ : clair TY Prop) : iProp Σ :=
    ∃ L, ⌜∀ π, π ◁ L → φπ π⌝ ∧
      [∗ list] pli ∈ L, own proph_name (ProphCar (pli_item pli)).
  Lemma proph_obs_aux : seal proph_obs_def. Proof. by eexists. Qed.
  Definition proph_obs := proph_obs_aux.(unseal).
  Lemma proph_obs_unseal : proph_obs = proph_obs_def.
  Proof. exact: seal_eq. Qed.
End defs.

Notation proph_toks ξl q := ([∗ list] ξ ∈ ξl, proph_tok ξ q)%I (only parsing).
Module ProphNotation.
  Notation "q :[ ξ ]" := (proph_tok ξ q)
    (at level 2, left associativity, format "q :[ ξ ]") : bi_scope.
  Notation "q :∗[ ξl ]" := (proph_toks ξl q)
    (at level 2, left associativity, format "q :∗[ ξl ]") : bi_scope.
  Notation ".⟨ φπ ⟩" := (proph_obs φπ%type%stdpp) (at level 1, only parsing)
    : bi_scope.
  Notation "⟨ π , φ ⟩" := (proph_obs (λ π, φ%type%stdpp))
    (at level 1, format "⟨ π ,  φ ⟩") : bi_scope.
End ProphNotation.
Import ProphNotation.

(** ** Lemmas *)

(** Initialize [prophGS] *)
Lemma proph_init `{!prophGpreS TY Σ} :
  ⊢ |==> ∃ _ : prophGS TY Σ, True : iProp Σ.
Proof.
  iMod (own_alloc (ε : prophR TY)) as (γ) "_"; [exact ucmra_unit_valid|].
  by iExists (ProphGS _ _ _ γ).
Qed.

Section lemmas.
  Context `{!prophGS TY Σ}.
  Implicit Type (X : TY) (φπ ψπ : clair TY Prop) (φ ψ : Prop).

  (** [proph_tok] is timelesss and fractional *)
  #[export] Instance proph_tok_timeless {q ξ} : Timeless q:[ξ].
  Proof. rewrite proph_tok_unseal. exact _. Qed.
  #[export] Instance proph_tok_fractional {ξ} : Fractional (λ q, q:[ξ]%I).
  Proof.
    move=> ??.
    by rewrite proph_tok_unseal -own_op proph_op singleton_op -Cinl_op.
  Qed.
  #[export] Instance proph_tok_as_fractional {q ξ} :
    AsFractional q:[ξ] (λ q, q:[ξ]%I) q.
  Proof. split; by [|exact _]. Qed.
  #[export] Instance frame_proph_tok `{!FrameFractionalQp q r s} {p ξ} :
    Frame p q:[ξ] r:[ξ] s:[ξ] | 5.
  Proof. apply: frame_fractional. Qed.
  (** [proph_toks] is fractional *)
  #[export] Instance proph_toks_as_fractional {q ξl} :
    AsFractional q:∗[ξl] (λ q, q:∗[ξl]%I) q.
  Proof. split; by [|exact _]. Qed.
  #[export] Instance frame_proph_toks `{!FrameFractionalQp q r s} {p ξl} :
    Frame p q:∗[ξl] r:∗[ξl] s:∗[ξl] | 5.
  Proof. apply: (frame_fractional _ _ _ _ _ _ _ proph_toks_as_fractional). Qed.

  (** On [proph_toks] *)
  Lemma proph_toks_singleton {ξ q} : q:[ξ] ⊣⊢ q:∗[[ξ]].
  Proof. by rewrite /= right_id. Qed.
  Lemma proph_toks_combine {ξl ηl q r} :
    q:∗[ξl] -∗ r:∗[ηl] -∗ ∃ s,
      s:∗[ξl ++ ηl] ∗ (s:∗[ξl ++ ηl] -∗ q:∗[ξl] ∗ r:∗[ηl]).
  Proof.
    case: (Qp.lower_bound q r)=> [s[?[?[->->]]]]. iIntros "[ξl ξl'][ηl ηl']".
    iExists s. iFrame "ξl ηl ξl' ηl'". iIntros "[$$]".
  Qed.

  (** [proph_obs] is persistent, timeless and monotone *)
  #[export] Instance proph_obs_persistent {φπ} : Persistent .⟨φπ⟩.
  Proof. rewrite proph_obs_unseal. exact _. Qed.
  #[export] Instance proph_obs_timeless {φπ} : Timeless .⟨φπ⟩.
  Proof. rewrite proph_obs_unseal. exact _. Qed.
  #[export] Instance proph_obs_mono :
    Proper (pointwise_relation _ impl ==> (⊢)) proph_obs.
  Proof.
    move=> ?? imp. rewrite proph_obs_unseal /proph_obs_def. do 4 f_equiv.
    move=> imp' ??. by apply imp, imp'.
  Qed.
  #[export] Instance proph_obs_flip_mono :
    Proper (pointwise_relation _ (flip impl) ==> flip (⊢)) proph_obs.
  Proof. solve_proper. Qed.
  #[export] Instance proph_obs_proper :
    Proper (pointwise_relation _ (↔) ==> (⊣⊢)) proph_obs.
  Proof.
    move=>/= ?? iff. by apply bi.equiv_entails; split; f_equiv=> ? /iff.
  Qed.

  (** On [proph_obs] *)
  Lemma proph_obs_true {φπ} : (∀ π, φπ π) → ⊢ ⟨π, φπ π⟩.
  Proof. rewrite proph_obs_unseal=> ?. iExists []. by iSplit. Qed.
  Lemma proph_obs_and {φπ ψπ} : .⟨φπ⟩ -∗ .⟨ψπ⟩ -∗ ⟨π, φπ π ∧ ψπ π⟩.
  Proof.
    rewrite proph_obs_unseal. iIntros "[%L[%Toφπ L]] [%L'[%Toψπ L']]".
    iExists (L ++ L'). iFrame "L L'". iPureIntro=> ? /Forall_app[??].
    split; by [apply Toφπ|apply Toψπ].
  Qed.
  #[export] Instance proph_obs_combine {φπ ψπ} :
    CombineSepAs .⟨φπ⟩ .⟨ψπ⟩ ⟨π, φπ π ∧ ψπ π⟩.
  Proof. rewrite /CombineSepAs. iIntros "#[??]". by iApply proph_obs_and. Qed.
  Lemma proph_obs_impl {φπ ψπ} : (∀ π, φπ π → ψπ π) → .⟨φπ⟩ -∗ .⟨ψπ⟩.
  Proof. iIntros "% ?". iStopProof. by f_equiv. Qed.
  Lemma proph_obs_impl2 {φπ φπ' ψπ} :
    (∀ π, φπ π → φπ' π → ψπ π) → .⟨φπ⟩ -∗ .⟨φπ'⟩ -∗ .⟨ψπ⟩.
  Proof.
    iIntros "%imp obs obs'". iCombine "obs obs'" as "?". iStopProof.
    do 2 f_equiv. case. apply imp.
  Qed.

  (** Preliminaries for [proph_obs_forall] *)
  Local Definition proph_aitem_log_item (i : positive) (ai : proph_aitemR TY)
    : proph_log_item TY :=
    let: Anyty _ xπ := unagree ai in
    .{Prvar (synty_to_inhab (xπ inhabitant)) i := xπ}.
  Local Definition proph_item_log (p : positive * proph_itemR TY)
    : proph_log TY :=
    match p.2 with
    | Cinr ai => [proph_aitem_log_item p.1 ai]
    | _ => []
    end.
  Arguments proph_item_log _ /.
  Local Definition proph_map_log (M : proph_mapUR TY) : proph_log TY :=
    mjoin (proph_item_log <$> map_to_list M).
  Local Definition iRes_log (r : iResUR Σ) : proph_log TY :=
    match iRes_at (i:=prophG_in) proph_name r with
    | Some (ProphCar M) => proph_map_log M
    | None => []
    end.
  Local Lemma elem_of_proph_map_log {ξ xπ M} :
    .{ξ := xπ} ∈ proph_map_log M ↔
      ∃ ai : proph_aitemR TY, M !! aprvar_id ξ = Some (Cinr ai) ∧
        Anyty _ xπ = unagree ai.
  Proof.
    rewrite elem_of_list_join. split.
    - move=> [L[el /elem_of_list_fmap[[i it][? /elem_of_map_to_list eq]]]].
      subst. move: el eq. case: it=> [?|ai|]/=; try by move=>/elem_of_nil.
      move=> /elem_of_list_singleton. unfold proph_aitem_log_item=> ?.
      simplify_eq. by exists ai.
    - move=> [ai[/elem_of_map_to_list ? eq]]. exists [.{ξ := xπ}].
      split; [by apply elem_of_list_singleton|].
      apply elem_of_list_fmap. exists (aprvar_id ξ, Cinr ai)=>/=.
      split; [|done]. f_equal. rewrite /proph_aitem_log_item -eq. clear.
      move: ξ xπ=> [?[h ?]]?. by rewrite (proof_irrel (synty_to_inhab _) h).
  Qed.
  Local Lemma pli_item_included_1 {pli M} :
    ✓ M → pli_item pli ≼ M → pli ∈ proph_map_log M.
  Proof.
    case: pli=> ξ xπ. move=> val /lookup_included inc.
    apply elem_of_proph_map_log.
    move: {val}(val (aprvar_id ξ)) {inc}(inc (aprvar_id ξ)).
    rewrite /pli_item lookup_singleton.
    case eq: (M !! aprvar_id ξ)=> [it|]; last first.
    { by move=> _ /option_included'. }
    move=> + /option_included'. rewrite csum_equiv' csum_included' /=. move: eq.
    case: it; [by move=> ???[|]| |done]=> ai eq val inc. exists ai.
    split; [done|]. have {}val: ✓ (ai : agreeR (leibnizO _)) by done. case: inc.
    - move=> eqv. apply symmetry in eqv. by move: (unagree_equiv val eqv).
    - move=> inc. by move: (unagree_included val inc).
  Qed.
  Local Lemma pli_item_included_2 {pli M} :
    pli ∈ proph_map_log M → pli_item pli ≼ M.
  Proof.
    case: pli=> ξ xπ. move=> /elem_of_proph_map_log[ai[eq eq']].
    apply lookup_included=> i. rewrite /pli_item /=.
    case: (decide (aprvar_id ξ = i))=> ?; last first.
    { rewrite lookup_singleton_ne; [|done]. by apply option_included'. }
    subst. rewrite lookup_singleton eq. apply option_included'. right.
    apply csum_included'=>/=. rewrite eq'. exact to_agree_unagree.
  Qed.
  Local Lemma of_proph_obs_uPred_holds {n r φπ} :
    ✓{n} r → uPred_holds .⟨φπ⟩ n r → ∀ π, π ◁ iRes_log r → φπ π.
  Proof.
    rewrite proph_obs_unseal /proph_obs_def. uPred.unseal.
    move=> ? [L[toφ own]]. case: (decide (L = [])).
    { move=> ?? _. subst. apply toφ. by apply Forall_nil. }
    move=> ?? /Forall_forall toeq. apply toφ, Forall_forall. move=> pli inL.
    apply toeq. apply big_opL_own in own; [|done..].
    apply own_uPred_holds, cmra_discrete_included_iff in own. move: own.
    have: ✓ iRes_at (i:=prophG_in) proph_name r.
    { apply cmra_discrete_valid, iRes_at_validN.
      apply: cmra_validN_le; [done|lia]. }
    unfold iRes_log. case: (iRes_at (i:=prophG_in) proph_name r); last first.
    { rewrite option_included=> ?. case; [done|]. by move=> [?[?[_[? _]]]]. }
    move=> [M] val /Some_included_total ?. apply pli_item_included_1.
    { apply val. }
    apply proph_included'. etrans; [|done].
    by etrans; [|by apply: big_cmra_opL_included].
  Qed.
  Local Lemma to_proph_obs_uPred_holds {n r φπ} :
    ✓{n} r → (∀ π, π ◁ iRes_log r → φπ π) → uPred_holds .⟨φπ⟩ n r.
  Proof.
    rewrite proph_obs_unseal /proph_obs_def. uPred.unseal.
    move=> ? toφ. exists (iRes_log r). split; [done|]. unfold iRes_log.
    case eq: (iRes_at proph_name r)=> [[M]|]; [|simpl; by uPred.unseal].
    apply big_opL_own_1; [done|]. apply own_uPred_holds. rewrite eq.
    apply cmra_discrete_included_iff, Some_included_total.
    apply core_id_included_big_cmra_opL; [exact _|]. apply Forall_forall=> ??.
    by apply proph_included', pli_item_included_2.
  Qed.
  (** [∀] over [proph_obs] *)
  Lemma proph_obs_forall {A φπf} : (∀ a : A, .⟨φπf a⟩) ⊢ ⟨π, ∀ a, φπf a π⟩.
  Proof.
    uPred.unseal. split=> ?? val obs. apply (to_proph_obs_uPred_holds val).
    move=> ?? a. by apply (of_proph_obs_uPred_holds val (obs a)).
  Qed.

  (** Update of [proph_alloc] *)
  Local Lemma proph_alloc_upd :
    ε ~~>: (λ a : prophR TY, ∃ i, a = ProphCar {[i := fitem 1]}).
  Proof.
    apply cmra_discrete_total_updateP. case=> M. rewrite left_id /=.
    move=> [val[L[[sim sim'] ?]]]. set i := fresh (dom M ∪ pl_ids L).
    exists (ProphCar {[i := fitem 1]}). split; [by eexists _|]. split=>/=.
    - move=> j. rewrite lookup_op. case: (decide (j = i)).
      + move=> ->. rewrite lookup_singleton. have ->: M !! i = None; [|done].
        apply (not_elem_of_dom M), (not_elem_of_union _ _ (pl_ids L)), is_fresh.
      + move=> ?. rewrite lookup_singleton_ne; [|done]. by rewrite left_id.
    - exists L. split; [|done]. split.
      + move=> ξ [q +]. rewrite lookup_op. case: (decide (ξ.(prvar_id) = i)).
        * move=> eq _ /(elem_of_list_fmap_1 (λ ξ, aprvar_id ξ)). rewrite eq.
          eapply (not_elem_of_list_to_set (C:=gset _) i (_ <$> _)), proj2,
            not_elem_of_union, is_fresh.
        * move=> ?. rewrite lookup_singleton_ne; [|done]. rewrite left_id=> ?.
          apply sim. by exists q.
      + move=> ξ ?. rewrite lookup_op. case: (decide (ξ.(prvar_id) = i)).
        * move=> ->. rewrite lookup_singleton.
          case: (M !! i)=>/=; [case=> > eq|move=> eq]; apply (inj Some) in eq;
            inversion eq.
        * move=> ?. rewrite lookup_singleton_ne; [|done]. rewrite left_id.
          apply sim'.
  Qed.
  (** Allocate a new prophecy variable *)
  Lemma proph_alloc {X} : X → ⊢ |==> ∃ ξ : prvar X, 1:[ξ].
  Proof.
    move=> x. iMod (own_unit (prophUR TY) proph_name) as "ε".
    iMod (own_updateP with "ε") as "big"; [apply proph_alloc_upd|].
    iDestruct "big" as (?[i->]) "?". iExists (Prvar (synty_to_inhab x) i).
    by rewrite proph_tok_unseal.
  Qed.
  (** Allocate new prophecy variables *)
  Lemma proph_alloc_list {Xl} : plist synty_ty Xl →
    ⊢ |==> ∃ ξl : plist _ Xl, 1:∗[of_plist_prvar ξl].
  Proof.
    elim: Xl; [move=>/= ?; by iExists ()|]=>/= ?? IH [x xl].
    iMod (IH xl) as (ξl) "ξl". iMod (proph_alloc x) as (ξ) "ξ". iModIntro.
    iExists (ξ, ξl)'. iFrame.
  Qed.

  (** Simplify [[^op list]] over [ProphCar] *)
  Local Lemma big_cmra_opL_ProphCar {A al} (F : A → proph_mapUR TY) :
    un_proph_car ([^op list] a ∈ al, ProphCar (F a)) = ([^op list] a ∈ al, F a).
  Proof. by elim: al=>/=; [done|]=> ?? ->. Qed.

  (** Lemmas for [proph_resolve_dep_upd] *)
  Local Lemma aitem_no_fitem {X xπ q o} :
    Some (aitem (X:=X) xπ) ⋅ o ≡ Some (fitem q) → False.
  Proof.
    move=> eq. have: Some (aitem xπ) ≼ Some (fitem q) by eexists _.
    move=> /Some_included[eq'|[it +]]; [inversion eq'|].
    case it=> > eq'; inversion eq'.
  Qed.
  Local Lemma aitem_eq_agree {X xπ Y yπ o} :
    Some (aitem xπ) ⋅ o ≡ Some (aitem yπ) →
    Anyty (F:=λ A, _ → A) X xπ = Anyty Y yπ.
  Proof.
    move=> eq. have: Some (aitem xπ) ≼ Some (aitem yπ) by eexists _.
    move=> /Some_included[/Cinr_inj/to_agree_inj ?|[it ?]]; [done|].
    have: aitem xπ ≼ aitem yπ by eexists _.
    by move=> /Cinr_included/to_agree_included ?.
  Qed.
  (** Update of [proph_resolve_dep] *)
  Local Lemma proph_resolve_dep_upd {ηl ξ xπ q} : proph_dep xπ ηl →
    ProphCar {[aprvar_id ξ := fitem (TY:=TY) 1]} ⋅
    ([^op list] η ∈ ηl, ProphCar {[aprvar_id η := fitem q]}) ~~>
      ProphCar {[aprvar_id .{ξ := xπ}.(pli_var) := aitem .{ξ := xπ}.(pli_val)]}
        ⋅ ([^op list] η ∈ ηl, ProphCar {[aprvar_id η := fitem q]}).
  Proof.
    move=> dep. apply cmra_discrete_total_update. case=> M.
    rewrite !proph_valid /=. move=> [val[L[sim ?]]]. split.
    { move: val. rewrite -!assoc. apply cmra_discrete_total_update.
      by apply singleton_update, cmra_update_exclusive. }
    exists (.{ξ := xπ} :: L)=>/=. split.
    - move: val sim. rewrite -!assoc. move: (_ ⋅ M)=> M' val sim. split=>/=.
      + move=> ζ [r eq]. apply not_elem_of_cons. split.
        { move=> ?. subst. move: eq. rewrite lookup_op lookup_singleton.
          apply aitem_no_fitem. }
        apply sim. exists r. move: eq. rewrite !lookup_op.
        case: (decide (ζ.(prvar_id) = ξ.(prvar_id))).
        { move=> ->. by rewrite !lookup_singleton=> /aitem_no_fitem. }
        move=> ?. rewrite !lookup_singleton_ne; [|done..].
        by rewrite left_id=> ->.
      + move=> ζ yπ eq. apply elem_of_cons.
        case: (decide (ζ.(prvar_id) = ξ.(prvar_id))); last first.
        { move=> ?. right. apply sim. move: eq. rewrite !lookup_op.
          by rewrite !lookup_singleton_ne; [|done..]. }
        move=> eqi. move: eq. rewrite eqi lookup_op lookup_singleton.
        move=> /aitem_eq_agree. move: eqi. clear.
        move: ξ ζ xπ yπ=> [?[h ?]][?[h' ?]]/= ??. left. simplify_eq.
        by rewrite (proof_irrel h h').
    - apply (proph_sim_op_l val) in sim. apply cmra_valid_op_l in val.
      split; [|split; [|done]].
      { apply (proph_sim_op_l val) in sim. apply sim. exists 1%Qp.
        by rewrite lookup_singleton. }
      move=> ?? eqπ. apply dep=> η el. apply eqπ. apply not_elem_of_cons.
      move: val sim. rewrite big_cmra_opL_ProphCar.
      case: (big_cmra_opL_included (C:=proph_mapUR TY)
        (λ η, {[aprvar_id η := fitem q]}) el)=> [?->].
      rewrite assoc=> val /(proph_sim_op_l val) sim.
      apply cmra_valid_op_l in val. split.
      + move=> ?. subst. move: (val ξ.(prvar_id)). clear.
        rewrite lookup_op !lookup_singleton Some_valid Cinl_valid frac_valid.
        by eapply Qp.not_add_le_l.
      + apply (proph_sim_op_r val) in sim. apply sim. exists q.
        by rewrite lookup_singleton.
  Qed.
  (** Resolve a prophecy *)
  Lemma proph_resolve_dep ηl ξ xπ q : proph_dep xπ ηl →
    1:[ξ] -∗ q:∗[ηl] ==∗ q:∗[ηl] ∗ ⟨π, π ξ = xπ π⟩.
  Proof.
    iIntros (dep) "ξ ηl". rewrite proph_tok_unseal.
    iMod (big_opL_own_2 with "ηl") as "ηl". iCombine "ξ ηl" as "ξηl".
    iMod (own_update with "ξηl") as "big"; [apply (proph_resolve_dep_upd dep)|].
    iModIntro. iDestruct "big" as "[aobs ηl]". rewrite big_opL_own_1.
    iFrame "ηl". rewrite proph_obs_unseal. iExists [.{ξ := xπ}]. iFrame "aobs".
    iSplit; [|done]. by iPureIntro=> ? /Forall_singleton.
  Qed.
  Lemma proph_resolve ξ x : 1:[ξ] ==∗ ⟨π, π ξ = x⟩.
  Proof.
    iIntros "ξ".
    by iMod (proph_resolve_dep [] ξ (λ _, x) 1 with "ξ [//]") as "[_ $]".
  Qed.

  (** Get [proph_sat] out of [✓] over [aitem]s *)
  Local Lemma aitems_sat {L : proph_log TY} :
    ✓ ([^op list] pli ∈ L,
      ProphCar {[aprvar_id pli.(pli_var) := aitem pli.(pli_val)]}) →
    ∃ π, π ◁ L.
  Proof.
    move=> [val [L'[sim /proph_valid_sat[π /Forall_forall sat]]]]. exists π.
    apply Forall_forall. move=> [ξ xπ] el. apply sat, sim.
    move: (val ξ.(prvar_id)). rewrite big_cmra_opL_ProphCar.
    case: (big_cmra_opL_included (C:=proph_mapUR TY) (λ pli,
      {[aprvar_id pli.(pli_var) := aitem pli.(pli_val)]}) el)=> [M ->]=>/=.
    rewrite lookup_op lookup_singleton.
    case: (M !! ξ.(prvar_id)); [|by rewrite right_id]. case; [done| |done].
    move=> ? /Some_valid/Cinr_valid val'. apply Some_proper.
    apply (Cinr_proper (B:=proph_aitemR TY)). symmetry.
    by apply agree_valid_included.
  Qed.
  (** Get a satisfiability from a prophecy observation *)
  Lemma proph_obs_sat {φπ} : .⟨φπ⟩ ⊢ ⌜∃ π, φπ π⌝.
  Proof.
    rewrite proph_obs_unseal. iDestruct 1 as (L to) "aobss".
    iMod (big_opL_own_2 with "aobss") as "aitems".
    iDestruct (own_valid with "aitems") as %val. iPureIntro.
    move: val=> /aitems_sat[π sat]. exists π. by apply to.
  Qed.
  Lemma proph_obs_elim {φπ ψ} : (∀ π, φπ π → ψ) → .⟨φπ⟩ ⊢ ⌜ψ⌝.
  Proof. rewrite proph_obs_sat=> ?. iPureIntro. by case. Qed.
  Lemma proph_obs_const {φ} : .⟨λ _, φ⟩ ⊢ ⌜φ⌝.
  Proof. by apply proph_obs_elim. Qed.
End lemmas.
