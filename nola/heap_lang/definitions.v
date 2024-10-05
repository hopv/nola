(** Definitions (cut out from [primitive_laws] for better compilation) *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat.
From iris.base_logic.lib Require Export gen_heap proph_map gen_inv_heap.
From nola.bi Require Export wpw.
From nola.heap_lang Require Export class_instances.
Import ModwNotation WpwNotation.

Class heapGS_gen hlc Σ := HeapGS {
  heapGS_invGS :: invGS_gen hlc Σ;
  heapGS_gen_heapGS :: gen_heapGS loc (option val) Σ;
  heapGS_inv_heapGS :: inv_heapGS loc (option val) Σ;
  heapGS_proph_mapGS :: proph_mapGS proph_id (val * val) Σ;
  heapGS_step_name : gname;
  heapGS_step_cnt :: mono_natG Σ;
}.
Arguments HeapGS {_ _} _ _ _ _ _ _.

Section steps.
  Context `{!heapGS_gen hlc Σ}.

  Local Definition steps_auth (n : nat) : iProp Σ :=
    mono_nat_auth_own heapGS_step_name 1 n.

  Definition steps_lb (n : nat) : iProp Σ :=
    mono_nat_lb_own heapGS_step_name n.

  Lemma steps_lb_0 :
    ⊢ |==> steps_lb 0.
  Proof. by apply mono_nat_lb_own_0. Qed.

  Lemma steps_lb_valid n m :
    steps_auth n -∗ steps_lb m -∗ ⌜m ≤ n⌝.
  Proof.
    iIntros "Hauth Hlb".
    by iDestruct (mono_nat_lb_own_valid with "Hauth Hlb") as %[_ Hle].
  Qed.

  Lemma steps_lb_get n :
    steps_auth n -∗ steps_lb n.
  Proof. apply mono_nat_lb_own_get. Qed.

  Local Lemma steps_auth_update n n' :
    n ≤ n' → steps_auth n ==∗ steps_auth n' ∗ steps_lb n'.
  Proof. intros Hle. by apply mono_nat_own_update. Qed.

  Lemma steps_auth_update_S n :
    steps_auth n ==∗ steps_auth (S n).
  Proof.
    iIntros "Hauth".
    iMod (mono_nat_own_update with "Hauth") as "[$ _]"; [lia|done].
  Qed.

  Lemma steps_lb_le n n' :
    n' ≤ n → steps_lb n -∗ steps_lb n'.
  Proof. intros Hle. by iApply mono_nat_lb_own_le. Qed.
End steps.

(** Since we use an [option val] instance of [gen_heap], we need to overwrite
the notations.  That also helps for scopes and coercions. *)
Notation "l ↦ dq v" := (pointsto (L:=loc) (V:=option val) l dq (Some v%V))
  (at level 20, dq custom dfrac at level 1, format "l  ↦ dq  v") : bi_scope.

(** The [array] connective is a version of [pointsto] that works
with lists of values. *)

Definition array `{!heapGS_gen hlc Σ} (l : loc) (dq : dfrac) (vs : list val) : iProp Σ :=
  [∗ list] i ↦ v ∈ vs, (l +ₗ i) ↦{dq} v.

Notation "l ↦∗ dq vs" := (array l dq vs)
  (at level 20, dq custom dfrac  at level 1, format "l  ↦∗ dq  vs") : bi_scope.

(** Same for [gen_inv_heap], except that these are higher-order notations so to
make setoid rewriting in the predicate [I] work we need actual definitions
here. *)
Section definitions.
  Context `{!heapGS_gen hlc Σ}.
  Definition inv_pointsto_own (l : loc) (v : val) (I : val → Prop) : iProp Σ :=
    inv_pointsto_own l (Some v) (from_option I False).
  Definition inv_pointsto (l : loc) (I : val → Prop) : iProp Σ :=
    inv_pointsto l (from_option I False).
End definitions.

Global Instance: Params (@inv_pointsto_own) 4 := {}.
Global Instance: Params (@inv_pointsto) 3 := {}.

Notation inv_heap_inv := (inv_heap_inv loc (option val)).
Notation "l '↦_' I □" := (inv_pointsto l I%stdpp%type)
  (at level 20, I at level 9, format "l  '↦_' I  '□'") : bi_scope.
Notation "l ↦_ I v" := (inv_pointsto_own l v I%stdpp%type)
  (at level 20, I at level 9, format "l  ↦_ I  v") : bi_scope.

Global Program Instance heapGS_iris'GS `{!heapGS_gen hlc Σ} :
  iris'GS_gen hlc heap_ectxi_lang Σ := {
  iris'_invGS := heapGS_invGS;
  state_interp' σ step_cnt κs _ :=
    (gen_heap_interp σ.(heap) ∗ proph_map_interp κs σ.(used_proph_id) ∗
     steps_auth step_cnt)%I;
  fork_post' _ := True%I;
  num_laters_per_step' n := n;
}.
Next Obligation.
  iIntros "* ($&$& H)". iApply (steps_auth_update_S with "H").
Qed.

(** ** Helper instances
  TODO: Can we remove these? *)
Section instances.
  Context `{!heapGS_gen hlc Σ}.
  Let iris := heapGS_iris'GS.

  #[export] Instance elim_modal_fupdw_wpw
    `{!WsatIncl W W' Wr} {p e s E P Φ} :
    ElimModal (to_val e = None) p false (|=[W']{E}=> P) P
      (WP[W] e @ s; E {{ Φ }}) (WP[W] e @ s; E {{ Φ }}).
  Proof. exact elim_modal_fupdw_wpw. Qed.

  #[export] Instance elim_modal_fupdw_twpw
    `{!WsatIncl W W' Wr} {p e s E P Φ} :
    ElimModal (to_val e = None) p false (|=[W']{E}=> P) P
      (WP[W] e @ s; E [{ Φ }]) (WP[W] e @ s; E [{ Φ }]).
  Proof. exact elim_modal_fupdw_twpw. Qed.

  #[export] Instance elim_modal_fupdw_wpw_atomic {p e s E E' P Φ}
    `{!Atomic (stuckness_to_atomicity s) e, !WsatIncl W W' Wr} :
    ElimModal (to_val e = None) p false (|=[W']{E,E'}=> P) P
      (WP[W] e @ s; E {{ Φ }}) (WP[W] e @ s; E' {{ v, |=[W]{E',E}=> Φ v }})%I
    | 100.
  Proof. exact (elim_modal_fupdw_wpw_atomic (iris'GS_gen0:=iris)). Qed.

  #[export] Instance elim_modal_fupdw_twpw_atomic {p e s E E' P Φ}
    `{!Atomic (stuckness_to_atomicity s) e, !WsatIncl W W' Wr} :
    ElimModal (to_val e = None) p false (|=[W']{E,E'}=> P) P
      (WP[W] e @ s; E [{ Φ }]) (WP[W] e @ s; E' [{ v, |=[W]{E',E}=> Φ v }])%I
    | 100.
  Proof. exact (elim_modal_fupdw_twpw_atomic (iris'GS_gen0:=iris)). Qed.
End instances.
