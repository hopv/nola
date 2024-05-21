(** * Utility on [list] *)

From nola Require Export prelude.
From iris.algebra Require Import cmra.
From iris.base_logic.lib Require Import own.
From iris.proofmode Require Import proofmode.

(** ** On [[^op list]] *)
Section big_cmra_opL.
  Context {C : ucmra}.

  (** For [∈] *)
  Lemma big_cmra_opL_elem_of {A} {a al} (f : A → C) :
    a ∈ al → f a ≼ [^op list] a ∈ al, f a.
  Proof.
    elim: al=>/=. { by move=> /elem_of_nil. }
    move=> ?? IH /elem_of_cons[<-|/IH ?]; [done|]. by etrans.
  Qed.

  (** [own] on [[^op list]] *)
  Lemma big_opL_own_2 `{!inG Σ C} {A} {γ al} (f : nat → A → C) :
    ([∗ list] k ↦ a ∈ al, own γ (f k a)) ⊢
      |==> own γ ([^op list] k ↦ a ∈ al, f k a).
  Proof.
    case al; [by apply own_unit|]=> ??. rewrite big_opL_own; by [iIntros|].
  Qed.
End big_cmra_opL.
