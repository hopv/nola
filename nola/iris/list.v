(** * Utility for [list] *)

From nola Require Export prelude.
From iris.base_logic.lib Require Import own.
From iris.proofmode Require Import proofmode.

(** ** On [[^op list]] *)
Section big_cmra_opL.
  Context {C : ucmra}.

  (** For [∈] *)
  Lemma big_cmra_opL_included {A a al} (f : A → C) :
    a ∈ al → f a ≼ [^op list] a ∈ al, f a.
  Proof.
    elim: al=>/=. { by move=> /elem_of_nil. }
    move=> ?? IH /elem_of_cons[<-|/IH ?]; [done|]. by etrans.
  Qed.
  Lemma core_id_included_big_cmra_opL' {A al} (f : A → C)
    `{!∀ a, CoreId (f a)} {c} :
    Forall (λ a, f a ≼ c) al → c ≡ ([^op list] a ∈ al, f a) ⋅ c.
  Proof.
    elim: al=>/=. { move=> _. by rewrite left_id. }
    move=> ?? IH /Forall_cons[[cf eq] all]. rewrite -assoc -(IH all) eq assoc.
    by rewrite -core_id_dup.
  Qed.
  Lemma core_id_included_big_cmra_opL {A al} (f : A → C)
    `{!∀ a, CoreId (f a)} {c} :
    Forall (λ a, f a ≼ c) al → ([^op list] a ∈ al, f a) ≼ c.
  Proof. move=> /core_id_included_big_cmra_opL' ?. by exists c. Qed.

  (** [own] over [[^op list]] *)
  Lemma big_opL_own_2 `{!inG Σ C} {A} {γ al} (f : nat → A → C) :
    ([∗ list] k ↦ a ∈ al, own γ (f k a)) ⊢
      |==> own γ ([^op list] k ↦ a ∈ al, f k a).
  Proof.
    case al; [exact: own_unit|]=> ??. rewrite big_opL_own; by [iIntros|].
  Qed.
End big_cmra_opL.
