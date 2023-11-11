(** * Utility on [list] *)

From nola Require Export prelude.
From iris.algebra Require Import cmra.
From iris.base_logic Require Import own.
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
  Lemma own_big_cmra_opL_as `{!inG Σ C} {A} {γ al} (f : A → C) :
    own γ ([^op list] a ∈ al, f a) ⊣⊢
      own γ ε ∗ [∗ list] a ∈ al, own γ (f a).
  Proof.
    elim: al=>/=; [by rewrite right_id|]=> ?? IH. rewrite own_op IH !assoc.
    f_equiv. by rewrite comm.
  Qed.
  Lemma of_own_big_cmra_opL `{!inG Σ C} {A} {γ al} (f : A → C) :
    own γ ([^op list] a ∈ al, f a) ⊢ [∗ list] a ∈ al, own γ (f a).
  Proof. rewrite own_big_cmra_opL_as. by iIntros "[_$]". Qed.
  Lemma to_own_big_cmra_opL `{!inG Σ C} {A} {γ al} (f : A → C) :
    ([∗ list] a ∈ al, own γ (f a)) ⊢ |==> own γ ([^op list] a ∈ al, f a).
  Proof. rewrite own_big_cmra_opL_as. iMod own_unit as "$". by iIntros. Qed.
End big_cmra_opL.

(** ** On [[∗ list]] *)
Section big_sepL.
  Context {PROP : bi} {A : Type}.

  #[export] Instance big_sepL_mono'' :
    Proper (pointwise_relation _ (pointwise_relation _ (flip (⊢))) ==> (=) ==>
      flip (⊢)) (big_opL (@bi_sep PROP) (A:=A)).
  Proof. solve_proper. Qed.
End big_sepL.
