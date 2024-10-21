(** * Paradox *)

From nola Require Export prelude.
From iris.base_logic Require Import base_logic.

(** ** Anti-adequacy for [∃ n : nat, ▷^n P], proved using the [uPred] model *)
Module exist_laterN_uPred. Section exist_laterN_uPred.
  Context {M : ucmra}.
  Implicit Type P : uPred M.

  (** Lemma for [exist_laterN] *)
  Lemma holds_laterN_S {x n P} : uPred_holds (▷^(S n) P) n x.
  Proof. unfold bi_laterN. elim: n; by uPred.unseal. Qed.

  (** Anti-adequacy for [∃ n : nat, ▷^n P], saying that a proposition weakened
    by unboundedly many laters trivially holds *)
  Lemma exist_laterN {P} : ⊢ ∃ n : nat, ▷^n P.
  Proof. uPred.unseal. split=> n ? _ _. exists (S n). exact holds_laterN_S. Qed.
End exist_laterN_uPred. End exist_laterN_uPred.
