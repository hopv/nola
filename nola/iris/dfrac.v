(** * Utility on [dfracR] *)

From nola Require Export prelude.
From iris.algebra Require Export dfrac.
From iris.algebra Require Import updates.

(** Restore a fraction out of a discarded token *)
Lemma dfrac_restore_update : DfracDiscarded ~~>: λ a, ∃ q, a = DfracOwn q.
Proof.
  move=> ?[[q||q]|]; setoid_rewrite <-cmra_discrete_valid_iff=>/=.
  - move=> /Qp.lt_sum[r eq]. exists (DfracOwn r).
    split; [by eexists _|]. apply dfrac_valid_own. by rewrite comm -eq.
  - move=> _. exists (DfracOwn (1/2)). split; by [eexists _|].
  - move=> /Qp.lt_sum[r eq]. exists (DfracOwn (r/2)).
    split; [by eexists _|]. apply dfrac_valid_own_discarded.
    rewrite comm eq. by apply Qp.add_lt_mono_l, Qp.div_lt.
  - move=> _. exists (DfracOwn 1). split; by [eexists _|].
Qed.