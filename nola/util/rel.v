(** * Utility for binary relations *)

From nola Require Import prelude util.pred.

(** ** Facts about well-founded relations *)
Section wf_facts.
  (** Take any well-founded relation [R] *)
  Context {A : Type} {R : A → A → Prop} (wfR : wf R).

  (** [R] is irreflexive *)
  Lemma wf_irrefl : Irreflexive R.
  Proof.
    move=> a aa. move: (wfR a). fix FIX 1=> Acca. apply FIX.
    exact (Acc_inv Acca aa).
  Qed.

  (** [R] is asymmetric *)
  Lemma wf_asymm : Asymmetric R.
  Proof.
    move=> a b. move: a (wfR a) b. fix FIX 2=> a Acca b ab ba.
    by apply (FIX b (Acc_inv Acca ba) a).
  Qed.
End wf_facts.
