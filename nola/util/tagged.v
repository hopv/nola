(** ** Tagged type *)

From nola Require Export prelude.
From iris.algebra Require Import ofe.

(** ** [tagged]: Type tagged with a ghost id *)
#[projections(primitive)]
Record tagged (Id : Type) (A : Type) := Tagged { untag : A; }.
Add Printing Constructor tagged.
Arguments Tagged {_ _}. Arguments untag {_ _}.

(** OFE for [tagged] *)
Definition tagged_equiv {Id} {A : ofe} : relation (tagged Id A) :=
  λ '(Tagged a) '(Tagged a'), a ≡ a'.
Definition tagged_dist {Id} {A : ofe} n : relation (tagged Id A) :=
  λ '(Tagged a) '(Tagged a'), a ≡{n}≡ a'.
Program Canonical taggedO (Id : Type) (A : ofe) :=
  @Ofe (tagged Id A) tagged_equiv tagged_dist _.
Next Obligation.
  move=> ??. split=> >; [by apply equiv_dist| |by apply dist_lt].
  unfold dist, tagged_dist. split; [by move..|]=> ???. apply transitivity.
Qed.
(** [Tagged] is non-expansive *)
#[export] Instance tagged_ne {Id} {A : ofe} : NonExpansive (@Tagged Id A).
Proof. solve_proper. Qed.
#[export] Instance tagged_proper {Id} {A : ofe} :
  Proper ((≡) ==> (≡)) (@Tagged Id A).
Proof. solve_proper. Qed.
