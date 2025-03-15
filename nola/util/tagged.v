(** ** Tagged type *)

From nola Require Export prelude.
From iris.algebra Require Import ofe.

(** ** [tagged]: Type tagged with a ghost id *)
#[projections(primitive)]
Record tagged (ID : Type) (A : Type) : Type := Tagged { untag : A; }.
Add Printing Constructor tagged.
Arguments Tagged {_ _}. Arguments untag {_ _}.

(** OFE for [tagged] *)
Definition tagged_equiv {ID} {A : ofe} : relation (tagged ID A) :=
  λ '(Tagged a) '(Tagged a'), a ≡ a'.
Definition tagged_dist {ID} {A : ofe} n : relation (tagged ID A) :=
  λ '(Tagged a) '(Tagged a'), a ≡{n}≡ a'.
Program Canonical taggedO (ID : Type) (A : ofe) :=
  @Ofe (tagged ID A) tagged_equiv tagged_dist _.
Next Obligation.
  move=> ??. split=> >; [exact: equiv_dist| |exact: dist_lt].
  unfold dist, tagged_dist. split; [by move..|]=> ???. apply transitivity.
Qed.
(** [Tagged] is non-expansive *)
#[export] Instance tagged_ne {ID} {A : ofe} : NonExpansive (@Tagged ID A).
Proof. solve_proper. Qed.
#[export] Instance tagged_proper {ID} {A : ofe} :
  Proper ((≡) ==> (≡)) (@Tagged ID A).
Proof. solve_proper. Qed.
