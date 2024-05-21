(** * On relations *)

From nola Require Export prelude.

(** Relation composition *)
Definition rcompose {A B C} (R : A → B → Prop) (R' : B → C → Prop) a c : Prop :=
  ∃ b, R a b ∧ R' b c.
