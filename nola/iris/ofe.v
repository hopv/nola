(** * Utility on OFEs *)

From nola Require Export prelude.
From iris.algebra Require Export ofe.

Notation "F $o x" := (oFunctor_apply F x) (at level 20, right associativity).
