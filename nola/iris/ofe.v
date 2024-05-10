(** * Utility on OFEs *)

From nola Require Export prelude.
From iris.algebra Require Export ofe cmra.

Module OfeNotation.
  Notation "F $o x" := (oFunctor_apply F x) (at level 20, right associativity).
  Notation "F $r x" := (rFunctor_apply F x) (at level 20, right associativity).
End OfeNotation.
