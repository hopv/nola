(** * Prelude *)

From iris.prelude Require Export prelude.

(** Admit Streicher's Axiom K *)
From Coq Require Export Program.Equality.
Export EqNotations.

(** Admit functional extensionality *)
From Coq Require Export FunctionalExtensionality.

(** ** Utility for functional extensionality *)

Ltac fun_ext := apply functional_extensionality.
Ltac fun_ext_dep := apply functional_extensionality_dep.
