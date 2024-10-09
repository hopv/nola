(** * Rust type basics *)

From nola.iris Require Export cif.
From nola.examples Require Export xty.

Implicit Type X : xty.

(** ** [ty]: Type *)
Definition ty CON Σ X := nat → cif CON Σ.
