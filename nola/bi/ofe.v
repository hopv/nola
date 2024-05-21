(** * Utility on OFEs *)

From nola Require Export prelude.
From iris.bi Require Import bi.

Implicit Type PROP : bi.

(** ** [laterl]: [▷] on [later PROP] *)
Definition laterl {PROP} (P : later PROP) : PROP := ▷ later_car P.
Arguments laterl {_} _ /.

(** [laterl] is non-expansive if [▷] is contractive *)
#[export] Instance laterl_ne `{!BiLaterContractive PROP} :
  NonExpansive (@laterl PROP).
Proof. move=> ?[?][?]?/=. by apply later_contractive. Qed.
