From stdpp Require Import base.

Declare Scope noix_scope.
Delimit Scope noix_scope with Nx.

(** Noix Proposition *)
Inductive nProp : Type :=
| Sep : nProp → nProp → nProp
| Forall (A : Type) : (A → nProp) → nProp.
Bind Scope noix_scope with nProp.

Notation "P ∗ Q" := (Sep P Q)%Nx
  (at level 80, right associativity, format "P  ∗  '/' Q") : noix_scope.

Definition from_Empty_set {A : Type} (x : Empty_set) : A := match x with end.
Notation "'True'" := (Forall Empty_set from_Empty_set)%Nx : noix_scope.

Check (True ∗ True)%Nx.
