(** * Interpretation *)

From nola Require Export prelude.

(** Parameterized interpretation *)
Class Pintp (X A B : Type) := pintp : X → A → B.
Hint Mode Pintp - ! - : typeclass_instances.
Module PintpNotation.
  Notation "⟦ ⟧( x )" := (pintp x) (format "⟦ ⟧( x )").
  Notation "⟦ ⟧( x )@{ A }" := (pintp (A:=A) x) (only parsing).
  Notation "⟦ a ⟧( x )" := (pintp x a) (format "⟦  '[' a  ']' ⟧( x )").
  Notation "⟦ a ⟧( x )@{ A }" := (pintp (A:=A) x a) (only parsing).
End PintpNotation.
