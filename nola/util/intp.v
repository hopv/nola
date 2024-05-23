(** * Interpretation *)

From nola Require Export prelude.

(** ** [Intp]: Interpretation *)
Class Intp (A B : Type) := intp : A → B.
Hint Mode Intp ! - : typeclass_instances.
Module IntpNotation.
  Notation "⟦ ⟧" := (intp) (format "⟦ ⟧").
  Notation "⟦ ⟧@{ A }" := (intp (A:=A)) (only parsing).
  Notation "⟦ a ⟧" := (intp a) (format "⟦  '[' a  ']' ⟧").
  Notation "⟦ a ⟧@{ A }" := (intp (A:=A) a) (only parsing).
End IntpNotation.

(** ** [Pintp]: Parameterized interpretation *)
Class Pintp (X A B : Type) := pintp : X → A → B.
Hint Mode Pintp - ! - : typeclass_instances.
Module PintpNotation.
  Notation "⟦ ⟧( x )" := (pintp x) (format "⟦ ⟧( x )").
  Notation "⟦ ⟧( x )@{ A }" := (pintp (A:=A) x) (only parsing).
  Notation "⟦ a ⟧( x )" := (pintp x a) (format "⟦  '[' a  ']' ⟧( x )").
  Notation "⟦ a ⟧( x )@{ A }" := (pintp (A:=A) x a) (only parsing).
End PintpNotation.
