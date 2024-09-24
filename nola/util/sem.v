(** * Semantics *)

From nola Require Export prelude.

(** ** [Sem]: Semantics *)
Class Sem (A B : Type) := sem : A → B.
Hint Mode Sem ! - : typeclass_instances.
Arguments sem {_ _ _} _ /.
Module SemNotation.
  Notation "⟦ ⟧" := (sem) (format "⟦ ⟧").
  Notation "⟦ ⟧@{ A }" := (sem (A:=A)) (only parsing).
  Notation "⟦ a ⟧" := (sem a) (format "⟦  '[' a  ']' ⟧").
  Notation "⟦ a ⟧@{ A }" := (sem (A:=A) a) (only parsing).
End SemNotation.

(** ** [Psem]: Parameterized semantics *)
Class Psem (X A B : Type) := psem : X → A → B.
Hint Mode Psem - ! - : typeclass_instances.
Arguments psem {_ _ _ _} _ _ /.
Module PsemNotation.
  Notation "⟦ ⟧( x )" := (psem x) (format "⟦ ⟧( x )").
  Notation "⟦ ⟧( x )@{ A }" := (psem (A:=A) x) (only parsing).
  Notation "⟦ a ⟧( x )" := (psem x a) (format "⟦  '[' a  ']' ⟧( x )").
  Notation "⟦ a ⟧( x )@{ A }" := (psem (A:=A) x a) (only parsing).
End PsemNotation.
