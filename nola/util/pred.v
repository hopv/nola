(** * Utility for predicates *)

From nola Require Export prelude.

Definition True₁ {A} (_ : A) : Prop := True.
Arguments True₁ {_} _ /.

Definition False₁ {A} (_ : A) : Prop := False.
Arguments False₁ {_} _ /.

Definition and₁ {A} (φ ψ : A → Prop) (a : A) := φ a ∧ ψ a.
Arguments and₁ {_} _ _ _ /.
Infix "∧₁" := and₁ (at level 80, right associativity).

Definition or₁ {A} (φ ψ : A → Prop) (a : A) := φ a ∨ ψ a.
Arguments or₁ {_} _ _ _ /.
Infix "∨₁" := or₁ (at level 85, right associativity).
