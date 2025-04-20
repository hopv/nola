(** * N-ary maps *)

From nola Require Export prelude.
From nola.util Require Import productive.
Import ProeqvNotation.

Implicit Type SI : sidx.

(** Nullary map *)
Definition nullary {SI} {A : ofe} : Empty_set -d> A := λ e, match e with end.
Arguments nullary {_ _} _ /.
(** Unary map *)
Definition unary {SI} {A : ofe} (a : A) : unit -d> A := λ _, a.
Arguments unary {_ _} _ _ /.
(** Binary map *)
Definition binary {SI} {A : ofe} (a a' : A) : bool -d> A :=
  λ b, if b then a else a'.
Arguments binary {_ _} _ _ _ /.

Section nary.
  Context {SI}.

  (** N-ary maps are non-expansive *)
  #[export] Instance unary_ne {A} : NonExpansive (unary (A:=A)).
  Proof. solve_proper. Qed.
  #[export] Instance unary_proper {A} : Proper ((≡) ==> (≡)) (unary (A:=A)).
  Proof. apply ne_proper, _. Qed.
  #[export] Instance binary_ne {A} : NonExpansive2 (binary (A:=A)).
  Proof. solve_proper. Qed.
  #[export] Instance binary_proper {A} :
    Proper ((≡) ==> (≡) ==> (≡)) (binary (A:=A)).
  Proof. apply ne_proper_2, _. Qed.
  (** N-ary maps preserve discreteness *)
  #[export] Instance nullary_discrete {A e} : Discrete (nullary (A:=A) e).
  Proof. by case: e. Qed.
  #[export] Instance unary_discrete {A u} `{!Discrete a} :
    Discrete (unary (A:=A) a u).
  Proof. by case: u. Qed.
  #[export] Instance binary_discrete {A b} `{!Discrete a, !Discrete a'} :
    Discrete (binary (A:=A) a a' b).
  Proof. by case: b. Qed.

  (** N-ary maps are size-preserving *)
  #[export] Instance unary_preserv {A : prost} : Preserv' _ _ (unary (A:=A)).
  Proof. solve_proper. Qed.
  #[export] Instance binary_preserv {A : prost} {k} :
    Proper ((≡[k]≡) ==> (≡[k]≡) ==> (≡[k]≡)) (binary (A:=A)).
  Proof. solve_proper. Qed.
End nary.
