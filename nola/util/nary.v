(** * N-ary maps *)

From nola Require Export prelude.
From nola Require Import productive.
Import ProeqvNotation.

Implicit Type A : ofe.

(** Nullary map *)
Definition nullary {A} : Empty_set -d> A := λ e, match e with end.
Arguments nullary {_} _ /.
(** Unary map *)
Definition unary {A} (a : A) : unit -d> A := λ _, a.
Arguments unary {_} _ _ /.
(** Binary map *)
Definition binary {A} (a a' : A) : bool -d> A := λ b, if b then a else a'.
Arguments binary {_} _ _ _ /.

(** N-ary maps are non-expansive *)
#[export] Instance unary_ne {A} : NonExpansive (@unary A).
Proof. solve_proper. Qed.
#[export] Instance unary_proper {A} : Proper ((≡) ==> (≡)) (@unary A).
Proof. apply ne_proper, _. Qed.
#[export] Instance binary_ne {A} : NonExpansive2 (@binary A).
Proof. solve_proper. Qed.
#[export] Instance binary_proper {A} : Proper ((≡) ==> (≡) ==> (≡)) (@binary A).
Proof. apply ne_proper_2, _. Qed.
(** N-ary maps preserve discreteness *)
#[export] Instance nullary_discrete {A e} : Discrete (@nullary A e).
Proof. by case: e. Qed.
#[export] Instance unary_discrete {A u} `{!Discrete a} :
  Discrete (@unary A a u).
Proof. by case: u. Qed.
#[export] Instance binary_discrete {A b} `{!Discrete a, !Discrete a'} :
  Discrete (@binary A a a' b).
Proof. by case: b. Qed.

(** N-ary maps are size-preserving *)
#[export] Instance unary_preserv {A : prost} : Preserv' _ _ (@unary A).
Proof. solve_proper. Qed.
#[export] Instance binary_preserv {A : prost} {k} :
  Proper ((≡[k]≡) ==> (≡[k]≡) ==> (≡[k]≡)) (@binary A).
Proof. solve_proper. Qed.
