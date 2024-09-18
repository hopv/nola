(** * Utility for functions *)

From nola Require Export prelude.
From iris.algebra Require Import ofe.

(** Map from [Empty_set] *)
Definition nullary {A} (e : Empty_set) : A := match e with end.
Arguments nullary {_} _ /.
(** Map from [unit] *)
Definition unary {A} (a : A) (_ : unit) : A := a.
Arguments unary {_} _ _ /.
(** Map from [bool] *)
Definition binary {A} (a a' : A) (b : bool) : A := if b then a else a'.
Arguments binary {_} _ _ _ /.

(** n-ary maps are non-expansive *)
#[export] Instance unary_ne {A : ofe} : NonExpansive (@unary A : _ → _ -d> _).
Proof. solve_proper. Qed.
#[export] Instance unary_proper {A : ofe} :
  Proper ((≡) ==> (≡)) (@unary A : _ → _ -d> _).
Proof. apply ne_proper, _. Qed.
#[export] Instance binary_ne {A : ofe} :
  NonExpansive2 (@binary A : _ → _ → _ -d> _).
Proof. solve_proper. Qed.
#[export] Instance binary_proper {A : ofe} :
  Proper ((≡) ==> (≡) ==> (≡)) (@binary A : _ → _ → _ -d> _).
Proof. apply ne_proper_2, _. Qed.
(** n-ary maps preserve discreteness *)
#[export] Instance nullary_discrete {A : ofe} {e} : Discrete (@nullary A e).
Proof. by case: e. Qed.
#[export] Instance unary_discrete {A : ofe} {u} `{!Discrete a} :
  Discrete (@unary A a u).
Proof. by case: u. Qed.
#[export] Instance binary_discrete {A : ofe} {b}
  `{!Discrete a, !Discrete a'} : Discrete (@binary A a a' b).
Proof. by case: b. Qed.
