(** * Utility for [list] *)

From nola Require Export prelude.

(** ** Equalities for [list], defined directly for computation *)

(** Reduce [++ []] *)
Fixpoint app_nil_d {A} {xs : list A} : xs ++ [] = xs :=
  match xs with
  | [] => eq_refl
  | _ :: _ => f_equal _ app_nil_d
  end.
Definition app_nil'_d {A} {xs : list A} : xs = xs ++ [] := eq_sym app_nil_d.
Definition app_eq_nil_d {A} {xs ys : list A} (eq : ys = []) : xs ++ ys = xs :=
  eq_trans (f_equal (_ ++.) eq) app_nil_d.

(** Associativity of [++] *)
Fixpoint app_assoc_d {A} {xs ys zs : list A}
  : xs ++ (ys ++ zs) = (xs ++ ys) ++ zs :=
  match xs with
  | [] => eq_refl
  | _ :: _ => f_equal _ app_assoc_d
  end.
