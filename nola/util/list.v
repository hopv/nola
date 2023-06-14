(** * Utility for [list] *)

From nola Require Export prelude.

(** ** Lemmas for [list], defined directly for computation *)

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

(** ** [schoice]: Variant choosing an element of [list] with a value *)

Inductive schoice {A} {F : A → Type} : list A → Type :=
| sbyhd {x} : F x → ∀ xs, schoice (x :: xs)
| sbytl {xs} : ∀ x, schoice xs → schoice (x :: xs).
Arguments schoice {A} F xs.

(** Utility patterns for [schoice] *)
Notation "!0 v" := (sbyhd v _) (at level 20, right associativity) : nola_scope.
Notation "+! s" := (sbytl _ s) (at level 20, right associativity) : nola_scope.
Notation "!1 v" := (+! !0 v) (at level 20, right associativity) : nola_scope.
Notation "!2 v" := (+! !1 v) (at level 20, right associativity) : nola_scope.
Notation "!3 v" := (+! !2 v) (at level 20, right associativity) : nola_scope.
Notation "!4 v" := (+! !3 v) (at level 20, right associativity) : nola_scope.
Notation "!5 v" := (+! !4 v) (at level 20, right associativity) : nola_scope.
Notation "!6 v" := (+! !5 v) (at level 20, right associativity) : nola_scope.
Notation "!7 v" := (+! !6 v) (at level 20, right associativity) : nola_scope.
Notation "!8 v" := (+! !7 v) (at level 20, right associativity) : nola_scope.
Notation "!9 v" := (+! !8 v) (at level 20, right associativity) : nola_scope.

(** Destruct [schoice F xs] with [xs = []] *)
Definition seqnil {A F R} {xs : list A} (s : schoice F xs) : xs = [] → R :=
  match s with
  | !0 _ => λ eq, match eq with end
  | +! _ => λ eq, match eq with end
  end.

(** Turn [schoice F xs] into [schoice F (xs ++ ys)] *)
Fixpoint sbylapp {A F} {xs : list A} (s : schoice F xs) ys
  : schoice F (xs ++ ys) :=
  match s with
  | !0 v => !0 v
  | +! s => +! sbylapp s ys
  end.

(** Turn [schoice F ys] into [schoice F (xs ++ ys)] *)
Fixpoint sbyrapp {A F} xs {ys : list A} (s : schoice F ys)
  : schoice F (xs ++ ys) :=
  match xs with
  | [] => s
  | _ :: xs => +! sbyrapp xs s
  end.

(** Decompose [schoice F (x :: xs)] *)
Definition suncons' {A F} {xs : list A} (s : schoice F xs) :
  from_option F Empty_set (head xs) + schoice F (tail xs) :=
  match s with !0 v => inl v | +! s => inr s end.
Definition suncons {A F x} {xs : list A} (s : schoice F (x :: xs)) :
  F x + schoice F xs := suncons' s.

(** Decompose [schoice F [x]] *)
Definition sunsingl {A F} {x : A} (s : schoice F [x]) : F x :=
  match suncons s with inl v => v | inr s => match s with end end.

(** Decompose [schoice F (xs ++ ys)] *)
Fixpoint sunapp {A F} {xs ys : list A}
  : schoice F (xs ++ ys) → schoice F xs + schoice F ys :=
  match xs with
  | [] => λ s, inr s
  | _ :: _ => λ s, match suncons s with inl v => inl (!0 v) | inr s =>
      match sunapp s with inl s => inl (+! s) | inr s => inr s end end
  end.
