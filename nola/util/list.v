(** * Utility for [list] *)

From nola Require Export prelude.

(** ** Lemmas for [list], defined directly for computation *)

(** Reduce [++ []] *)
Fixpoint app_nil_def {A} (xs : list A) : xs ++ [] = xs :=
  match xs with
  | [] => eq_refl
  | x :: xs => f_equal (cons x) (app_nil_def xs)
  end.

(** Associativity of [++] *)
Fixpoint app_assoc_def {A} (xs ys zs : list A)
  : xs ++ (ys ++ zs) = (xs ++ ys) ++ zs :=
  match xs with
  | [] => eq_refl
  | x :: xs => f_equal (cons x) (app_assoc_def xs ys zs)
  end.

(** [take (length xs ++ i)] over [xs ++ ys] *)
Fixpoint take_add_app_def {A} i (xs ys : list A)
  : take (length xs + i) (xs ++ ys) = xs ++ take i ys :=
  match xs with
  | [] => eq_refl
  | x :: xs => f_equal (cons x) (take_add_app_def i xs ys)
  end.

(** [drop (length xs ++ i)] over [xs ++ ys] *)
Fixpoint drop_add_app_def {A} i (xs ys : list A)
  : drop (length xs + i) (xs ++ ys) = drop i ys :=
  match xs with
  | [] => eq_refl
  | _ :: xs => drop_add_app_def i xs ys
  end.

(** ** [plist]: Product type calculated over elements of [list] *)

(** Unit type for [tnil] *)
Variant punit : Set := pnil.
(** Product type for [tcons] *)
#[projections(primitive)]
Record pprod (A B : Type) : Type := pcons { phd : A; ptl : B }.
Arguments pcons {_ _} _ _.
Arguments phd {_ _} _.
Arguments ptl {_ _} _.

Notation "*[ ]" := punit (at level 1, format "*[ ]") : nola_scope.
Infix "*::" := pprod (at level 60, right associativity) : nola_scope.
Notation "*[ A ; .. ; Z ]" := (A *:: .. (Z *:: *[]) ..)
  (at level 1, format "*[ A ;  .. ;  Z ]") : nola_scope.

Notation "-[ ]" := pnil (at level 1, format "-[ ]") : nola_scope.
Infix "-::" := pcons (at level 60, right associativity) : nola_scope.
Notation "-[ x ; .. ; z ]" := (x -:: .. (z -:: -[]) ..)
  (at level 1, format "-[ x ;  .. ;  z ]") : nola_scope.

(** [plist]: Heterogeneous list type calculated from [list] *)
Fixpoint plist {A} (F : A → Type) (xs : list A) : Type :=
  match xs with
  | [] => *[]
  | x :: xs => F x *:: plist F xs
  end.

(** ** [csum]: Variant choosing an element of [list] with a value *)

Inductive csum {A} {F : A → Type} : list A → Type :=
| cbyhd {x} : F x → ∀ xs, csum (x :: xs)
| cbytl {xs} : ∀ x, csum xs → csum (x :: xs).
Arguments csum {A} F xs.

(** Utility patterns for [csum] *)
Notation "#0 v" := (cbyhd v _) (at level 20, right associativity) : nola_scope.
Notation "+/ s" := (cbytl _ s) (at level 20, right associativity) : nola_scope.
Notation "#1 v" := (+/ #0 v) (at level 20, right associativity) : nola_scope.
Notation "#2 v" := (+/ #1 v) (at level 20, right associativity) : nola_scope.
Notation "#3 v" := (+/ #2 v) (at level 20, right associativity) : nola_scope.
Notation "#4 v" := (+/ #3 v) (at level 20, right associativity) : nola_scope.
Notation "#5 v" := (+/ #4 v) (at level 20, right associativity) : nola_scope.
Notation "#6 v" := (+/ #5 v) (at level 20, right associativity) : nola_scope.
Notation "#7 v" := (+/ #6 v) (at level 20, right associativity) : nola_scope.
Notation "#8 v" := (+/ #7 v) (at level 20, right associativity) : nola_scope.
Notation "#9 v" := (+/ #8 v) (at level 20, right associativity) : nola_scope.

(** Turn [csum F xs] into [csum F (xs ++ ys)] *)
Fixpoint cbylapp {A F} {xs : list A} (s : csum F xs) ys : csum F (xs ++ ys) :=
  match s with
  | #0 v => #0 v
  | +/ s => +/ cbylapp s ys
  end.

(** Turn [csum F ys] into [csum F (xs ++ ys)] *)
Fixpoint cbyrapp {A F} xs {ys : list A} (s : csum F ys) : csum F (xs ++ ys) :=
  match xs with
  | [] => s
  | _ :: xs => +/ cbyrapp xs s
  end.

(** Decompose [csum] with [take]/[drop] *)
Fixpoint ctakedrop {A F} i {xs : list A} (s : csum F xs)
  : csum F (take i xs) + csum F (drop i xs) :=
  match i, s with
  | 0, _ => inr s
  | S i, #0 v => inl (#0 v)
  | S i, +/ s => match ctakedrop i s with
      inl s => inl (+/ s) | inr s => inr s end
  end.

(** Apply to a [csum] a [plist] *)
Fixpoint cpapply {A F G B} {xs : list A}
  (f : ∀ x, F x → G x → B) (s : csum F xs) (vs : plist G xs) : B :=
  match s, vs with
  | #0 u, v -:: _ => f _ u v
  | +/ s, _ -:: vs => cpapply f s vs
  end.
