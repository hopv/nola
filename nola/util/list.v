(** * Utility for [list] *)

From nola Require Export prelude.

(** ** Lemmas for [list] *)

(** Associativity of [++], defined directly for computation *)
Fixpoint app_assoc_def {A} (xs ys zs : list A)
  : xs ++ (ys ++ zs) = (xs ++ ys) ++ zs :=
  match xs with
  | [] => eq_refl
  | x :: xs => f_equal (cons x) (app_assoc_def xs ys zs)
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

(** Append [plist]s *)
Reserved Infix "-++" (at level 60, right associativity).
Fixpoint papp {A F} {xs ys : list A}
  (us : plist F xs) (vs : plist F ys) : plist F (xs ++ ys) :=
  match xs, us with
  | [], _ => vs
  | _ :: _, u -:: us => u -:: us -++ vs
  end
where "us -++ vs" := (papp us vs) : nola_scope.

(** Map over [plist] *)
Reserved Infix "-<$>" (at level 61, left associativity).
Fixpoint pmap {A} {F G : A → Type} (f : ∀ x, F x → G x) {xs : list A}
  (us : plist F xs) : plist G xs :=
  match xs, us with
  | [], -[] => -[]
  | _ :: _, u -:: us => f _ u -:: (f -<$> us)
  end
where "f -<$> us" := (pmap f us) : nola_scope.

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

(** Apply a function of [plist] to a value of [csum] *)
Fixpoint pcapply {A F G B} {xs : list A}
  (f : ∀ x, F x → G x → B) (vs : plist F xs) (s : csum G xs) : B :=
  match s, vs with
  | #0 w, v -:: _ => f _ v w
  | +/ s, _ -:: vs => pcapply f vs s
  end.

(** Map over [csum] *)
Reserved Infix "+<$>" (at level 61, left associativity).
Fixpoint cmap {A F G} (f : ∀ x, F x → G x) {xs : list A} (s : csum F xs)
  : csum G xs :=
  match xs, s with
  | [], _ => match s with end
  | _ :: _, #0 a => #0 f _ a
  | _ :: _, +/ s => +/ (f +<$> s)
  end
where "f +<$> s" := (cmap f s) : nola_scope.
