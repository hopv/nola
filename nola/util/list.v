(** * Utility for [list] *)

From nola Require Export prelude.

(** ** Lemmas for [list], defined directly for computation *)

(** Reduce [++ []] *)
Fixpoint app_nil_def {A} {xs : list A} : xs ++ [] = xs :=
  match xs with
  | [] => eq_refl
  | _ :: _ => f_equal _ app_nil_def
  end.

(** Associativity of [++] *)
Fixpoint app_assoc_def {A} {xs ys zs : list A}
  : xs ++ (ys ++ zs) = (xs ++ ys) ++ zs :=
  match xs with
  | [] => eq_refl
  | _ :: _ => f_equal _ app_assoc_def
  end.

(** [take (length xs ++ i)] over [xs ++ ys] *)
Fixpoint take_add_app_def {A i} {xs ys : list A}
  : take (length xs + i) (xs ++ ys) = xs ++ take i ys :=
  match xs with
  | [] => eq_refl
  | _ :: _ => f_equal _ take_add_app_def
  end.

(** [drop (length xs ++ i)] over [xs ++ ys] *)
Fixpoint drop_add_app_def {A i} {xs ys : list A}
  : drop (length xs + i) (xs ++ ys) = drop i ys :=
  match xs with
  | [] => eq_refl
  | _ :: xs => drop_add_app_def (xs:=xs)
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

(** ** [schoice]: Variant choosing an element of [list] with a value *)

Inductive schoice {A} {F : A → Type} : list A → Type :=
| sbyhd {x} : F x → ∀ xs, schoice (x :: xs)
| sbytl {xs} : ∀ x, schoice xs → schoice (x :: xs).
Arguments schoice {A} F xs.

(** Utility patterns for [schoice] *)
Notation "#0 v" := (sbyhd v _) (at level 20, right associativity) : nola_scope.
Notation "+/ s" := (sbytl _ s) (at level 20, right associativity) : nola_scope.
Notation "#1 v" := (+/ #0 v) (at level 20, right associativity) : nola_scope.
Notation "#2 v" := (+/ #1 v) (at level 20, right associativity) : nola_scope.
Notation "#3 v" := (+/ #2 v) (at level 20, right associativity) : nola_scope.
Notation "#4 v" := (+/ #3 v) (at level 20, right associativity) : nola_scope.
Notation "#5 v" := (+/ #4 v) (at level 20, right associativity) : nola_scope.
Notation "#6 v" := (+/ #5 v) (at level 20, right associativity) : nola_scope.
Notation "#7 v" := (+/ #6 v) (at level 20, right associativity) : nola_scope.
Notation "#8 v" := (+/ #7 v) (at level 20, right associativity) : nola_scope.
Notation "#9 v" := (+/ #8 v) (at level 20, right associativity) : nola_scope.

(** Destruct [schoice F xs] with [xs = []] *)
Definition seqnil {A F R} {xs : list A} (s : schoice F xs) : xs = [] → R :=
  match s with
  | #0 _ => λ eq, match eq with end
  | +/ _ => λ eq, match eq with end
  end.

(** Turn [schoice F xs] into [schoice F (xs ++ ys)] *)
Fixpoint sbylapp {A F} {xs : list A} (s : schoice F xs) ys
  : schoice F (xs ++ ys) :=
  match s with
  | #0 v => #0 v
  | +/ s => +/ sbylapp s ys
  end.

(** Turn [schoice F ys] into [schoice F (xs ++ ys)] *)
Fixpoint sbyrapp {A F} xs {ys : list A} (s : schoice F ys)
  : schoice F (xs ++ ys) :=
  match xs with
  | [] => s
  | _ :: xs => +/ sbyrapp xs s
  end.

(** Decompose [schoice] with [take]/[drop] *)
Fixpoint stakedrop {A F} i {xs : list A} (s : schoice F xs)
  : schoice F (take i xs) + schoice F (drop i xs) :=
  match i, s with
  | 0, _ => inr s
  | S i, #0 v => inl (#0 v)
  | S i, +/ s => match stakedrop i s with
      inl s => inl (+/ s) | inr s => inr s end
  end.

(** Apply to a [schoice] a [plist] *)
Fixpoint spapply {A F G B} {xs : list A}
  (f : ∀ x, F x → G x → B) (s : schoice F xs) (vs : plist G xs) : B :=
  match s, vs with
  | #0 u, v -:: _ => f _ u v
  | +/ s, _ -:: vs => spapply f s vs
  end.

(** Let a function go inside [spapply] *)
Lemma spapply_in {A F G B C xs} {f : ∀ x, F x → G x → B} (g : B → C) {s vs} :
  g (spapply (A:=A) (xs:=xs) f s vs) = spapply (λ x u v, g (f x u v)) s vs.
Proof. move: xs s vs. by fix FIX 2=> ?[?|?]/=. Qed.
