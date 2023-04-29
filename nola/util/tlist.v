(** * Utility for [tlist], [plist] and [csum] *)

From nola Require Export prelude.

(** ** [tlist]: List of elements in a higher universe
  It is almost the same as [list], but the element type can belong to
  a higher universe, which includes [list] itself. *)
Inductive tlist (T : Type) : Type :=
| tnil : tlist T
| tcons : T → tlist T → tlist T.

Arguments tnil {_}.
Arguments tcons {_} _ _.

Notation "^[]" := tnil : nola_scope.
Infix "^::" := tcons (at level 60, right associativity) : nola_scope.
Notation "^[ x ; .. ; z ]" := (x ^:: .. (z ^:: ^[]) ..)
  (at level 1, format "^[ x ;  .. ;  z ]") : nola_scope.

(** Wildcard patterns for [tlist] of n or more elements *)
Notation "^+1" := (_ ^:: _) (only parsing) : nola_scope.
Notation "^+2" := (_ ^:: ^+1) (only parsing) : nola_scope.
Notation "^+3" := (_ ^:: ^+2) (only parsing) : nola_scope.
Notation "^+4" := (_ ^:: ^+3) (only parsing) : nola_scope.
Notation "^+5" := (_ ^:: ^+4) (only parsing) : nola_scope.
Notation "^+6" := (_ ^:: ^+5) (only parsing) : nola_scope.
Notation "^+7" := (_ ^:: ^+6) (only parsing) : nola_scope.
Notation "^+8" := (_ ^:: ^+7) (only parsing) : nola_scope.
Notation "^+9" := (_ ^:: ^+8) (only parsing) : nola_scope.

(** Concatenate [tlist]s *)
Reserved Infix "^++" (at level 60, right associativity).
Fixpoint tapp {T} (ts us : tlist T) : tlist T :=
  match ts with
  | ^[] => us
  | t ^:: ts => t ^:: ts ^++ us
  end
where "ts ^++ us" := (tapp ts us) : nola_scope.

(** Map over [tlist] *)
Reserved Infix "^<$>" (at level 61, left associativity).
Fixpoint tmap {T U} (f : T → U) (ts : tlist T) : tlist U :=
  match ts with
  | ^[] => ^[]
  | t ^:: ts => f t ^:: (f ^<$> ts)
  end
where "f ^<$> ts" := (tmap f ts) : nola_scope.

#[export] Instance tlist_fmap : FMap tlist := λ _ _, tmap.

(** ** [tlength]: Length of a list *)

Fixpoint tlength {T} (ts : tlist T) : nat :=
  match ts with
  | ^[] => 0
  | _ ^:: ts => S (tlength ts)
  end.

(** ** [tinsert]: Insert an element to the i-th position of a list *)

Fixpoint tinsert {T} (u : T) (i : nat) (ts : tlist T) : tlist T :=
  match i, ts with
  | 0, _ => u ^:: ts
  | S i, t ^:: ts => t ^:: tinsert u i ts
  | S i, ^[] => ^[u]
  end.

(** Pull [_ ^++] out of [tinsert]

  We keep it computable to use it with [eq_rect] *)
Fixpoint tinsert_lapp {T} {v : T} {i ts us} :
  tinsert v (tlength ts + i) (ts ^++ us) = ts ^++ tinsert v i us :=
  match ts with
  | ^[] => eq_refl
  | _ ^:: _ => f_equal _ tinsert_lapp
  end.

(** Pull [^++ _] out of [tinsert]

  We keep it computable to use it with [eq_rect] *)
Fixpoint tinsert_rapp {T} {v : T} {i ts us} :
  tinsert v (tlength ts `min` i) (ts ^++ us) = tinsert v i ts ^++ us :=
  match ts with
  | ^[] => match i with 0 => eq_refl | S _ => eq_refl end
  | _ ^:: _ => match i with 0 => eq_refl | S _ => f_equal _ tinsert_rapp end
  end.

(** ** [plist]: Product type calculated over elements of [tlist] *)

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

(** [plist]: Heterogeneous list type calculated from [tlist] *)
Fixpoint plist {T} (F : T → Type) (ts : tlist T) : Type :=
  match ts with
  | ^[] => *[]
  | t ^:: ts => F t *:: plist F ts
  end.

(** Append [plist]s *)
Reserved Infix "-++" (at level 60, right associativity).
Fixpoint papp {T F} {ts us : tlist T}
  (xs : plist F ts) (ys : plist F us) : plist F (ts ^++ us) :=
  match ts, xs with
  | ^[], _ => ys
  | _ ^:: _, x -:: xs => x -:: xs -++ ys
  end
where "xs -++ ys" := (papp xs ys) : nola_scope.

(** Map over [plist] *)
Reserved Infix "-<$>" (at level 61, left associativity).
Fixpoint pmap {T} {F G : T → Type} (f : ∀ t, F t → G t) {ts : tlist T}
  (xs : plist F ts) : plist G ts :=
  match ts, xs with
  | ^[], -[] => -[]
  | _ ^:: _, x -:: xs => f _ x -:: (f -<$> xs)
  end
where "f -<$> xs" := (pmap f xs) : nola_scope.

(** ** [csum]: Variant choosing an element of [tlist] with a value *)

Inductive csum {T} {F : T → Type} : tlist T → Type :=
| cbyhd {t} : F t → ∀ ts, csum (t ^:: ts)
| cbytl {ts} : ∀t, csum ts → csum (t ^:: ts).
Arguments csum {T} F ts.

(** Utility patterns for [csum] *)
Notation "#0 a" := (cbyhd a _) (at level 20, right associativity) : nola_scope.
Notation "+/ s" := (cbytl _ s) (at level 20, right associativity) : nola_scope.
Notation "#1 a" := (+/ #0 a) (at level 20, right associativity) : nola_scope.
Notation "#2 a" := (+/ #1 a) (at level 20, right associativity) : nola_scope.
Notation "#3 a" := (+/ #2 a) (at level 20, right associativity) : nola_scope.
Notation "#4 a" := (+/ #3 a) (at level 20, right associativity) : nola_scope.
Notation "#5 a" := (+/ #4 a) (at level 20, right associativity) : nola_scope.
Notation "#6 a" := (+/ #5 a) (at level 20, right associativity) : nola_scope.
Notation "#7 a" := (+/ #6 a) (at level 20, right associativity) : nola_scope.
Notation "#8 a" := (+/ #7 a) (at level 20, right associativity) : nola_scope.
Notation "#9 a" := (+/ #8 a) (at level 20, right associativity) : nola_scope.

(** [csum F (t ^:: ts)] destructed *)
Variant csum' {T} {F : T → Type} (t : T) (ts : tlist T) :=
| cbyhd' : F t → csum' t ts
| cbytl' : csum F ts → csum' t ts.
Arguments csum' {T} F t ts.
Notation "#0' a" := (cbyhd' _ _ a) (at level 20, right associativity)
  : nola_scope.
Notation "+/' s" := (cbytl' _ _ s) (at level 20, right associativity)
  : nola_scope.

(** Destruct [csum F (t ^:: ts)] into [csum' F t ts] *)
Definition cdestr {T F} {t : T} {ts} (s : csum F (t ^:: ts)) : csum' F t ts :=
  match s with #0 a => #0' a | +/ s => +/' s end.

(** Insert an element to the list of [csum] *)
Fixpoint cinsert {T F} (u : T) (i : nat) {ts} (s : csum F ts)
  : csum F (tinsert u i ts) :=
  match i, s with
  | 0, #0 a => #1 a
  | S _, #0 a => #0 a
  | 0, +/ s => +/ +/ s
  | S i, +/ s => +/ cinsert u i s
  end.

(** Turn [csum F ts] into [csum F (ts ^++ us)] *)
Fixpoint cbylapp {T F} {ts : tlist T} (s : csum F ts) us : csum F (ts ^++ us) :=
  match s with
  | #0 a => #0 a
  | +/ s => +/ cbylapp s us
  end.

(** Turn [csum F us] into [csum F (ts ^++ us)] *)
Fixpoint cbyrapp {T F} ts {us : tlist T} (s : csum F us) : csum F (ts ^++ us) :=
  match ts with
  | ^[] => s
  | _ ^:: ts => +/ cbyrapp ts s
  end.

(** Apply a function of [plist] to a value of [csum] *)
Fixpoint pcapply {T F G} {A : Type} {ts : tlist T}
  (app : ∀ t, F t → G t → A) (xs : plist F ts) (s : csum G ts) : A :=
  match s, xs with
  | #0 a, x -:: _ => app _ x a
  | +/ s, _ -:: xs => pcapply app xs s
  end.

(** Map over [csum] *)
Reserved Infix "+<$>" (at level 61, left associativity).
Fixpoint cmap {T F G} (f : ∀ t, F t → G t) {ts : tlist T}
  (s : csum F ts) : csum G ts :=
  match ts, s with
  | ^[], _ => match s with end
  | _ ^:: _, #0 a => #0 f _ a
  | _ ^:: _, +/ s => +/ (f +<$> s)
  end
where "f +<$> s" := (cmap f s) : nola_scope.
