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

(** Type list *)
Notation Types := (tlist Type).

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

Notation "[*] t ∈ ts , A" := (plist (λ t, A) ts)
  (at level 200, ts at level 10, t binder, right associativity, only parsing)
  : nola_scope.

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

Inductive csum {T} (F : T → Type) : tlist T → Type :=
| cbyhd {t ts} : F t → csum F (t ^:: ts)
| cbytl {t ts} : csum F ts → csum F (t ^:: ts).
Arguments cbyhd {T F t ts} _.
Arguments cbytl {T F t ts} _.

Notation "[+] t ∈ ts , A" := (csum (λ t, A) ts)
  (at level 200, ts at level 10, t binder, right associativity, only parsing)
  : nola_scope.

(** Utility patterns for [csum] *)
Notation "#0 a" := (cbyhd a) (at level 20) : nola_scope.
Notation "+/ a" := (cbytl a) (at level 20, right associativity) : nola_scope.
Notation "#1 a" := (+/ #0 a) (at level 20) : nola_scope.
Notation "#2 a" := (+/ #1 a) (at level 20) : nola_scope.
Notation "#3 a" := (+/ #2 a) (at level 20) : nola_scope.
Notation "#4 a" := (+/ #3 a) (at level 20) : nola_scope.
Notation "#5 a" := (+/ #4 a) (at level 20) : nola_scope.
Notation "#6 a" := (+/ #5 a) (at level 20) : nola_scope.
Notation "#7 a" := (+/ #6 a) (at level 20) : nola_scope.
Notation "#8 a" := (+/ #7 a) (at level 20) : nola_scope.
Notation "#9 a" := (+/ #8 a) (at level 20) : nola_scope.

(** [csum] over [Types] *)
Notation tysum := (csum id).

(** [csum F (t ^:: ts)] destructed *)
Variant csum' {T} (F : T → Type) (t : T) (ts : tlist T) :=
| cbyhd' : F t → csum' F t ts
| cbytl' : csum F ts → csum' F t ts.
Arguments cbyhd' {T F t ts} _.
Arguments cbytl' {T F t ts} _.
Notation "#0' a" := (cbyhd' a) (at level 20) : nola_scope.
Notation "+/' a" := (cbytl' a) (at level 20, right associativity) : nola_scope.

(** Destruct [csum F (t ^:: ts)] into [csum' F t ts] *)
Definition cinv {T F} {t : T} {ts} (s : csum F (t ^:: ts)) : csum' F t ts :=
  match s with #0 a => #0' a | +/ s => +/' s end.

(** Lift [csum], inserting an element to the list *)
Fixpoint clift {T F} {ts us : tlist T} {t : T}
  : csum F (ts ^++ us) → csum F (ts ^++ t ^:: us) :=
  match ts with
  | ^[] => λ s, +/ s
  | _ ^:: _ => λ s, match cinv s with
    | #0' a => #0 a
    | +/' s => +/ clift s
    end
  end.

(** Turn [csum F ts] into [csum F (ts ^++ us)] *)
Fixpoint cbylapp {T F} {ts us : tlist T} (s : csum F ts) : csum F (ts ^++ us) :=
  match s with
  | #0 a => #0 a
  | +/ s => +/ cbylapp s
  end.

(** Turn [csum F us] into [csum F (ts ^++ us)] *)
Fixpoint cbyrapp {T F} {ts us : tlist T} (s : csum F us) : csum F (ts ^++ us) :=
  match ts with
  | ^[] => s
  | _ ^:: _ => +/ cbyrapp s
  end.

(** Apply a function of [plist] to a value of [csum] *)
Reserved Infix "-$+" (at level 20, no associativity).
Fixpoint pcapply {T F} {A : Type} {ts : tlist T}
  (fs : plist (λ t, F t → A) ts) (s : csum F ts) : A :=
  match s, fs with
  | #0 a, f -:: _ => f a
  | +/ s, _ -:: fs => fs -$+ s
  end
where "fs -$+ s" := (pcapply fs s) : nola_scope.

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
