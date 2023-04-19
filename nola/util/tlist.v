(** * Utility for [tlist], [plist] and [csum] *)

From nola Require Import prelude.

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

(** ** [plist]: Product type calculated over elements of [tlist] *)

(** Unit type for [tnil] *)
Variant punit : Set := pnil.
(** Product type for [tcons] *)
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
  (at level 200, ts at level 10, t binder, right associativity) : nola_scope.

(** Append [plist]s *)
Reserved Infix "-++" (at level 60, right associativity).
Fixpoint papp {T} {F : T → Type} {ts us : tlist T}
  (xs : [*] t ∈ ts, F t) (ys : [*] t ∈ us, F t) : [*] t ∈ ts ^++ us, F t :=
  match ts, xs with
  | ^[], _ => ys
  | _ ^:: _, x -:: xs => x -:: xs -++ ys
  end
where "xs -++ ys" := (papp xs ys) : nola_scope.

(** Map over [plist] *)
Reserved Infix "-<$>" (at level 61, left associativity).
Fixpoint pmap {T} {F G : T → Type} (f : ∀ t, F t → G t) {ts : tlist T}
  (xs : [*] t ∈ ts, F t) : [*] t ∈ ts, G t :=
  match ts, xs with
  | ^[], -[] => -[]
  | _ ^:: _, x -:: xs => f _ x -:: (f -<$> xs)
  end
where "f -<$> xs" := (pmap f xs) : nola_scope.

(** ** [lsum]: Variant choosing an element of [tlist] with a value *)

Inductive lsum {T} (F : T → Type) : tlist T → Type :=
| cbyhd {t ts} : F t → lsum F (t ^:: ts)
| cbytl {t ts} : lsum F ts → lsum F (t ^:: ts).
Arguments cbyhd {T F t ts} _.
Arguments cbytl {T F t ts} _.

Notation "# x" := (cbyhd x)
  (at level 20, right associativity, format "#  x") : nola_scope.
Notation "+. x" := (cbytl x)
  (at level 20, right associativity, format "+. x") : nola_scope.
Notation "[+] t ∈ ts , A" := (lsum (λ t, A) ts)
  (at level 200, ts at level 10, t binder, right associativity) : nola_scope.

(** Lift [[+] t ∈ ts, F t] into [[+] t ∈ ts ^++ us, F t] *)
Fixpoint cbylapp {T} {F : T → Type} {ts us : tlist T}
  (x : [+] t ∈ ts, F t) : [+] t ∈ ts ^++ us, F t :=
  match x with
  | # x => # x
  | +. x => +. cbylapp x
  end.

(** Lift [[+] t ∈ us, F t] into [[+] t ∈ ts ^++ us, F t] *)
Fixpoint cbyrapp {T} {F : T → Type} {ts us : tlist T}
  (x : [+] t ∈ us, F t) : [+] t ∈ ts ^++ us, F t :=
  match ts with
  | ^[] => x
  | _ ^:: _ => +. cbyrapp x
  end.

(** Apply a function of [plist] to a value of [csum] *)
Reserved Infix "-$+" (at level 20, no associativity).
Fixpoint pcapply {T} {F : T → Type} {A : Type} {ts : tlist T}
  (fs : [*] t ∈ ts, F t → A) (x : [+] t ∈ ts, F t) : A :=
  match x, fs with
  | # x, f -:: _ => f x
  | +. x, _ -:: fs => fs -$+ x
  end
where "fs -$+ x" := (pcapply fs x) : nola_scope.

(** Map over [csum] *)
Reserved Infix "+<$>" (at level 61, left associativity).
Fixpoint cmap {T} {F G : T → Type} (f : ∀ t, F t → G t) {ts : tlist T}
  (x : [+] t ∈ ts, F t) : [+] t ∈ ts, G t :=
  match ts, x with
  | ^[], _ => match x with end
  | _ ^:: _, # x => # f _ x
  | _ ^:: _, +. x => +. (f +<$> x)
  end
where "f +<$> x" := (cmap f x) : nola_scope.
