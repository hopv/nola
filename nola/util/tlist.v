(** * Utility for [tlist], [clist] and [cchoice] *)

From nola Require Import prelude.

(** ** [tlist]: List of elements in a higher universe
  It is almost the same as [list], but the element type can belong to
  a higher universe, which includes [list] itself. *)
Inductive tlist (T : Type) : Type :=
| tnil : tlist T
| tcons : T -> tlist T -> tlist T.

Arguments tnil {_}.
Arguments tcons {_} _ _.

Notation "^[]" := tnil.
Infix "^::" := tcons (at level 60, right associativity).
Notation "^[ x ; .. ; z ]" := (x ^:: .. (z ^:: ^[]) ..)
  (at level 1, format "^[ x ;  .. ;  z ]").

(** Concatenate [tlist]s *)
Reserved Infix "^++" (at level 60, right associativity).
Fixpoint tapp {T} (ts us : tlist T) : tlist T :=
  match ts with
  | ^[] => us
  | t ^:: ts => t ^:: ts ^++ us
  end
where "ts ^++ us" := (tapp ts us).

(** ** [clist]: Heterogeneous list type calculated from [tlist] *)

(** Unit type for [tnil] *)
Variant cunit : Set := cnil.
(** Product type for [tcons] *)
Record cprod (A B : Type) : Type := ccons { chd : A; ctl : B }.
Arguments ccons {_ _} _ _.
Arguments chd {_ _} _.
Arguments ctl {_ _} _.

Notation "*[ ]" := cunit (at level 1, format "*[ ]") : type_scope.
Infix "*::" := cprod (at level 60, right associativity) : type_scope.
Notation "*[ A ; .. ; Z ]" := (A *:: .. (Z *:: *[]) ..)
  (at level 1, format "*[ A ;  .. ;  Z ]") : type_scope.

Notation "-[ ]" := cnil (at level 1, format "-[ ]").
Infix "-::" := ccons (at level 60, right associativity).
Notation "-[ x ; .. ; z ]" := (x -:: .. (z -:: -[]) ..)
  (at level 1, format "-[ x ;  .. ;  z ]").

(** [clist]: Heterogeneous list type calculated from [tlist] *)
Fixpoint clist {T} (F : T → Type) (ts : tlist T) : Type :=
  match ts with
  | ^[] => *[]
  | t ^:: ts => F t *:: clist F ts
  end.

Notation "[*] t ∈ ts , A" := (clist (λ t, A) ts)
  (at level 200, ts at level 10, t binder, right associativity,
    format "[*]  t  ∈  ts ,  A").

(** Append [clist]s *)
Reserved Infix "-++" (at level 60, right associativity).
Fixpoint capp {T} {F : T → Type} {ts us : tlist T}
  (xs : [*] t ∈ ts , F t) (ys : [*] t ∈ us , F t) : [*] t ∈ ts ^++ us , F t :=
  match ts, xs with
  | ^[], _ => ys
  | _ ^:: _, x -:: xs => x -:: xs -++ ys
  end
where "xs -++ ys" := (capp xs ys).

(** ** [cchoice]: Sum type calculated from [tlist] *)

(** Empty type for [tnil] *)
Variant cempty : Set := .
(** Sum type for [tcons] *)
Variant csum (A B : Type) : Type := cbyhd (_ : A) | cbytl (_ : B).
Arguments cbyhd {_ _} _.
Arguments cbytl {_ _} _.

Notation "+[ ]" := cempty (at level 1, format "+[ ]") : type_scope.
Infix "+::" := csum (at level 60, right associativity) : type_scope.
Notation "+[ A ; .. ; Z ]" := (A +:: .. (Z +:: +[]) ..)
  (at level 1, format "+[ A ;  .. ;  Z ]") : type_scope.

Notation "-# x" := (cbyhd x)
  (at level 20, right associativity, format "-#  x").
Notation "-/ x" := (cbytl x)
  (at level 20, right associativity, format "-/ x").

(** [cchoice]: Sum type calculated from [tlist] *)
Fixpoint cchoice {T} (F : T → Type) (ts : tlist T) : Type :=
  match ts with
  | ^[] => +[]
  | t ^:: ts => F t +:: cchoice F ts
  end.

Notation "[+] t ∈ ts , A" := (cchoice (λ t, A) ts)
  (at level 200, ts at level 10, t binder, right associativity,
    format "[+]  t  ∈  ts ,  A").

(** Lift [[+] t ∈ ts, F t] into [[+] t ∈ ts ^++ us, F t] *)
Fixpoint cbyleft {T} {F : T → Type} {ts us : tlist T}
  (x : [+] t ∈ ts, F t) : [+] t ∈ ts ^++ us, F t :=
  match ts, x with
  | ^[], _ => match x with end
  | _ ^:: _, -# x => -# x
  | _ ^:: _, -/ x => -/ cbyleft x
  end.

(** Lift [[+] t ∈ us, F t] into [[+] t ∈ ts ^++ us, F t] *)
Fixpoint cbyright {T} {F : T → Type} {ts us : tlist T}
  (x : [+] t ∈ us, F t) : [+] t ∈ ts ^++ us, F t :=
  match ts with
  | ^[] => x
  | _ ^:: _ => -/ cbyright x
  end.

(** Access [clist] with [cchoice] *)
Fixpoint caccess {T} {F G : T → Type} {A : Type}
  (f : ∀ t , F t → G t → A) {ts : tlist T}
  (xs : [*] t ∈ ts, F t) (y : [+] t ∈ ts, G t) : A :=
  match ts, xs, y with
  | ^[], _, _ => match y with end
  | _ ^:: _, x -:: _, -# y => f _ x y
  | _ ^:: _, _ -:: xs, -/ y => caccess f xs y
  end.
