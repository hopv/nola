(** * Utility for [tlist], [clist] and [cchoice] *)

From nola Require Import prelude.

(** ** [tlist]: List of elements in a higher universe
  It is almost the same as [list], but the element type can belong to
  a higher universe, which includes [list] itself. *)
Inductive tlist (T : Type) : Type :=
| tnil : tlist T
| tcons : T -> tlist T -> tlist T.

Global Arguments tnil {_}.
Global Arguments tcons {_} _ _.

(** Concatenate [tlist]s *)
Fixpoint tapp {T} (ts us : tlist T) : tlist T :=
  match ts with
  | tnil => us
  | tcons t ts => tcons t (tapp ts us)
  end.

(** Notations for [tlist] *)
Module TlistNotations.
  Notation "^[]" := tnil.
  Infix "^::" := tcons (at level 60, right associativity).
  Notation "^[ x ; .. ; z ]" := (x ^:: .. (z ^:: ^[]) ..)
    (at level 1, format "^[ x ;  .. ;  z ]").
  Infix "^++" := tapp (at level 60, right associativity).
End TlistNotations.
Import TlistNotations.

(** ** [clist]: Heterogeneous list type calculated from [tlist] *)

(** Unit type for [tnil] *)
Variant cunit : Set := cnil.
(** Product type for [tcons] *)
Record cprod (A B : Type) : Type := ccons { chd : A; ctl : B }.
Global Arguments ccons {_ _} _ _.
Global Arguments chd {_ _} _.
Global Arguments ctl {_ _} _.

(** [clist]: Heterogeneous list type calculated from [tlist] *)
Fixpoint clist {T} (F : T → Type) (ts : tlist T) : Type :=
  match ts with
  | ^[] => cunit
  | t ^:: ts => cprod (F t) (clist F ts)
  end.

(** Append [clist]s *)
Fixpoint capp {T} {F : T → Type} {ts us : tlist T}
  (xs : clist F ts) (ys : clist F us) : clist F (ts ^++ us) :=
  match ts, xs with
  | ^[], _ => ys
  | _ ^:: _, ccons x xs => ccons x (capp xs ys)
  end.

(** Notations for [clist] *)
Module ClistNotations.
  Notation "[*] t ∈ ts , A" := (clist (λ t, A) ts)
    (at level 200, ts at level 10, t binder, right associativity,
      format "[*]  t  ∈  ts ,  A").
  Notation "*[ ]" := cunit (at level 1, format "*[ ]") : type_scope.
  Infix "*::" := cprod (at level 60, right associativity) : type_scope.
  Notation "*[ A ; .. ; Z ]" := (A *:: .. (Z *:: *[]) ..)
    (at level 1, format "*[ A ;  .. ;  Z ]") : type_scope.

  Notation "-[ ]" := cnil (at level 1, format "-[ ]").
  Infix "-::" := ccons (at level 60, right associativity).
  Notation "-[ x ; .. ; z ]" := (x -:: .. (z -:: -[]) ..)
    (at level 1, format "-[ x ;  .. ;  z ]").
  Infix "-++" := capp (at level 60, right associativity).
End ClistNotations.
Import ClistNotations.

(** ** [cchoice]: Sum type calculated from [tlist] *)

(** Empty type for [tnil] *)
Variant cempty : Set := .
(** Sum type for [tcons] *)
Variant csum (A B : Type) : Type := cbyhd (_ : A) | cbytl (_ : B).
Global Arguments cbyhd {_ _} _.
Global Arguments cbytl {_ _} _.

(** [cchoice]: Sum type calculated from [tlist] *)
Fixpoint cchoice {T} (F : T → Type) (ts : tlist T) : Type :=
  match ts with
  | ^[] => cempty
  | t ^:: ts => csum (F t) (cchoice F ts)
  end.

(** Notations for [cchoice] *)
Module CchoiceNotations.
  Notation "[+] t ∈ ts , A" := (cchoice (λ t, A) ts)
    (at level 200, ts at level 10, t binder, right associativity,
      format "[+]  t  ∈  ts ,  A").

  Notation "+[ ]" := cempty (at level 1, format "+[ ]") : type_scope.
  Infix "+::" := csum (at level 60, right associativity) : type_scope.
  Notation "+[ A ; .. ; Z ]" := (A +:: .. (Z +:: +[]) ..)
    (at level 1, format "+[ A ;  .. ;  Z ]") : type_scope.

  Notation "-# x" := (cbyhd x)
    (at level 20, right associativity, format "-#  x").
  Notation "-/ x" := (cbytl x)
    (at level 20, right associativity, format "-/ x").
End CchoiceNotations.
Import CchoiceNotations.

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
