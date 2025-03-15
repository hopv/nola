(** * Utility *)

From nola.util Require Export prod.
Import ProdNotation.

(** [list_unwrap]: Unwrap function for the list type *)
Definition list_unwrap {A} (l : list A) : unit + A *' list A :=
  match l with [] => inl () | a :: l' => inr (a, l')' end.
(** [list_unwrap] is injective *)
#[export] Instance list_unwrap_inj {A} : Inj (=) (=) (@list_unwrap A).
Proof. by move=> [|??][|??]//=[<-<-]. Qed.

(** [list_wrap]: Wrap function for the list type *)
Definition list_wrap {A} (s : unit + A *' list A) : list A :=
  match s with inl () => [] | inr (a, l')' => a :: l' end.

(** [list_wrap] and [list_unwrap] are mutually inverse *)
Lemma list_wrap_unwrap {A l} : @list_wrap A (list_unwrap l) = l.
Proof. by case l. Qed.
Lemma list_unwrap_wrap {A s} : @list_unwrap A (list_wrap s) = s.
Proof. by case s=> [[]|?]. Qed.
