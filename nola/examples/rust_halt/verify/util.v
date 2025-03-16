(** * Utility *)

From nola.util Require Export prod bin.
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

(** [bin_unwrap]: Unwrap function for the [bin] type *)
Definition bin_unwrap {A} (t : bin A) : unit + A *' bin A *' bin A :=
  match t with BinLeaf => inl () | BinNode a tl tr => inr (a, tl, tr)' end.
(** [bin_unwrap] is injective *)
#[export] Instance bin_unwrap_inj {A} : Inj (=) (=) (@bin_unwrap A).
Proof. by move=> [|???][|???]//=[<-<-<-]. Qed.

(** [bin_wrap]: Wrap function for the [bin] type *)
Definition bin_wrap {A} (s : unit + A *' bin A *' bin A) : bin A :=
  match s with inl () => BinLeaf | inr (a, tl, tr)' => BinNode a tl tr end.

(** [bin_wrap] and [bin_unwrap] are mutually inverse *)
Lemma bin_wrap_unwrap {A t} : @bin_wrap A (bin_unwrap t) = t.
Proof. by case t. Qed.
Lemma bin_unwrap_wrap {A s} : @bin_unwrap A (bin_wrap s) = s.
Proof. by case s=> [[]|?]. Qed.

(** Apply a function to each element of the left spine of [bin] *)
Section bin_lspine_map.
  Context {A} (f : A → A).
  Fixpoint bin_lspine_map (t : bin A) : bin A :=
    match t with BinLeaf => BinLeaf |
      BinNode a tl tr => BinNode (f a) (bin_lspine_map tl) tr end.
End bin_lspine_map.
