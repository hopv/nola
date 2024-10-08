(** * Modified product types *)

From nola Require Export prelude.

(** ** [prod']: Modified [prod] with primitive projections and
  right-associative notations *)
#[projections(primitive)]
Record prod' (A B : Type) : Type := pair' { fst' : A; snd' : B; }.
Add Printing Constructor prod'.
Arguments pair' {_ _} _ _. Arguments fst' {_ _} _. Arguments snd' {_ _} _.

Module ProdNotation.
  Infix "*'" := prod' (at level 41, right associativity).
  Notation "( a , .. , y , z )'" := (pair' a (.. (pair' y z) ..))
    (format "( a ,  .. ,  y ,  z )'").
  Notation "p .1'" := (fst' p) (at level 2, left associativity, format "p .1'").
  Notation "p .2'" := (snd' p) (at level 2, left associativity, format "p .2'").
  Notation "pl .*1'" := (fmap (M:=list) fst' pl)
    (at level 2, left associativity, format "pl .*1'").
  Notation "pl .*2'" := (fmap (M:=list) snd' pl)
    (at level 2, left associativity, format "pl .*2'").
End ProdNotation.

(** [pair'] is injective *)
#[export] Instance pair'_inj {A B} : Inj2 (=) (=) (=) (@pair' A B).
Proof. by move=> ????[]. Qed.

(** ** [sigT']: Modified [sigT] as a record with primitive projections *)
#[projections(primitive)]
Record sigT' {A : Type} (F : A → Type) : Type :=
  existT' { projT1' : A; projT2' : F projT1'; }.
Add Printing Constructor sigT'.
Arguments existT' {_ _} _ _.
Arguments projT1' {_ _} _. Arguments projT2' {_ _} _.
