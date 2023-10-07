(** * Modified product type *)

From nola Require Export prelude.

(** [prod']: Modified [prod],
  using primitive projections and right-associative notations *)
#[projections(primitive)]
Record prod' (A B : Type) : Type := pair' {
  fst' : A; snd' : B;
}.
Arguments pair' {_ _} _ _.
Arguments fst' {_ _} _.
Arguments snd' {_ _} _.
Infix "*'" := prod' (at level 80, right associativity) : nola_scope.
Notation "( a , .. , y , z )'" := (pair' a (.. (pair' y z) ..))
  (format "( a ,  .. ,  y ,  z )'") : nola_scope.
Notation "p .1'" := (fst' p) (at level 2, left associativity, format "p .1'")
  : nola_scope.
Notation "p .2'" := (snd' p) (at level 2, left associativity, format "p .2'")
  : nola_scope.
Notation "pl .*1'" := (fmap (M:=list) fst' pl)
  (at level 2, left associativity, format "pl .*1'").
Notation "pl .*2'" := (fmap (M:=list) snd' pl)
  (at level 2, left associativity, format "pl .*2'").
