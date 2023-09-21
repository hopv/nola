(** * Base definitions for shared mutable singly linked infinite lists *)

From nola.examples.heap_lang Require Export notation.

(** Calls ["f"] on the first ["n"] elements of the infinite list *)
Definition siter : val := rec: "self" "f" "n" "l" :=
  if: !"n" = #0 then #() else
    "f" "l";; "n" <- !"n" - #1;; "self" "f" "n" (! ("l" +ₗ #1)).

(** Calls [iter] with non-deterministically initialized ["n"] *)
Definition siter_nd : val := λ: "f" "l",
  let: "n" := ref Ndnat in siter "f" "n" "l".

(** Forks [c] threads executing [siter_nd] *)
Definition siter_nd_forks : val := rec: "self" "f" "k" "l" :=
  if: !"k" = #0 then #() else
    Fork (siter_nd "f" "l");; "k" <- !"k" - #1;; "self" "f" "k" "l".

(** Calls [siter_nd_forks] with a non-deterministic ["k"] *)
Definition siter_nd_forks_nd : val := λ: "f" "l",
  let: "k" := ref Ndnat in siter_nd_forks "f" "k" "l".
