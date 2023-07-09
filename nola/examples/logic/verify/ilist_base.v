(** * Base definitions for shared mutable singly linked infinite lists *)

From nola.examples.heap_lang Require Export notation.

(** Calls [f] on the first [c] elements of the infinite list by [d] *)
Definition siter : val :=
  rec: "self" "f" "c" "l" :=
    if: "c" = #0 then #() else "f" "l";; "self" "f" ("c" - #1) (! ("l" +ₗ #1)).

(** Calls [iter] with a non-deterministic [c] *)
Definition siter_nd : val := λ: "f" "l", siter "f" Ndnat "l".

(** Forks [c] threads executing [siter_nd] *)
Definition siter_nd_forks : val :=
  rec: "self" "f" "c" "l" :=
    if: "c" = #0 then #() else
      Fork (siter_nd "f" "l");; "self" "f" ("c" - #1) "l".

(** Calls [siter_nd_forks] with a non-deterministic [c] *)
Definition siter_nd_forks_nd : val := λ: "f" "l", siter_nd_forks "f" Ndnat "l".
