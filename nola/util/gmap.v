(** * On [gmap] *)

From nola Require Export prelude.
From stdpp Require Export gmap.

(** ** [map_with], [map_without] and [map_by] *)

(** [map_with m l]: [m] with [l] freshly added *)
Fixpoint map_with `{!EqDecision K, !Countable K, !Infinite K} {A}
  (m : gmap K A) (l : list A) : gmap K A :=
  match l with [] => m | x :: l =>
    let m' := map_with m l in <[fresh (dom m'):=x]> m' end.
(** [map_by]: Map initialized by [l] *)
Notation map_by K := (map_with (K:=K) ∅).

(** [map_without m]: [map_with m l] minus [m] *)
Fixpoint map_without `{!EqDecision K, !Countable K, !Infinite K} {A}
  (m : gmap K A) (l : list A) : gmap K A :=
  match l with [] => ∅ | x :: l =>
    <[fresh (dom (map_with m l)):=x]> (map_without m l) end.

Section map_with.
  Context `{!EqDecision K, !Countable K, !Infinite K}.

  (** [map_with m l] is the union of [map_without m l] and [m] *)
  Lemma map_with_without {A} {m : gmap K A} {l} :
    map_with m l = map_without m l ∪ m.
  Proof.
    elim: l; [by rewrite/= left_id|]=>/= a l IH.
    by rewrite -insert_union_l -IH.
  Qed.

  (** Accessing [map_without m l] at a fresh index of [map_with m l] *)
  Lemma map_without_with_fresh {A} {m : gmap K A} {l} :
    map_without m l !! fresh (dom (map_with m l)) = None.
  Proof.
    rewrite map_with_without. apply not_elem_of_dom. eapply not_elem_of_union.
    rewrite comm dom_union_L. apply is_fresh.
  Qed.

  (** Accessing [m] at a fresh index of [map_with m l] *)
  Lemma map_with_fresh {A} {m : gmap K A} {l} :
    m !! fresh (dom (map_with m l)) = None.
  Proof.
    rewrite map_with_without. apply not_elem_of_dom. eapply not_elem_of_union.
    rewrite dom_union_L. apply is_fresh.
  Qed.

  (** [map_without m l] and [m] are disjoint *)
  Lemma map_without_disj {A} {m : gmap K A} {l} : map_without m l ##ₘ m.
  Proof.
    elim: l; [by apply map_disjoint_empty_l|]=>/= ?? IH.
    apply map_disjoint_insert_l. split; [|done]. exact map_with_fresh.
  Qed.
End map_with.
