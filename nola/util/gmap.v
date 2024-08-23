(** * On [gmap] *)

From nola Require Export prelude.
From stdpp Require Export gmap.

(** ** [list_to_gmap] *)

(** [list_to_gmap]: [list] to [gmap nat] *)
Fixpoint list_to_gmap' {A : Type} (i : nat) (l : list A) : gmap nat A :=
  match l with [] => ∅ | x :: l => <[i := x]> (list_to_gmap' (S i) l) end.
Definition list_to_gmap {A} := list_to_gmap' (A:=A) 0.

(** [!!] over [list_to_gmap] *)
Lemma lookup_list_to_gmap' {A i l j} :
  list_to_gmap' (A:=A) i l !! (i + j) = l !! j.
Proof.
  move: i j. elim: l; [done|]=>/= y l IH i [|j]/=.
  { by rewrite Nat.add_0_r lookup_insert. }
  rewrite lookup_insert_ne; [|lia]. rewrite -(IH (S i)). f_equal. lia.
Qed.
Lemma lookup_list_to_gmap {A l i} : list_to_gmap (A:=A) l !! i = l !! i.
Proof. exact lookup_list_to_gmap'. Qed.
Lemma lookup_list_to_gmap'_pre {A i l j} :
  j < i → list_to_gmap' (A:=A) i l !! j = None.
Proof.
  move: i j. elim: l; [done|]=>/= a l IH i j ?. apply lookup_insert_None.
  split; [|lia]. apply IH. lia.
Qed.

(** [list_to_gmap] over snoc *)
Lemma list_to_gmap'_snoc {A i l x} :
  list_to_gmap' (A:=A) i (l ++ [x]) = <[i + length l := x]> (list_to_gmap' i l).
Proof.
  move: i. elim: l=>/= [|y l IH] i. { f_equal. lia. }
  rewrite IH insert_commute; [|lia]. f_equal. lia.
Qed.
Lemma list_to_gmap_snoc {A l x} :
  list_to_gmap (A:=A) (l ++ [x]) = <[length l := x]> (list_to_gmap l).
Proof. exact list_to_gmap'_snoc. Qed.

(** [list_to_gmap] over [insert] *)
Lemma list_to_gmap_insert {A l i x} : i < length l →
  list_to_gmap (A:=A) (<[i := x]> l) = <[i := x]> (list_to_gmap l).
Proof.
  move=> ?. apply map_eq=> j. rewrite lookup_list_to_gmap.
  case (decide (i = j)).
  - move=> <-. by rewrite lookup_insert list_lookup_insert.
  - move=> ?. rewrite lookup_insert_ne; [|done].
    rewrite list_lookup_insert_ne; [|done]. by rewrite lookup_list_to_gmap.
Qed.

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
