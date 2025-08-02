(** * On [gmap] *)

From nola Require Export prelude.
From stdpp Require Export gmap.
From iris.algebra Require Import gmap.

Implicit Type SI : sidx.

(** ** Basic operations *)

Section gmap.
  Context {SI} `{!EqDecision K, !Countable K} {A : ofe}.

  (** [lookup] is proper *)
  #[export] Instance lookup_proper {i} :
    Proper ((≡@{gmap K A}) ==> (≡)) (lookup i).
  Proof. apply ne_proper, _. Qed.

  (** [singletonM] is proper *)
  #[export] Instance singleton_proper {i} :
    Proper ((≡) ==> (≡@{gmap K A})) (singletonM i).
  Proof. apply ne_proper, _. Qed.
End gmap.

(** ** [list_to_gmap] *)

(** [list_to_gmap]: [list] to [gmap nat] *)
Section list_to_gmap'.
  Context {A : Type}.
  Fixpoint list_to_gmap' (i : nat) (l : list A) : gmap nat A :=
    match l with [] => ∅ | x :: l => <[i := x]> (list_to_gmap' (S i) l) end.
  Definition list_to_gmap := list_to_gmap' 0.
End list_to_gmap'.

(** [!!] over [list_to_gmap] *)
Lemma lookup_list_to_gmap' {A i l j} :
  list_to_gmap' (A:=A) i l !! (i + j) = l !! j.
Proof.
  move: i j. elim: l; [done|]=>/= y l IH i [|j]/=.
  { by rewrite Nat.add_0_r lookup_insert_eq. }
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
  rewrite IH insert_insert_ne; [|lia]. f_equal. lia.
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
  - move=> <-. by rewrite lookup_insert_eq list_lookup_insert_eq.
  - move=> ?. rewrite lookup_insert_ne; [|done].
    rewrite list_lookup_insert_ne; [|done]. by rewrite lookup_list_to_gmap.
Qed.

(** ** [insdel]: Insert or delete *)

(** [insdel]: Insert or delete *)
Definition insdel `{!EqDecision K, !Countable K, !Infinite K} {A}
  (i : K) (oa : option A) : gmap K A → gmap K A :=
  match oa with
  | Some a => <[i := a]>
  | None => delete i
  end.

Section insdel.
  Context `{!EqDecision K, !Countable K, !Infinite K}.

  (** Lookup over [insdel] *)
  Lemma lookup_insdel {A i oa} {m : gmap K A} : insdel i oa m !! i = oa.
  Proof. case: oa=> [?|]; [apply lookup_insert_eq|apply lookup_delete_eq]. Qed.
  Lemma lookup_insdel_ne {A i j oa} {m : gmap K A} :
    i ≠ j → insdel i oa m !! j = m !! j.
  Proof. case: oa=> [?|]; [apply lookup_insert_ne|apply lookup_delete_ne]. Qed.
End insdel.

(** ** [map_with], [map_without] and [map_by] *)

Section map_with.
  Context `{!EqDecision K, !Countable K, !Infinite K} {A : Type} (m : gmap K A).

  (** [map_with m l]: [m] with [l] freshly added *)
  Fixpoint map_with (l : list A) : gmap K A :=
    match l with [] => m | x :: l =>
      let m' := map_with l in <[fresh (dom m'):=x]> m' end.

  (** [map_without m]: [map_with m l] minus [m] *)
  Fixpoint map_without (l : list A) : gmap K A :=
    match l with [] => ∅ | x :: l =>
      <[fresh (dom (map_with l)):=x]> (map_without l) end.
End map_with.

Section map_with.
  Context `{!EqDecision K, !Countable K, !Infinite K}.

  (** [map_by]: Map initialized by [l] *)
  Definition map_by {A} := map_with (K:=K) (A:=A) ∅.

  (** [map_with m l] is the union of [map_without m l] and [m] *)
  Lemma map_with_without {A} {m : gmap K A} {l} :
    map_with m l = map_without m l ∪ m.
  Proof.
    elim: l; [by rewrite /= left_id|]=>/= a l IH.
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
    elim: l; [exact: map_disjoint_empty_l|]=>/= ?? IH.
    apply map_disjoint_insert_l. split; [|done]. exact map_with_fresh.
  Qed.
End map_with.
