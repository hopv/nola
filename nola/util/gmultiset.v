(** On [gmultiset] *)

From nola Require Export prelude.
From stdpp Require Export gmap gmultiset.

Section gmultiset.
  Context `{Countable A}.
  Implicit Type s : gset A.

  (** Convert [gset] to [gmultiset] *)
  Definition gset_to_gmultiset (s : gset A) : gmultiset A :=
    GMultiSet (gset_to_gmap 1%positive s).
  (** [dom] over [gset_to_gmultiset] *)
  Lemma dom_gset_to_gmultiset {s} : dom (gset_to_gmultiset s) = s.
  Proof. apply dom_gset_to_gmap. Qed.
  (** [∈] over [gset_to_gmultiset] *)
  Lemma elem_of_gset_to_gmultiset {s a} : a ∈ gset_to_gmultiset s ↔ a ∈ s.
  Proof. by rewrite -gmultiset_elem_of_dom dom_gset_to_gmultiset. Qed.
End gmultiset.
