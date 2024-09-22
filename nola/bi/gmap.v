(** * Utility for [gmap] *)

From nola.util Require Export gmap.
From iris.algebra Require Import updates gmap.
From iris.proofmode Require Import proofmode.

Implicit Type PROP : bi.

(** ** On [gmapR] *)

Section gmapR.
  Context `{!EqDecision K, !Countable K} {C : cmra}.

  (** [f <$> m] is valid if [✓ f x] is always valid *)
  Lemma gmap_fmap_valid {A} (f : A → C) (m : gmap K A) :
    (∀ x, ✓ f x) → ✓ (f <$> m).
  Proof. move=> ? i. rewrite lookup_fmap. by case: (m !! i). Qed.

  (** Simplify [op] over disjoint maps *)
  Lemma gmap_op_disj {m m' : gmap K C} : m ##ₘ m' → m ⋅ m' ≡ m ∪ m'.
  Proof.
    move=> /map_disjoint_spec disj i. rewrite gmap_op lookup_merge.
    rewrite lookup_union. case eq: (m !! i); case eq': (m' !! i); [|done..].
    exfalso. by eapply disj.
  Qed.
End gmapR.

(** ** On [[∗ map]] *)

Section big_sepM.
  Context `{!EqDecision K, !Countable K} {PROP} {A : Type}.
  Implicit Type (m : gmap K A) (l : list A).

  (** [[∗ map]] over [list_to_gmap] *)
  Lemma big_sepM_list_to_gmap' l j (Φ : nat → A → PROP) :
    ([∗ map] i ↦ x ∈ list_to_gmap' j l, Φ i x) ⊣⊢
      [∗ list] i ↦ x ∈ l, Φ (j + i) x.
  Proof.
    move: j. elim: l=>/=; [move=> ?; by rewrite big_sepM_empty|]=> ?? IH j.
    setoid_rewrite <-plus_n_Sm. rewrite -(IH (S _)) (right_id 0).
    rewrite big_sepM_insert; [done|]. apply lookup_list_to_gmap'_pre. lia.
  Qed.
  Lemma big_sepM_list_to_gmap l (Φ : nat → A → PROP) :
    ([∗ map] i ↦ x ∈ list_to_gmap l, Φ i x) ⊣⊢ [∗ list] i ↦ x ∈ l, Φ i x.
  Proof. apply big_sepM_list_to_gmap'. Qed.

  (** [[∗ map]] over [map_without] *)
  Lemma big_sepM_map_without `{!Infinite K} m l (Φ : A → PROP) :
    ([∗ map] x ∈ map_without m l, Φ x) ⊣⊢ [∗ list] x ∈ l, Φ x.
  Proof.
    elim: l; [by rewrite big_sepM_empty|]=>/= a l <-.
    rewrite big_sepM_insert; [done|]. apply map_without_with_fresh.
  Qed.
  Lemma big_sepM_map_without' `{!Infinite K} m l (Φ : K → A → PROP) :
    ([∗ map] i ↦ x ∈ map_without m l, Φ i x) ⊢ [∗ list] x ∈ l, ∃ i, Φ i x.
  Proof.
    elim: l; [by rewrite big_sepM_empty|]=>/= a l <-.
    rewrite big_sepM_insert; [|by apply map_without_with_fresh]. f_equiv.
    iIntros. by iExists _.
  Qed.

  (** [[∗ map]] over [map_with] *)
  Lemma big_sepM_map_with_without `{!Infinite K} m l (Φ : K → A → PROP) :
    ([∗ map] i ↦ x ∈ map_with m l, Φ i x) ⊣⊢
      ([∗ map] i ↦ x ∈ map_without m l, Φ i x) ∗ [∗ map] i ↦ x ∈ m, Φ i x.
  Proof.
    by rewrite map_with_without big_sepM_union; [|exact map_without_disj].
  Qed.
  Lemma big_sepM_map_with `{!Infinite K} m l (Φ : A → PROP) :
    ([∗ map] x ∈ map_with m l, Φ x) ⊣⊢
      ([∗ list] x ∈ l, Φ x) ∗ [∗ map] x ∈ m, Φ x.
  Proof. by rewrite big_sepM_map_with_without big_sepM_map_without. Qed.
  Lemma big_sepM_map_with' `{!Infinite K} m l (Φ : K → A → PROP) :
    ([∗ map] i ↦ x ∈ map_with m l, Φ i x) ⊢
      ([∗ list] x ∈ l, ∃ i, Φ i x) ∗ [∗ map] i ↦ x ∈ m, Φ i x.
  Proof. by rewrite big_sepM_map_with_without big_sepM_map_without'. Qed.

  (** [[∗ map]] over [map_by] *)
  Lemma big_sepM_map_by `{!Infinite K} l (Φ : A → PROP) :
    ([∗ map] x ∈ map_by K l, Φ x) ⊣⊢ [∗ list] x ∈ l, Φ x.
  Proof. by rewrite big_sepM_map_with big_sepM_empty right_id. Qed.
  Lemma big_sepM_map_by' `{!Infinite K} l (Φ : K → A → PROP) :
    ([∗ map] i ↦ x ∈ map_by K l, Φ i x) ⊢ [∗ list] x ∈ l, ∃ i, Φ i x.
  Proof. by rewrite big_sepM_map_with' big_sepM_empty right_id. Qed.
End big_sepM.
