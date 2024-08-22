(** * Utility on [gmap] *)

From nola.util Require Export gmap.
From iris.algebra Require Import updates gmap.
From iris.proofmode Require Import proofmode.

(** ** On [gmapR] *)

Section gmapR.
  Context `{!EqDecision K, !Countable K} {C : cmra}.

  (** [lookup] is proper *)
  #[export] Instance lookup_proper {i} :
    Proper ((≡@{gmapR K C}) ==> (≡)) (lookup i).
  Proof. apply ne_proper, _. Qed.

  (** [singletonM] is proper *)
  #[export] Instance singleton_proper {i} :
    Proper ((≡) ==> (≡@{gmapR K C})) (singletonM i).
  Proof. apply ne_proper, _. Qed.

  (** [f <$> m] is valid if [✓ f x] is always valid *)
  Lemma gmap_fmap_valid {A} (f : A → C) (m : gmap K A) :
    (∀ x, ✓ f x) → ✓ (f <$> m).
  Proof. move=> ? i. rewrite lookup_fmap. by case: (m !! i). Qed.

  (** Simplify [op] on disjoint maps *)
  Lemma gmap_op_disj {m m' : gmap K C} : m ##ₘ m' → m ⋅ m' ≡ m ∪ m'.
  Proof.
    move=> /map_disjoint_spec disj i. rewrite gmap_op lookup_merge.
    rewrite lookup_union. case eq: (m !! i); case eq': (m' !! i); [|done..].
    exfalso. by eapply disj.
  Qed.
End gmapR.

(** ** On [[∗ map]] *)

Section big_sepM.
  Context `{!EqDecision K, !Countable K} {PROP : bi} {A : Type}.
  Implicit Type (m : gmap K A) (l : list A).

  (** [[∗ map]] on [map_with] *)
  Lemma big_sepM_map_with `{!Infinite K} m l (Φ : A → PROP) :
    ([∗ map] x ∈ map_with m l, Φ x) ⊣⊢
      ([∗ list] x ∈ l, Φ x) ∗ [∗ map] x ∈ m, Φ x.
  Proof.
    elim: l; [by rewrite/= left_id|]=>/= ?? IH. rewrite -assoc -IH.
    rewrite big_sepM_insert; [done|]. apply not_elem_of_dom, is_fresh.
  Qed.
  Lemma big_sepM_map_with' `{!Infinite K} m l (Φ : K → A → PROP) :
    ([∗ map] i ↦ x ∈ map_with m l, Φ i x) ⊢
      ([∗ list] x ∈ l, ∃ i, Φ i x) ∗ [∗ map] i ↦ x ∈ m, Φ i x.
  Proof.
    elim: l; [by rewrite/= left_id|]=>/= ?? IH. rewrite -assoc -IH.
    rewrite big_sepM_insert. { f_equiv. iIntros. by iExists _. }
    apply not_elem_of_dom, is_fresh.
  Qed.

  (** [[∗ map]] on [map_by] *)
  Lemma big_sepM_map_by `{!Infinite K} l (Φ : A → PROP) :
    ([∗ map] x ∈ map_by K l, Φ x) ⊣⊢ [∗ list] x ∈ l, Φ x.
  Proof. by rewrite big_sepM_map_with big_sepM_empty right_id. Qed.
  Lemma big_sepM_map_by' `{!Infinite K} l (Φ : K → A → PROP) :
    ([∗ map] i ↦ x ∈ map_by K l, Φ i x) ⊢ [∗ list] x ∈ l, ∃ i, Φ i x.
  Proof. by rewrite big_sepM_map_with' big_sepM_empty right_id. Qed.

  (** [[∗ map]] on [map_withouut] *)
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

  (** Conversion between [[∗ map]] and [[∗ list]] *)
  Lemma big_sepM_map_to_list_snd m (Φ : A → PROP) :
    ([∗ map] x ∈ m, Φ x) ⊣⊢ [∗ list] x ∈ (map_to_list m).*2, Φ x.
  Proof. by rewrite big_sepM_map_to_list big_sepL_fmap. Qed.

  (** [big_sepM_filter'] with keys ignored *)
  Lemma big_sepM_filter'' φ `{∀ x, Decision (φ x)} m (Φ : A → PROP) :
    ([∗ map] x ∈ filter (λ ix, φ (snd ix)) m, Φ x) ⊣⊢
    ([∗ map] x ∈ m, if decide (φ x) then Φ x else emp).
  Proof. by rewrite big_sepM_filter'. Qed.

  (** Split [big_sepM] by [filter] *)
  Lemma big_sepM_filter_complement φ
    `{! ∀ ix, Decision (φ ix)} m (Φ : A → PROP) :
    ([∗ map] x ∈ m, Φ x) ⊣⊢ ([∗ map] x ∈ filter φ m, Φ x) ∗
      ([∗ map] x ∈ filter (λ ix, ¬ φ ix)%type m, Φ x).
  Proof.
    rewrite -{1}(map_filter_union_complement φ m).
    rewrite big_sepM_union; by [|apply map_disjoint_filter_complement].
  Qed.
End big_sepM.
