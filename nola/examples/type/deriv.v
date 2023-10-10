(** * Derivability *)

From nola.examples.type Require Export intp.

(** Namespaces *)
Definition tguardN := nroot .@ "tguard".
Definition trefN := nroot .@ "tref".

(** ** [tacc]: Accessor for [tinvd] *)
Definition tacc `{!tintpGS L Σ} {i} (δ : tderiv_ty Σ) (Tx : tinvd i)
  : iProp Σ :=
  match Tx with
  | tinvd_guard T v => ∀ E, ⌜↑tguardN ⊆ E⌝ →
      |=[tinv_wsat δ (S i)]{E}=> ⟦ T ⟧(δ) v
  | tinvd_ref l T => |=[tinv_wsat δ (S i)]{⊤,⊤∖↑trefN}=> ∃ v,
      l ↦ v ∗ ⟦ T ⟧(δ) v ∗
      (∀ w, l ↦ w -∗ ⟦ T ⟧(δ) w =[tinv_wsat δ (S i)]{⊤∖↑trefN,⊤}=∗ True)
  end%I.

(** ** [tderivsi]: [derivsi] for [tinvd] *)
Canonical tderivsi `{!tintpGS L Σ} :=
  Derivsi (tderivs Σ) (λ δ '(Darg _ (existT _ Tx)), tacc δ Tx).

(** Notation for [tderivsi] *)
Notation tderivy := (derivy tderivsi).
Notation tderiv := (deriv (DI:=tderivsi)).
Notation tderiv_sound := (deriv_sound (DI:=tderivsi)).

(** Utility for [tderiv] *)
Notation trefd := (tref tderiv).
Notation tguardd := (tguard tderiv).
Notation "⟦ T ⟧{ i }" := ⟦ T ⟧{i}(tderiv) (only parsing) : nola_scope.
Notation "⟦ T ⟧" := ⟦ T ⟧(tderiv) : nola_scope.
Notation tinv_wsatd M := (tinv_wsat tderiv M).
Notation inv_wsatd i := (inv_wsat' tderiv i).

(** ** Type judgments *)

(** Subtyping *)
Definition tsub `{!tintpGS L Σ} δ {i j} (T : type i (;ᵞ)) (U : type j (;ᵞ))
  : Prop := ∀ v, ⟦ T ⟧(δ) v ⊢ ⟦ U ⟧(δ) v.
Infix "⊑{ i , j } ( δ )" := (tsub δ (i:=i) (j:=j))
  (at level 99, no associativity, only parsing) : nola_scope.
Notation "T ⊑( δ ) U" := (tsub δ T U)
  (at level 99, no associativity, format "T  ⊑( δ )  U") : nola_scope.

(** Type equivalence *)
Definition teqv `{!tintpGS L Σ} δ {i j} (T : type i (;ᵞ)) (U : type j (;ᵞ))
  : Prop := ∀ v, ⟦ T ⟧(δ) v ⊣⊢ ⟦ U ⟧(δ) v.
Infix "≃{ i , j } ( δ )" := (teqv δ (i:=i) (j:=j))
  (at level 99, no associativity, only parsing) : nola_scope.
Notation "T ≃( δ ) U" := (teqv δ T U)
  (at level 99, no associativity, format "T  ≃( δ )  U") : nola_scope.

(** Type transmutation *)
Definition ttrans `{!tintpGS L Σ} δ (i : nat)
  {j k} (T : type j (;ᵞ)) (U : type k (;ᵞ)) : Prop :=
  ∀ E v, ↑tguardN ⊆ E → ⟦ T ⟧(δ) v =[tinv_wsat δ i]{E}=∗ ⟦ U ⟧(δ) v.
Infix "==>{ j , k } ( i , δ )" := (ttrans δ i (j:=j) (k:=k))
  (at level 99, no associativity, only parsing) : nola_scope.
Notation "T ==>( i , δ ) U" := (ttrans δ i T U)
  (at level 99, no associativity, format "T  ==>( i , δ )  U") : nola_scope.

Definition tbitrans `{!tintpGS L Σ} δ (i : nat)
  {j k} (T : type j (;ᵞ)) (U : type k (;ᵞ)) : Prop :=
  (T ==>(i,δ) U) ∧ (U ==>(i,δ) T).
Infix "<==>{ j , k } ( i , δ )" := (tbitrans δ i (j:=j) (k:=k))
  (at level 99, no associativity, only parsing) : nola_scope.
Notation "T <==>( i , δ ) U" := (tbitrans δ i T U)
  (at level 99, no associativity, format "T  <==>( i , δ )  U") : nola_scope.

(** Typed object *)
Definition tobj_def `{!tintpGS L Σ} {i} (v : val) (T : type i (;ᵞ)) : iProp Σ :=
  ⟦ T ⟧ v.
Definition tobj_aux : seal (@tobj_def). Proof. by eexists. Qed.
Definition tobj `{!tintpGS L Σ} {i} := tobj_aux.(unseal) L Σ _ i.
Lemma tobj_unseal : @tobj = @tobj_def. Proof. exact: seal_eq. Qed.
Infix ":ᵒ{ i }" := (tobj (i:=i)) (at level 70, no associativity) : nola_scope.
Infix ":ᵒ" := tobj (at level 70, no associativity) : nola_scope.

(** Typed expression *)
Definition texpr `{!tintpGS L Σ} i {j} (e : expr) (T : type j (;ᵞ)) : iProp Σ :=
  WP[tinv_wsatd i] e [{ v, |=[tinv_wsatd i]{⊤}=> ⟦ T ⟧ v }]%I.
Arguments texpr {_ _ _} i {j} e%E T : simpl never.
Infix ":ᵉ{ j } ( i )" := (texpr i (j:=j)) (at level 70, no associativity)
  : nola_scope.
Notation "e :ᵉ( i ) T" := (texpr i e T)
  (at level 70, no associativity, format "e  :ᵉ( i )  T") : nola_scope.
