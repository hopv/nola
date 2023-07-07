(** * Derivability *)

From nola.examples.type Require Export intp.

(** Namespaces *)
Definition tguardN := nroot .@ "tguard".
Definition trefN := nroot .@ "tref".

(** ** [tacc]: Accessor for [tinvd] *)
Definition tacc `{!tintpGS L Σ} {i} (d : tderiv_ty Σ) (Tx : tinvd i)
  : iProp Σ :=
  match Tx with
  | tinvd_guard T v => ∀ E, ⌜↑tguardN ⊆ E⌝ →
      |=[tinv_wsat d (S i)]{E}=> ⟦ T ⟧(d) v
  | tinvd_ref l T => |=[tinv_wsat d (S i)]{⊤,⊤∖↑trefN}=> ∃ v,
      l ↦ v ∗ ⟦ T ⟧(d) v ∗
      (∀ w, l ↦ w -∗ ⟦ T ⟧(d) w =[tinv_wsat d (S i)]{⊤∖↑trefN,⊤}=∗ True)
  end%I.

(** ** [tderivsi]: [derivsi] for [tinvd] *)
Definition tderivsi Σ `{!tintpGS L Σ} : derivsi :=
  Intpsi (tderivs Σ) (λ d '(Darg _ (existT _ Tx)), tacc d Tx).

(** Notation for [tderivsi] *)
Notation tderivy Σ := (derivy (tderivsi Σ)).
Notation tderiv := (deriv (ITI:=tderivsi _)).
Notation tdsound := (dsound (ITI:=tderivsi _)).
Notation tderiv_sound := (deriv_sound (ITI:=tderivsi _)).

(** Utility for [tderiv] *)
Notation trefd := (tref tderiv).
Notation tguardd := (tguard tderiv).
Notation "⟦ T ⟧{ i }" := ⟦ T ⟧{i}(tderiv) (only parsing) : nola_scope.
Notation "⟦ T ⟧" := ⟦ T ⟧(tderiv) : nola_scope.
Notation tinv_wsatd M := (tinv_wsat tderiv M).
Notation tninv_wsatd i := (tninv_wsat tderiv i).

(** ** Type judgments *)

(** Subtyping *)
Definition tsub `{!tintpGS L Σ} d {i j} (T : type i (;ᵞ)) (U : type j (;ᵞ))
  : Prop := ∀ v, ⟦ T ⟧(d) v ⊢ ⟦ U ⟧(d) v.
Infix "⊑{ i , j } ( d )" := (tsub d (i:=i) (j:=j))
  (at level 99, no associativity, only parsing) : nola_scope.
Notation "T ⊑( d ) U" := (tsub d T U)
  (at level 99, no associativity, format "T  ⊑( d )  U") : nola_scope.

(** Type equivalence *)
Definition teqv `{!tintpGS L Σ} d {i j} (T : type i (;ᵞ)) (U : type j (;ᵞ))
  : Prop := ∀ v, ⟦ T ⟧(d) v ⊣⊢ ⟦ U ⟧(d) v.
Infix "≃{ i , j } ( d )" := (teqv d (i:=i) (j:=j))
  (at level 99, no associativity, only parsing) : nola_scope.
Notation "T ≃( d ) U" := (teqv d T U)
  (at level 99, no associativity, format "T  ≃( d )  U") : nola_scope.

(** Type transmutation *)
Definition ttrans `{!tintpGS L Σ} d (i : nat)
  {j k} (T : type j (;ᵞ)) (U : type k (;ᵞ)) : Prop :=
  ∀ E v, ↑tguardN ⊆ E → ⟦ T ⟧(d) v =[tinv_wsat d i]{E}=∗ ⟦ U ⟧(d) v.
Infix "==>{ j , k } ( i , d )" := (ttrans d i (j:=j) (k:=k))
  (at level 99, no associativity, only parsing) : nola_scope.
Notation "T ==>( i , d ) U" := (ttrans d i T U)
  (at level 99, no associativity, format "T  ==>( i , d )  U") : nola_scope.

Definition tbitrans `{!tintpGS L Σ} d (i : nat)
  {j k} (T : type j (;ᵞ)) (U : type k (;ᵞ)) : Prop :=
  (T ==>(i,d) U) ∧ (U ==>(i,d) T).
Infix "<==>{ j , k } ( i , d )" := (tbitrans d i (j:=j) (k:=k))
  (at level 99, no associativity, only parsing) : nola_scope.
Notation "T <==>( i , d ) U" := (tbitrans d i T U)
  (at level 99, no associativity, format "T  <==>( i , d )  U") : nola_scope.

(** Typed object *)
Definition tobj_def `{!tintpGS L Σ} {i} (v : val) (T : type i (;ᵞ)) : iProp Σ :=
  ⟦ T ⟧ v.
Definition tobj_aux : seal (@tobj_def). Proof. by eexists. Qed.
Definition tobj `{!tintpGS L Σ} {i} := tobj_aux.(unseal) L Σ _ i.
Lemma tobj_unseal : @tobj = @tobj_def. Proof. exact tobj_aux.(seal_eq). Qed.
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
