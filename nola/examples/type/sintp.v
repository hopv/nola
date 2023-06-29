(** * Strong interpretation *)

From nola.examples.type Require Export intp.

(** Namespaces *)
Definition trefN := nroot .@ "tref".
Definition tguardN := nroot .@ "tguard".

(** ** [tacc]: Accessor for [tinvd] *)
Definition tacc `{!tintpGS L Σ} {i} (s : tsintp_ty Σ) (Tx : tinvd i)
  : iProp Σ :=
  match Tx with
  | tinvd_ref l T => |=[tinv_wsat s (S i)]{⊤,⊤∖↑trefN}=> ∃ v,
      l ↦ v ∗ ⟦ T ⟧(s) v ∗
      (∀ w, l ↦ w -∗ ⟦ T ⟧(s) w =[tinv_wsat s (S i)]{⊤∖↑trefN,⊤}=∗ True)
  | tinvd_guard T v => ∀ E, ⌜↑tguardN ⊆ E⌝ →
      |=[tinv_wsat s (S i)]{E}=> ⟦ T ⟧(s) v
  end%I.

(** ** [tintpsi]: [inpsi] for [tinvd] *)
Definition tintpsi Σ `{!tintpGS L Σ} : intpsi :=
  Intpsi (tintps Σ) (λ s '(Sarg _ (existT _ Tx)), tacc s Tx).

(** Notation for [tintpsi] *)
Notation tsintpy Σ := (sintpy (tintpsi Σ)).
Notation tsintp := (sintp (ITI:=tintpsi _)).
Notation tssound := (ssound (ITI:=tintpsi _)).
Notation tsintp_sound := (sintp_sound (ITI:=tintpsi _)).

(** Utility for [tsintp] *)
Notation trefs := (tref tsintp).
Notation tguards := (tguard tsintp).
Notation "⟦ T ⟧{ i }" := ⟦ T ⟧{i}(tsintp) (only parsing) : nola_scope.
Notation "⟦ T ⟧" := ⟦ T ⟧(tsintp) : nola_scope.
Notation tinv_wsats M := (tinv_wsat tsintp M).
Notation tninv_wsats i := (tninv_wsat tsintp i).

(** ** Type judgments *)

(** Subtyping *)
Definition tsub `{!tintpGS L Σ} s {i j} (T : type i (;ᵞ)) (U : type j (;ᵞ))
  : Prop := ∀ v, ⟦ T ⟧(s) v ⊢ ⟦ U ⟧(s) v.
Infix "⊑{ i , j } ( s )" := (tsub s (i:=i) (j:=j))
  (at level 99, no associativity, only parsing) : nola_scope.
Notation "T ⊑( s ) U" := (tsub s T U)
  (at level 99, no associativity, format "T  ⊑( s )  U") : nola_scope.

(** Type equivalence *)
Definition teqv `{!tintpGS L Σ} s {i j} (T : type i (;ᵞ)) (U : type j (;ᵞ))
  : Prop := ∀ v, ⟦ T ⟧(s) v ⊣⊢ ⟦ U ⟧(s) v.
Infix "≃{ i , j } ( s )" := (teqv s (i:=i) (j:=j))
  (at level 99, no associativity, only parsing) : nola_scope.
Notation "T ≃( s ) U" := (teqv s T U)
  (at level 99, no associativity, format "T  ≃( s )  U") : nola_scope.

(** Type transmutation *)
Definition ttrans `{!tintpGS L Σ} s (i : nat)
  {j k} (T : type j (;ᵞ)) (U : type k (;ᵞ)) : Prop :=
  ∀ E v, ↑tguardN ⊆ E → ⟦ T ⟧(s) v =[tinv_wsat s i]{E}=∗ ⟦ U ⟧(s) v.
Infix "==>{ j , k } ( i , s )" := (ttrans s i (j:=j) (k:=k))
  (at level 99, no associativity, only parsing) : nola_scope.
Notation "T ==>( i , s ) U" := (ttrans s i T U)
  (at level 99, no associativity, format "T  ==>( i , s )  U") : nola_scope.

Definition tbitrans `{!tintpGS L Σ} s (i : nat)
  {j k} (T : type j (;ᵞ)) (U : type k (;ᵞ)) : Prop :=
  (T ==>(i,s) U) ∧ (U ==>(i,s) T).
Infix "<==>{ j , k } ( i , s )" := (tbitrans s i (j:=j) (k:=k))
  (at level 99, no associativity, only parsing) : nola_scope.
Notation "T <==>( i , s ) U" := (tbitrans s i T U)
  (at level 99, no associativity, format "T  <==>( i , s )  U") : nola_scope.

(** Typed object *)
Notation tobj i v T := (⟦ T ⟧{i} v).
Infix ":ᵒ{ i }" := (tobj i) (at level 70, no associativity) : nola_scope.
Infix ":ᵒ" := (tobj _) (at level 70, no associativity) : nola_scope.

(** Typed expression *)
Notation texpr i j e T :=
  (WP[tinv_wsats i] e [{ v, |=[tinv_wsats i]{⊤}=> ⟦ T ⟧{j} v }])%I.
Infix ":ᵉ{ j } ( i )" := (texpr i j) (at level 70, no associativity)
  : nola_scope.
Notation "e :ᵉ( i ) T" := (texpr i _ e T)
  (at level 70, no associativity, format "e  :ᵉ( i )  T") : nola_scope.
