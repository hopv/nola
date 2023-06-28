(** * Strong interpretation *)

From nola.examples.type Require Export intp.

(** ** [tacc]: Accessor for [tinvd] *)
Definition tacc `{!tintpGS L Σ} {i} (s : tsintp_ty Σ) (Tx : tinvd i)
  : iProp Σ :=
  match Tx with
  | tinvd_ref l T => |=[tinv_wsat s i]{⊤,∅}=> ∃ v, l ↦ v ∗ ⟦ T ⟧(s) v ∗
      (∀ w, l ↦ w ∗ ⟦ T ⟧(s) w =[tinv_wsat s i]{∅,⊤}=∗ True)
  | tinvd_guard T v => |=[tinv_wsat s i]{⊤}=> ⟦ T ⟧(s) v
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

(** Typed object *)
Definition tobj `{!tintpGS L Σ} {i} (v : val) (T : type i (;ᵞ)) : iProp Σ :=
  ⟦ T ⟧ v.
Infix ":ᵒ{ i }" := (tobj (i:=i)) (at level 50, no associativity) : nola_scope.
Infix ":ᵒ" := tobj (at level 50, no associativity) : nola_scope.

(** Typed expression *)
Definition texpr `{!tintpGS L Σ} (i : nat) {j} (e : expr) (T : type j (;ᵞ))
  : iProp Σ := WP[tinv_wsats i] e [{ ⟦ T ⟧ }].
Infix ":ᵉ{ j } ( i )" := (texpr i (j:=j)) (at level 50, no associativity) :
  nola_scope.
Notation "e :ᵉ( i ) T" := (texpr i e T)
  (at level 50, no associativity, format "e  :ᵉ( i )  T") : nola_scope.
