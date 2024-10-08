(** * Prophecy *)

From nola Require Export prelude.
From nola.util Require Import plist.

(** ** Syntactic pre-type *)

#[projections(primitive)]
Structure synpty := Synpty {
  (* Syntax *) synpty_car :> Type;
  (* Equality decision over the syntax *) #[canonical=no]
    synpty_eqdec :: EqDecision synpty_car;
  (* Inhabitance predicate *) #[canonical=no] synpty_inhab : synpty_car → Prop;
  (* [synty_inhab] is proof-irrelevant *) #[canonical=no]
    synpty_inhab_irrel {X} :: ProofIrrel (synpty_inhab X);
}.
Add Printing Constructor synpty.
Arguments synpty_eqdec {_} _. Arguments synpty_inhab {_} _.
Arguments synpty_inhab_irrel {_ _} _.

Implicit Type PTY : synpty.

(** ** Prophecy variable *)

#[projections(primitive)]
Record prvar {PTY} (A : PTY) := Prvar {
  (* Proof of inhabitance *) prvar_inhab : synpty_inhab A;
  (* Id *) prvar_id : positive;
}.
Add Printing Constructor prvar.
Arguments prvar_inhab {_ _} _. Arguments prvar_id {_ _} _.
Arguments Prvar {_ _} _ _.

(** Equality decision over [prvar] *)
#[export] Instance prvar_eq_dec {PTY} (A : PTY) : EqDecision (prvar A).
Proof.
  move=> [h i] [h' j]. rewrite (proof_irrel h h'). case: (decide (i = j))=> ?.
  { subst. by left. } { right. by case. }
Defined.

(** Inhabitant of [prvar] by [synpty_inhab] *)
Definition prvar_by_inhab {PTY} (X : PTY) (h : synpty_inhab X)
  : prvar X := Prvar h inhabitant.

(** Negated [synpty_inhab] ensures the emptiness of [prvar] *)
Lemma prvar_neg_inhab {PTY} (X : PTY) :
  ¬ synpty_inhab X → prvar X → False.
Proof. move=> neg [??]. by apply neg. Qed.

(** Prophecy variable of any type *)
#[projections(primitive)]
Record aprvar PTY := Aprvar {
  (* Type *) aprvar_ty : PTY;
  (* Variable *) aprvar_var :> prvar aprvar_ty;
}.
Add Printing Constructor aprvar.
Arguments Aprvar {_} _ _. Arguments aprvar_ty {_}. Arguments aprvar_var {_}.
Coercion Aprvar : prvar >-> aprvar.
Notation aprvar_id ξ := ξ.(aprvar_var).(prvar_id).

(** Equality decision over [aprvar] *)
#[export] Instance aprvar_eq_dec {PTY} : EqDecision (aprvar PTY).
Proof.
  move=> [X [h i]] [Y [h' j]]. case: (decide (X = Y)); last first.
  { move=> ?. right. by case. }
  move=> ?. subst. rewrite (proof_irrel h h').
  case: (decide (i = j))=> ?. { subst. by left. } { right. by case. }
Defined.

(** Inhabitant of [aprvar] by [synpty_inhab] *)
Definition aprvar_by_inhab {PTY} (X : PTY) (h : synpty_inhab X) : aprvar PTY :=
  prvar_by_inhab X h.

(** [plist prvar] as [list aprvar] *)
Definition of_plist_prvar {PTY} {Xl : list PTY}
  : plist prvar Xl → list (aprvar PTY) :=
  of_plist Aprvar.

(** ** Syntactic type *)

(** Syntactic type *)
#[projections(primitive)]
Structure synty := Synty {
  (* Pre-type *) synty_pty :> synpty;
  (* Type semantics *) #[canonical=no] synty_ty : synty_pty → Type;
  (* [synty_inhab] ensures [Inhabited] *) #[canonical=no]
    synty_inhabited {X} :: synpty_inhab X → Inhabited (synty_ty X);
  (* An inhabitant implies [synty_inhab] *) #[canonical=no]
    synty_to_inhab {X} : synty_ty X → synpty_inhab X;
}.
Add Printing Constructor synty.
Arguments synty_ty {_} _. Arguments synty_inhabited {_ _} _.
Arguments synty_to_inhab {_ _} _.
#[warning="-uniform-inheritance"] Coercion synty_ty : synpty_car >-> Sortclass.

Implicit Type TY : synty.

(** ** Prophecy assignment *)

(** Prophecy assignment *)
Definition proph_asn TY := ∀ ξ : aprvar TY, ξ.(aprvar_ty).

(** Clairvoyant monad, i.e., reader monad over the prophecy assignment *)
Notation clair TY A := (proph_asn TY → A).

(** [prvar X] entails [Inhabited X] *)
Lemma prvar_to_inhabited {TY} {X : TY} : prvar X → Inhabited X.
Proof. move=> ?. by apply synty_inhabited, prvar_inhab. Qed.

(** [proph_asn] is inhabited *)
#[export] Instance proph_asn_inhabited {TY} : Inhabited (proph_asn TY).
Proof. apply populate. move=> [??]. by apply prvar_to_inhabited. Qed.

(** Instantiate [plist] over [clair] with [proph_asn] *)
Definition app_plist_clair {TY} {Xl : list TY} (π : proph_asn TY)
  (xπl : plist (λ X : TY, clair TY X) Xl) : plist synty_ty Xl :=
  plist_map (λ _ xπ, xπ π) xπl.
(** Evaluate [plist prvar] with [proph_asn] *)
Definition app_plist_prvar {TY} {Xl : list TY}
  (π : proph_asn TY) (ξl : plist prvar Xl) : plist synty_ty Xl :=
  plist_map (λ _ (ξ : prvar _), π ξ) ξl.

(** ** Prophecy Dependency *)

(** Equivalence of prophecy assignments over a set of prophecy variables *)
Definition proph_asn_eqv {TY} (φ : aprvar TY → Prop) (π π' : proph_asn TY) :=
  ∀ ξ : aprvar TY, φ ξ → π ξ = π' ξ.

(** Prophecy dependency *)
Definition proph_dep {TY A} (aπ : clair TY A) (ξl: list (aprvar TY)) :=
  ∀ π π', proph_asn_eqv (.∈ ξl) π π' → aπ π = aπ π'.

(** Lemmas *)

Section lemmas.
  Context {TY}.
  Implicit Type (ξ η ζ : aprvar TY) (ξl ηl ζl : list (aprvar TY))
    (Xl : list TY).

  (** Monotonicity of [proph_dep] over the list set *)
  #[export] Instance proph_dep_mono {A} :
    Proper (pointwise_relation _ (=) ==> (⊆) ==> impl) (@proph_dep TY A).
  Proof.
    move=> ?? eq ?? sub dep ?? eqv. rewrite -eq. apply dep=> ??.
    by apply eqv, sub.
  Qed.
  #[export] Instance proph_dep_flip_mono {A} :
    Proper (pointwise_relation _ (=) ==> flip (⊆) ==> flip impl)
      (@proph_dep TY A).
  Proof. move=> ??????/=. by apply proph_dep_mono. Qed.
  #[export] Instance proph_dep_proper {A} :
    Proper (pointwise_relation _ (=) ==> (≡ₚ) ==> (↔)) (@proph_dep TY A).
  Proof. move=> ????? eq. split; apply proph_dep_mono=>//; by rewrite eq. Qed.

  (** On a constant *)
  Lemma proph_dep_const {A} a : @proph_dep A TY (λ _, a) [].
  Proof. done. Qed.

  (** On the clairvoyant value for a prophecy variable *)
  Lemma proph_dep_one ξ : proph_dep (λ π, π ξ) [ξ].
  Proof. move=> ?? eqv. apply eqv. constructor. Qed.

  (** Construct with a function *)
  Lemma proph_dep_fpi {A B} (fπ : clair TY (A → B)) aπ ξl ηl :
    (∀ a, proph_dep (λ π, fπ π a) ξl) → proph_dep aπ ηl →
      proph_dep (λ π, fπ π (aπ π)) (ξl ++ ηl).
  Proof.
    move=> dep dep' π π' eqv.
    have <-: aπ π = aπ π'. { apply dep'=> ??. apply eqv. set_solver. }
    apply dep=> ??. apply eqv. set_solver.
  Qed.
  Lemma proph_dep_f {A B} (f : A → B) aπ ξl :
    proph_dep aπ ξl → proph_dep (λ π, f (aπ π)) ξl.
  Proof. move=> dep ?? /dep ?. by apply (f_equal f). Qed.
  Lemma proph_dep_f2 {A B C} (f: A → B → C) aπ bπ ξl ηl :
    proph_dep aπ ξl → proph_dep bπ ηl →
      proph_dep (λ π, f (aπ π) (bπ π)) (ξl ++ ηl).
  Proof.
    move=> dep dep' π π' eqv.
    rewrite (dep π π') ?(dep' π π') //; move=> ??; apply eqv; set_solver.
  Qed.
  Lemma proph_dep_plist_prvar {Xl} (ξl : plist prvar Xl) :
    proph_dep (λ π, app_plist_prvar π ξl) (of_plist_prvar ξl).
  Proof.
    elim: Xl ξl; [done|]=>/= ?? IH [ξ ξl] ?? eqv.
    unfold app_plist_prvar=>/=. f_equal.
    { apply (eqv ξ). set_solver. } { apply IH=> ??. apply eqv. set_solver. }
  Qed.

  (** Destruct from an injective function *)
  Lemma proph_dep_unfpi {A B} (fπ : clair TY (A → B)) aπ ξl :
    (∀ π π' a a', fπ π a = fπ π' a' → a = a') →
    proph_dep (λ π, fπ π (aπ π)) ξl → proph_dep aπ ξl.
  Proof. by move=> inj dep ?? /dep/inj. Qed.
  Lemma proph_dep_unf {A B} f `{!@Inj A B (=) (=) f} aπ ξl :
    proph_dep (λ π, f (aπ π)) ξl → proph_dep aπ ξl.
  Proof. by apply proph_dep_unfpi. Qed.
  Lemma proph_dep_unf2 {A B C} f `{!@Inj2 A B C (=) (=) (=) f} aπ bπ ξl :
    proph_dep (λ π, f (aπ π) (bπ π)) ξl → proph_dep aπ ξl ∧ proph_dep bπ ξl.
  Proof.
    move=> dep. split; move=> ?? /dep eq; apply (inj2 f _) in eq; apply eq.
  Qed.

  (** On a singleton type *)
  Lemma proph_dep_singleton {A} (aπ : clair TY A) :
    (∀ a a' : A, a = a') → proph_dep aπ [].
  Proof. by move=> ????. Qed.
End lemmas.
