(** * Prophecy *)

From nola Require Export prelude.
From nola.util Require Import plist.

(** ** Syntactic pre-type and prophecy variable *)

(** Syntactic pre-type *)
#[projections(primitive)]
Structure synpty := Synpty {
  (* Syntax *) synpty_car :> Type;
  (* Equality decision over the syntax *) #[canonical=no]
    synpty_eqdec :: EqDecision synpty_car;
  (* Inhabitance predicate *) #[canonical=no] synpty_inhab : synpty_car → Prop;
  (* [synty_inhab] is proof-irrelevant *) #[canonical=no]
    synpty_inhab_irrel :: ∀ X, ProofIrrel (synpty_inhab X);
}.
Arguments synpty_eqdec {_} _. Arguments synpty_inhab {_} _.
Arguments synpty_inhab_irrel {_ _} _.

(** Prophecy variable *)
#[projections(primitive)]
Record prvar {TY : synpty} (A : TY) := Prvar {
  (* Proof of inhabitance *) prvar_inhab : synpty_inhab A;
  (* Id *) prvar_id : positive;
}.
Add Printing Constructor prvar.
Arguments prvar_inhab {_ _} _. Arguments prvar_id {_ _} _.
Arguments Prvar {_ _} _ _.

(** Equality decision over [prvar] *)
#[export] Instance prvar_eq_dec {TY : synpty} (A : TY) : EqDecision (prvar A).
Proof.
  move=> [h i] [h' j]. rewrite (proof_irrel h h'). case: (decide (i = j))=> ?.
  { subst. by left. } { right. by case. }
Defined.

(** Inhabitant of [prvar] by [synpty_inhab] *)
Definition prvar_by_inhab {TY : synpty} (X : TY) (h : synpty_inhab X)
  : prvar X := Prvar h inhabitant.

(** Negated [synpty_inhab] ensures the emptiness of [prvar] *)
Lemma prvar_neg_inhab {TY : synpty} (X : TY) :
  ¬ synpty_inhab X → prvar X → False.
Proof. move=> neg [??]. by apply neg. Qed.

(** Prophecy variable of any type *)
#[projections(primitive)]
Record aprvar (TY : synpty) := Aprvar {
  (* Type *) aprvar_ty : TY;
  (* Variable *) aprvar_var :> prvar aprvar_ty;
}.
Add Printing Constructor aprvar.
Arguments aprvar_ty {_}. Arguments aprvar_var {_}.
Arguments Aprvar {_} _ _.
Coercion Aprvar : prvar >-> aprvar.

(** Equality decision over [aprvar] *)
#[export] Instance aprvar_eq_dec {TY} : EqDecision (aprvar TY).
Proof.
  move=> [X [h i]] [Y [h' j]]. case: (decide (X = Y)); last first.
  { move=> ?. right. by case. }
  move=> ?. subst. rewrite (proof_irrel h h').
  case: (decide (i = j))=> ?. { subst. by left. } { right. by case. }
Defined.

(** Inhabitant of [aprvar] by [synpty_inhab] *)
Definition aprvar_by_inhab {TY : synpty} (X : TY) (h : synpty_inhab X)
  : aprvar TY := prvar_by_inhab X h.

(** [plist prvar] as [list aprvar] *)
Definition of_plist_prvar {TY : synpty} {Xl : list TY}
  : plist prvar Xl → list (aprvar TY) := of_plist Aprvar.

(** ** Syntactic type and prophecy assignment *)

(** Syntactic type *)
#[projections(primitive)]
Structure synty := Synty {
  (* Pre-type *) synty_pty :> synpty;
  (* Type interpretation *) #[canonical=no] synty_ty : synty_pty → Type;
  (* [synty_inhab] ensures [Inhabited] *) #[canonical=no]
    synty_inhabited {X} :: synpty_inhab X → Inhabited (synty_ty X);
  (* An inhabitant implies [synty_inhab] *) #[canonical=no]
    synty_to_inhab {X} : synty_ty X → synpty_inhab X;
}.
Arguments synty_ty {_} _. Arguments synty_inhabited {_ _} _.
Arguments synty_to_inhab {_ _} _.
#[warnings="-uniform-inheritance"] Coercion synty_ty : synpty_car >-> Sortclass.

Implicit Type TY : synty.

(** Prophecy assignment *)
Definition proph_asn (TY : synty) := ∀ ξ : aprvar TY, ξ.(aprvar_ty).

(** [prvar X] entails [Inhabited X] *)
Lemma prvar_to_inhabited {TY} {X : TY} : prvar X → Inhabited X.
Proof. move=> ?. by apply synty_inhabited, prvar_inhab. Qed.

(** [proph_asn] is inhabited *)
#[export] Instance proph_asn_inhabited {TY} : Inhabited (proph_asn TY).
Proof. apply populate. move=> [??]. by apply prvar_to_inhabited. Qed.

(** Evaluate [plist prvar] with [proph_asn] *)
Definition app_plist_prvar {TY} {Xl : list TY}
  (π : proph_asn TY) (ξl : plist prvar Xl) : plist synty_ty Xl :=
  plist_map (λ _ (ξ : prvar _), π ξ) ξl.

(** ** Prophecy Dependency *)

(** Equivalence of prophecy assignments over a set of prophecy variables *)
Definition proph_asn_eqv {TY}
  (φ : aprvar TY → Prop) (π π' : proph_asn TY) :=
  ∀ ξ : aprvar TY, φ ξ → π ξ = π' ξ.
Notation "π .≡{ φ }≡ π'" := (proph_asn_eqv φ π π')
  (at level 70, format "π  .≡{ φ }≡  π'") : nola_scope.

(** Prophecy dependency *)
Definition proph_dep {TY A} (aπ : proph_asn TY → A) (ξl: list (aprvar TY)) :=
  ∀ π π', π .≡{ (.∈ ξl) }≡ π' → aπ π = aπ π'.
Notation "aπ ./ ξl" := (proph_dep aπ ξl) (at level 70, format "aπ  ./  ξl")
  : nola_scope.

(** Lemmas *)

Section lemmas.
  Context {TY}.
  Implicit Type (ξ η ζ : aprvar TY) (ξl ηl ζl : list (aprvar TY)).

  (** Monotonicity over the list set *)
  #[export] Instance proph_dep_mono {A} (aπ : proph_asn TY → A) :
    Proper ((⊆) ==> impl) (proph_dep aπ).
  Proof. move=>/= ?? sub dep ?? eqv. apply dep => ??. by apply eqv, sub. Qed.
  #[export] Instance proph_dep_mono' {A} (aπ : proph_asn TY → A) :
    Proper (flip (⊆) ==> flip impl) (proph_dep aπ).
  Proof. solve_proper. Qed.
  #[export] Instance proph_dep_proper {A} (aπ : proph_asn TY → A) :
    Proper ((≡ₚ) ==> iff) (proph_dep aπ).
  Proof. move=> ?? eq. split; apply proph_dep_mono; by rewrite eq. Qed.

  (** On a constant *)
  Lemma proph_dep_const {A} (a : A) : (λ _ : proph_asn TY, a) ./ [].
  Proof. done. Qed.

  (** On [(.$ ξ)] *)
  Lemma proph_dep_one ξ : (λ π, π ξ) ./ [ξ].
  Proof. move=> ?? eqv. apply eqv. constructor. Qed.

  (** Construct with a function *)
  Lemma proph_dep_constr {A B} (f : A → B) aπ ξl :
    aπ ./ ξl → (λ π, f (aπ π)) ./ ξl.
  Proof. move=> dep ?? /dep ?. by apply (f_equal f). Qed.
  Lemma proph_dep_constr2 {A B C} (f: A → B → C) aπ bπ ξl ηl :
    aπ ./ ξl → bπ ./ ηl → (λ π, f (aπ π) (bπ π)) ./ ξl ++ ηl.
  Proof.
    move=> dep dep' ?? eqv.
    eapply proph_dep_mono, (.$ eqv) in dep, dep'; [|set_solver..]. by f_equal.
  Qed.
  Lemma proph_dep_constr3 {A B C D} (f: A → B → C → D) aπ bπ cπ ξl ηl ζl :
    aπ ./ ξl → bπ ./ ηl → cπ ./ ζl →
    (λ π, f (aπ π) (bπ π) (cπ π)) ./ ξl ++ ηl ++ ζl.
  Proof.
    move=> dep dep' dep'' ?? eqv.
    eapply proph_dep_mono, (.$ eqv) in dep, dep', dep''; [|set_solver..].
    by f_equal.
  Qed.
  Lemma proph_dep_plist' {Xl : list TY} (ξl : plist prvar Xl) :
    (λ π, app_plist_prvar π ξl) ./ of_plist_prvar ξl.
  Proof.
    elim: Xl ξl; [done|]=>/= ?? IH [ξ ξl] ?? eqv.
    unfold app_plist_prvar=>/=. f_equal.
    { apply (eqv ξ). set_solver. } { apply IH=> ??. apply eqv. set_solver. }
  Qed.
  Lemma proph_dep_plist {A} {Xl : list TY} (f : _ → A) (ξl : plist prvar Xl) :
    (λ π, f (app_plist_prvar π ξl)) ./ of_plist_prvar ξl.
  Proof. apply proph_dep_constr, proph_dep_plist'. Qed.

  (** On a singleton type *)
  Lemma proph_dep_singleton {A} (aπ : proph_asn TY → A) :
    (∀ a a' : A, a = a') → aπ ./ [].
  Proof. by move=> ????. Qed.
End lemmas.
