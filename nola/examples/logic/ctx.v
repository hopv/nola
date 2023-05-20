(** * [nctx]: Context of [nProp] *)

From nola Require Export util.list.

(** ** [nsort]: Sort of [nProp], [nS] or [nL] *)

Variant nsort : Set := (* small *) nS | (* large *) nL.

(** Equality on [nsort] is decidable *)
#[export] Instance nsort_eq_dec : EqDecision nsort.
Proof. case; case; try (by left); by right. Defined.

(** ** [npvar]: Predicate variable *)

#[projections(primitive)]
Record npvar := Npvar {
  npvar_argty : Type;
  npvar_sort : nsort;
}.

(** Notations for [npvar] *)
Notation "A →nP σ" := (Npvar A σ) (at level 1, no associativity) : nola_scope.
Notation "A →nPS" := (A →nP nS) (at level 1) : nola_scope.
Notation "A →nPL" := (A →nP nL) (at level 1) : nola_scope.
Notation nP σ := (unit →nP σ).
Notation nPS := (unit →nPS).
Notation nPL := (unit →nPL).

(** ** [nparg]: Argument to [npvar], with [nsort] specified *)

Variant nparg {σ : nsort} : npvar → Type :=
| Nparg {A} : A → nparg (A →nP σ).
Arguments nparg σ V : clear implicits.
Notation npargS := (nparg nS).
Notation npargL := (nparg nL).
Notation "@! a" := (Nparg a) (at level 20, right associativity) : nola_scope.

(** ** [nctx]: Context of [nProp] *)

#[projections(primitive)]
Record nctx : Type := Nctx {
  (** Outer (i.e., unguarded) variables *)
  nctx_o : list npvar;
  (** Inner (i.e., guarded) variables *)
  nctx_i : list npvar;
}.

(** Notations for [nctx] *)
Declare Scope nctx_scope.
Delimit Scope nctx_scope with nctx.
Bind Scope nctx_scope with nctx.
Notation "( Γᵒ ; Γⁱ )" := (Nctx Γᵒ Γⁱ) : nctx_scope.
Notation "( Γᵒ ; )" := (Nctx Γᵒ []) : nctx_scope.
Notation "( ; Γⁱ )" := (Nctx [] Γⁱ) (format "( ;  Γⁱ )") : nctx_scope.
Notation "( ; )" := (Nctx [] []) (format "( ; )") : nctx_scope.
