(** * [nctx]: Context of [nProp] *)

From nola.util Require Export tlist.

(** ** [nvar]: Variable *)

Variant nvar :=
| nvar_ns : Type → nvar
| nvar_nl : Type → nvar.

(** Notations for [nvar] *)
Notation "A →nS" := (nvar_ns A) (at level 1) : nola_scope.
Notation "A →nL" := (nvar_nl A) (at level 1) : nola_scope.
Notation nS := (nvar_ns unit).
Notation nL := (nvar_nl unit).

(** ** [narg], [nargs]: Argument to [nvar] *)

(** [narg]: Argument to [nvar] *)

Variant narg : nvar → Type :=
| narg_s {A} : A → narg (A →nS)
| narg_l {A} : A → narg (A →nL).

Notation "!ₛ a" := (narg_s a) (at level 20, right associativity) : nola_scope.
Notation "!ₗ a" := (narg_l a) (at level 20, right associativity) : nola_scope.

(** [nargo]: Argument to outer [nvar] *)

Variant nargo : nvar → Type :=
| nargo_s {A} : A → nargo (A →nS).

Notation "!ₒₛ a" := (nargo_s a) (at level 20, right associativity) : nola_scope.

(** ** [nctx]: Context of [nProp] *)

#[projections(primitive)]
Record nctx : Type := Nctx {
  (** Outer variables *)
  nctx_o : tlist nvar;
  (** Inner variables *)
  nctx_i : tlist nvar;
}.

(** Notations for [nctx] *)
Declare Scope nctx_scope.
Delimit Scope nctx_scope with nctx.
Bind Scope nctx_scope with nctx.
Notation "( Γₒ ; Γᵢ )" := (Nctx Γₒ Γᵢ) : nctx_scope.
Notation "( Γₒ ; )" := (Nctx Γₒ ^[]) : nctx_scope.
Notation "( ; Γᵢ )" := (Nctx ^[] Γᵢ) (format "( ;  Γᵢ )") : nctx_scope.
Notation "( ; )" := (Nctx ^[] ^[] ^[] ^[]) (format "( ; )") : nctx_scope.
