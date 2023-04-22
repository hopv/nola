(** * [nctx]: Context of [nProp] *)

From nola.util Require Export tlist.

(** ** [nctx]: Context of [nProp] *)

#[projections(primitive)]
Record nctx : Type := Nctx {
  (** Outer small proposition variables *)
  nctx_os : Types;
  (** Inner small proposition variables *)
  nctx_s : Types;
  (** Outer large proposition variables *)
  nctx_ol : Types;
  (** Inner large proposition variables *)
  nctx_l : Types;
}.

(** Notations for [nctx] *)

Declare Scope nctx_scope.
Delimit Scope nctx_scope with nctx.
Bind Scope nctx_scope with nctx.

Notation "( Γₒₛ , Γₛ ; Γₒₗ , Γₗ )" := (Nctx Γₒₛ Γₛ Γₒₗ Γₗ) : nctx_scope.
Notation "( Γₛ ; Γₗ )" := (Nctx ^[] Γₛ ^[] Γₗ) : nctx_scope.
Notation "( Γₒₛ , ; Γₒₗ , )" := (Nctx Γₒₛ ^[] Γₒₗ ^[]) : nctx_scope.
Notation "( Γₒₛ , Γₛ ; )" := (Nctx Γₒₛ Γₛ ^[] ^[]) : nctx_scope.
Notation "( Γₛ ; )" := (Nctx ^[] Γₛ ^[] ^[]) : nctx_scope.
Notation "( ; Γₒₗ , Γₗ )" := (Nctx ^[] ^[] Γₒₗ Γₗ)
  (format "( ;  Γₒₗ ,  Γₗ )") : nctx_scope.
Notation "( ; Γₗ )" := (Nctx ^[] ^[] ^[] Γₗ) (format "( ;  Γₗ )") : nctx_scope.
Notation "( ; )" := (Nctx ^[] ^[] ^[] ^[]) (format "( ; )") : nctx_scope.
