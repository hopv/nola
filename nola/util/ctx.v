(** * [ctx]: Context with unguarded/guarded variables *)

From nola.util Require Export list.

(** ** [ctx]: Context with unguarded/guarded variables *)
#[projections(primitive)]
Record ctx (A : Type) : Type := Ctx {
  (** Unguarded variables *)
  ctx_u : list A;
  (** Guarded variables *)
  ctx_g : list A;
}.
Arguments Ctx {_} _ _.
Arguments ctx_u {_} _.
Arguments ctx_g {_} _.

Notation "Γ .ᵞu" := Γ.(ctx_u) (at level 2, left associativity, format "Γ .ᵞu")
  : nola_scope.
Notation "Γ .ᵞg" := Γ.(ctx_g) (at level 2, left associativity, format "Γ .ᵞg")
  : nola_scope.

Notation "( Γᵘ ;ᵞ Γᵍ )" := (Ctx Γᵘ Γᵍ) : nola_scope.
Notation "( Γᵘ ;ᵞ )" := (Ctx Γᵘ []) : nola_scope.
Notation "( ;ᵞ Γᵍ )" := (Ctx [] Γᵍ) (format "( ;ᵞ  Γᵍ )") : nola_scope.
Notation "( ;ᵞ )" := (Ctx [] []) (format "( ;ᵞ )") : nola_scope.

(** Utility for equalities over [ctx]s *)

Definition ctxeq_g {A} {Γᵘ Γᵍ Δᵍ : list A} (eg : Γᵍ = Δᵍ)
  : (Γᵘ;ᵞ Γᵍ) = (Γᵘ;ᵞ Δᵍ) := match eg with eq_refl => eq_refl end.
Definition ctxeq_ug {A} {Γᵘ Δᵘ Γᵍ Δᵍ : list A} (eu : Γᵘ = Δᵘ) (eg : Γᵍ = Δᵍ)
  : (Γᵘ;ᵞ Γᵍ) = (Δᵘ;ᵞ Δᵍ) := match eu, eg with eq_refl, eq_refl => eq_refl end.

Definition eq_app_assoc_d {A} {Γᵍ' Γᵘ Γᵍ Γˣ : list A} (eq : Γᵍ' = Γᵍ ++ Γˣ)
  : Γᵘ ++ Γᵍ' = (Γᵘ ++ Γᵍ) ++ Γˣ := eq_trans (f_equal (_ ++.) eq) app_assoc_d.
Definition eq_nil_ug_g {A} {Γᵘ Γᵍ : list A} (un : Γᵘ = []) (gn : Γᵍ = [])
  : (;ᵞ Γᵘ ++ Γᵍ) = (;ᵞ) := ctxeq_g (eq_trans (f_equal (.++ _) un) gn).
