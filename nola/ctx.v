(** * [ctx]: Context with unguarded/guarded variables *)

From nola Require Export util.list.

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

Definition app_eq_nil_d {A} {Γᵘ Γᵍ : list A} (gn : Γᵍ = [])
  : Γᵘ ++ Γᵍ = Γᵘ := eq_trans (f_equal _ gn) app_nil_d.
Definition app_assoc'_g {A} {Γᵘ Γᵍ Δ : list A}
  : (;ᵞ (Γᵘ ++ Γᵍ) ++ Δ) = (;ᵞ Γᵘ ++ (Γᵍ ++ Δ)) :=
  ctxeq_g (eq_sym app_assoc_d).
Definition app_assoc_eq_nil_g {A} {Γᵘ Γᵍ Δᵘ Δᵍ : list A} (gn : Γᵍ = [])
  : (;ᵞ (Γᵘ ++ Γᵍ) ++ Δᵘ ++ Δᵍ) = (;ᵞ (Γᵘ ++ Δᵘ) ++ Δᵍ) :=
  ctxeq_g (eq_trans (f_equal (.++ _) (app_eq_nil_d gn)) app_assoc_d).
Definition take_add_app_g {A i} {Γᵘ Γᵍ : list A}
  : (;ᵞ take (length Γᵘ + i) (Γᵘ ++ Γᵍ)) = (;ᵞ Γᵘ ++ take i Γᵍ) :=
  ctxeq_g take_add_app_d.
Definition drop_add_app'_d {A i} {Γᵘ Γᵍ : list A}
  : drop i Γᵍ = drop (length Γᵘ + i) (Γᵘ ++ Γᵍ) := eq_sym drop_add_app_d.
Definition f_app_eq_nil_out_g {A Γᵘ Γᵍ} {f : list A → list A} (gn : Γᵍ = [])
  : (;ᵞ f (Γᵘ ++ Γᵍ)) = (;ᵞ f Γᵘ ++ []) :=
  ctxeq_g (eq_trans (f_equal _ (app_eq_nil_d gn)) (eq_sym app_nil_d)).
Definition f_app_eq_nil_d {A Γᵘ Γᵍ} {f : list A → list A} (gn : Γᵍ = [])
  : f Γᵘ = f (Γᵘ ++ Γᵍ) :=
  eq_sym (f_equal _ (app_eq_nil_d gn)).
Definition app_eq_nil_ug_g {A} {Γᵘ Γᵍ : list A} (un : Γᵘ = []) (gn : Γᵍ = [])
  : (;ᵞ Γᵘ ++ Γᵍ) = (;ᵞ) := ctxeq_g (eq_trans (f_equal (.++ _) un) gn).
