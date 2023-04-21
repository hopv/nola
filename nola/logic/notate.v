(** * Notations for [nPropS]/[nPropL] connectives *)

From nola.logic Require Export prop.
From iris.bi Require Import notation.

Declare Scope nPropS_scope.
Delimit Scope nPropS_scope with nS.
Bind Scope nPropS_scope with nPropS.

Declare Scope nPropL_scope.
Delimit Scope nPropL_scope with nL.
Bind Scope nPropL_scope with nPropL.

Notation "%ₛ a" := (ns_vars a) (at level 99, no associativity) : nPropS_scope.
Notation "%ₛ a" := (nl_vars a) (at level 99, no associativity) : nPropL_scope.
Notation "%ₗ a" := (ns_varl a) (at level 99, no associativity) : nPropS_scope.
Notation "%ₗ a" := (nl_varl a) (at level 99, no associativity) : nPropL_scope.
Notation "%ₒₛ a" := (nl_varos a) (at level 99, no associativity) : nPropL_scope.

Notation "P ⊢!{ i @ I }{ Γₒₛ ; Γₒₗ } Q" := (ns_deriv Γₒₛ Γₒₗ I i P Q)
  (at level 99, Q at level 200, only parsing) : nPropS_scope.
Notation "P ⊢!{ i @ I }{ Γₒₛ ; Γₒₗ } Q" := (nl_deriv Γₒₛ Γₒₗ I i P Q)
  (only parsing): nPropL_scope.
Notation "P ⊢!{ i }{ Γₒₛ ; Γₒₗ } Q " := (ns_deriv Γₒₛ Γₒₗ _ i P Q)
  (at level 99, Q at level 200, only parsing) : nPropS_scope.
Notation "P ⊢!{ i }{ Γₒₛ ; Γₒₗ } Q" := (nl_deriv Γₒₛ Γₒₗ _ i P Q)
  (only parsing): nPropL_scope.
Notation "P ⊢!{ i @ I }{ Γₒₛ } Q" := (ns_deriv Γₒₛ _ I i P Q)
  (at level 99, Q at level 200, only parsing) : nPropS_scope.
Notation "P ⊢!{ i @ I }{ Γₒₛ } Q" := (nl_deriv Γₒₛ _ I i P Q)
  (only parsing): nPropL_scope.
Notation "P ⊢!{ i }{ Γₒₛ } Q " := (ns_deriv Γₒₛ _ _ i P Q)
  (at level 99, Q at level 200, only parsing) : nPropS_scope.
Notation "P ⊢!{ i }{ Γₒₛ } Q" := (nl_deriv Γₒₛ _ _ i P Q)
  (only parsing): nPropL_scope.
Notation "P ⊢!{ i @ I } Q" := (ns_deriv _ _ I i P Q)
  (at level 99, Q at level 200, only parsing) : nPropS_scope.
Notation "P ⊢!{ i @ I } Q" := (nl_deriv _ _ I i P Q)
  (only parsing): nPropL_scope.
Notation "P ⊢!{ i } Q" := (ns_deriv _ _ _ i P Q)
  (at level 99, Q at level 200, format "P  ⊢!{ i }  Q") : nPropS_scope.
Notation "P ⊢!{ i } Q" := (nl_deriv _ _ _ i P Q)
  (format "P  ⊢!{ i }  Q") : nPropL_scope.

Notation "'⌜' φ '⌝'" := (ns_pure φ%type%stdpp%nola) : nPropS_scope.
Notation "'⌜' φ '⌝'" := (nl_pure φ%type%stdpp%nola) : nPropL_scope.
Notation "'True'" := (ns_pure True) : nPropS_scope.
Notation "'True'" := (nl_pure True) : nPropL_scope.
Notation "'False'" := (ns_pure False) : nPropS_scope.
Notation "'False'" := (nl_pure False) : nPropL_scope.
Infix "∧" := ns_and : nPropS_scope.
Infix "∧" := nl_and : nPropL_scope.
Notation "(∧)" := ns_and (only parsing) : nPropS_scope.
Notation "(∧)" := nl_and (only parsing) : nPropL_scope.
Infix "∨" := ns_or : nPropS_scope.
Infix "∨" := nl_or : nPropL_scope.
Notation "(∨)" := ns_or (only parsing) : nPropS_scope.
Notation "(∨)" := nl_or (only parsing) : nPropL_scope.
Infix "→" := ns_impl : nPropS_scope.
Infix "→" := nl_impl : nPropL_scope.
Notation "¬ P" := (P → False)%nS : nPropS_scope.
Notation "¬ P" := (P → False)%nL : nPropL_scope.

Infix "∗" := ns_sep : nPropS_scope.
Infix "∗" := nl_sep : nPropL_scope.
Notation "(∗)" := ns_sep (only parsing) : nPropS_scope.
Notation "(∗)" := nl_sep (only parsing) : nPropL_scope.
Infix "-∗" := ns_wand : nPropS_scope.
Infix "-∗" := nl_wand : nPropL_scope.

Notation "∀' Φ" := (ns_forall Φ)
  (at level 200, right associativity, only parsing) : nPropS_scope.
Notation "∀' Φ" := (nl_forall Φ) (only parsing) : nPropL_scope.
Notation "∀ x .. z , P" :=
  (ns_forall (λ x, .. (ns_forall (λ z, P%nS)) ..)) : nPropS_scope.
Notation "∀ x .. z , P" :=
  (nl_forall (λ x, .. (nl_forall (λ z, P%nL)) ..)) : nPropL_scope.
Notation "∃' Φ" := (ns_exist Φ)
  (at level 200, right associativity, only parsing) : nPropS_scope.
Notation "∃' Φ" := (nl_exist Φ) (only parsing) : nPropL_scope.
Notation "∃ x .. z , P" :=
  (ns_exist (λ x, .. (ns_exist (λ z, P%nS)) ..)) : nPropS_scope.
Notation "∃ x .. z , P" :=
  (nl_exist (λ x, .. (nl_exist (λ z, P%nL)) ..)) : nPropL_scope.

Notation "∀: A →nS , P" := (ns_ns_forall A P)
  (at level 200, right associativity,
    format "'[' '[' ∀:  A  →nS ']' ,  '/' P ']'") : nPropS_scope.
Notation "∀: A →nS , P" := (nl_ns_forall A P) : nPropL_scope.
Notation "∀: 'nS' , P" := (ns_ns_forall unit P)
  (at level 200, right associativity,
    format "'[' '[' ∀:  'nS' ']' ,  '/' P ']'") : nPropS_scope.
Notation "∀: 'nS' , P" := (nl_ns_forall unit P) : nPropL_scope.
Notation "∃: A →nS , P" := (ns_ns_exist A P)
  (at level 200, right associativity,
  format "'[' '[' ∃:  A  →nS ']' ,  '/' P ']'") : nPropS_scope.
Notation "∃: A →nS , P" := (nl_ns_exist A P) : nPropL_scope.
Notation "∃: 'nS' , P" := (ns_ns_exist unit P)
  (at level 200, right associativity,
  format "'[' '[' ∃:  'nS' ']' ,  '/' P ']'") : nPropS_scope.
Notation "∃: 'nS' , P" := (nl_ns_exist unit P) : nPropL_scope.

Notation "∀: A →nL , P" := (ns_nl_forall A P)
  (at level 200, right associativity,
    format "'[' '[' ∀:  A  →nL ']' ,  '/' P ']'") : nPropS_scope.
Notation "∀: A →nL , P" := (nl_nl_forall A P) : nPropL_scope.
Notation "∀: 'nL' , P" := (ns_nl_forall unit P)
  (at level 200, right associativity,
    format "'[' '[' ∀:  'nL' ']' ,  '/' P ']'") : nPropS_scope.
Notation "∀: 'nL' , P" := (nl_nl_forall unit P) : nPropL_scope.
Notation "∃: A →nL , P" := (ns_nl_exist A P)
  (at level 200, right associativity,
  format "'[' '[' ∃:  A  →nL ']' ,  '/' P ']'") : nPropS_scope.
Notation "∃: A →nL , P" := (nl_nl_exist A P) : nPropL_scope.
Notation "∃: 'nL' , P" := (ns_nl_exist unit P)
  (at level 200, right associativity,
  format "'[' '[' ∃:  'nL' ']' ,  '/' P ']'") : nPropS_scope.
Notation "∃: 'nL' , P" := (nl_nl_exist unit P) : nPropL_scope.

Notation "□ P" := (ns_persistently P) : nPropS_scope.
Notation "□ P" := (nl_persistently P) : nPropL_scope.
Notation "■ P" := (ns_plainly P) : nPropS_scope.
Notation "■ P" := (nl_plainly P) : nPropL_scope.
Notation "▷{ Γₒₛ ; Γₒₗ } P" := (ns_later Γₒₛ Γₒₗ P)
  (at level 20, right associativity, only parsing) : nPropS_scope.
Notation "▷{ Γₒₛ ; Γₒₗ } P" := (nl_later Γₒₛ Γₒₗ P)
  (only parsing) : nPropL_scope.
Notation "▷{ Γₒₛ } P" := (ns_later Γₒₛ _ P)
  (at level 20, right associativity, only parsing) : nPropS_scope.
Notation "▷{ Γₒₛ } P" := (nl_later Γₒₛ _ P) (only parsing) : nPropL_scope.
Notation "▷ P" := (ns_later _ _ P) : nPropS_scope.
Notation "▷ P" := (nl_later _ _ P) : nPropL_scope.
Notation "|==> P" := (ns_bupd P) : nPropS_scope.
Notation "|==> P" := (nl_bupd P) : nPropL_scope.

Notation "+!! { Γₒₛ ; Γₒₗ } ( d ; Φᵤ ; Φₙₛ ; Φₙₗ )" :=
  (ns_sxs Γₒₛ Γₒₗ d Φᵤ Φₙₛ Φₙₗ) (only parsing) : nPropS_scope.
Notation "+!! { Γₒₛ ; Γₒₗ } ( d ; Φᵤ ; Φₙₛ ; Φₙₗ )" :=
  (nl_sxs Γₒₛ Γₒₗ d Φᵤ Φₙₛ Φₙₗ) (only parsing) : nPropL_scope.
Notation "+!! { Γₒₛ } ( d ; Φᵤ ; Φₙₛ ; Φₙₗ )" :=
  (ns_sxs Γₒₛ _ d Φᵤ Φₙₛ Φₙₗ) (only parsing) : nPropS_scope.
Notation "+!! { Γₒₛ } ( d ; Φᵤ ; Φₙₛ ; Φₙₗ )" :=
  (nl_sxs Γₒₛ _ d Φᵤ Φₙₛ Φₙₗ) (only parsing) : nPropL_scope.
Notation "+!! ( d ; Φᵤ ; Φₙₛ ; Φₙₗ )" := (ns_sxs _ _ d Φᵤ Φₙₛ Φₙₗ)
  : nPropS_scope.
Notation "+!! ( d ; Φᵤ ; Φₙₛ ; Φₙₗ )" := (nl_sxs _ _ d Φᵤ Φₙₛ Φₙₗ)
  : nPropL_scope.
Notation "+!!ₗ { Γₒₛ ; Γₒₗ } ( d ; Φᵤ ; Φₙₛ ; Φₙₗ )" :=
  (nl_sxl Γₒₛ Γₒₗ d Φᵤ Φₙₛ Φₙₗ) (only parsing) : nPropL_scope.
Notation "+!!ₗ { Γₒₛ } ( d ; Φᵤ ; Φₙₛ ; Φₙₗ )" :=
  (nl_sxl Γₒₛ _ d Φᵤ Φₙₛ Φₙₗ) (only parsing) : nPropL_scope.
Notation "+!!ₗ ( d ; Φᵤ ; Φₙₛ ; Φₙₗ )" := (nl_sxl _ _ d Φᵤ Φₙₛ Φₙₗ)
  : nPropL_scope.

Notation "+! { Γₒₛ ; Γₒₗ } ( d ; Φᵤ ; Φₙₛ ; Φₙₗ )" :=
  (ns_subsxs Γₒₛ Γₒₗ d Φᵤ Φₙₛ Φₙₗ) (only parsing) : nPropS_scope.
Notation "+! { Γₒₛ ; Γₒₗ } ( d ; Φᵤ ; Φₙₛ ; Φₙₗ )" :=
  (nl_subsxs Γₒₛ Γₒₗ d Φᵤ Φₙₛ Φₙₗ) (only parsing) : nPropL_scope.
Notation "+! { Γₒₛ } ( d ; Φᵤ ; Φₙₛ ; Φₙₗ )" :=
  (ns_subsxs Γₒₛ _ d Φᵤ Φₙₛ Φₙₗ) (only parsing) : nPropS_scope.
Notation "+! { Γₒₛ } ( d ; Φᵤ ; Φₙₛ ; Φₙₗ )" := (nl_subsxs Γₒₛ _ d Φᵤ Φₙₛ Φₙₗ)
  (only parsing) : nPropL_scope.
Notation "+! ( d ; Φᵤ ; Φₙₛ ; Φₙₗ )" := (ns_subsxs _ _ d Φᵤ Φₙₛ Φₙₗ)
  : nPropS_scope.
Notation "+! ( d ; Φᵤ ; Φₙₛ ; Φₙₗ )" := (nl_subsxs _ _ d Φᵤ Φₙₛ Φₙₗ)
  : nPropL_scope.
Notation "+!ₗ { Γₒₛ ; Γₒₗ } ( d ; Φᵤ ; Φₙₛ ; Φₙₗ )" :=
  (nl_subsxl Γₒₛ Γₒₗ d Φᵤ Φₙₛ Φₙₗ) (only parsing) : nPropL_scope.
Notation "+!ₗ { Γₒₛ } ( d ; Φᵤ ; Φₙₛ ; Φₙₗ )" :=
  (nl_subsxl Γₒₛ _ d Φᵤ Φₙₛ Φₙₗ) (only parsing) : nPropL_scope.
Notation "+!ₗ ( d ; Φᵤ ; Φₙₛ ; Φₙₗ )" :=
  (nl_subsxl _ _ d Φᵤ Φₙₛ Φₙₗ) : nPropL_scope.
