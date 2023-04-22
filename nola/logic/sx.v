
(** * [nsx]: Syntactic extension for [nProp] *)

From nola Require Export prelude.

(** ** [nesx]: Elemental syntactic extension *)

#[projections(primitive)]
Structure nesx : Type := Nesx {
  (** Proposition data *)
  nesx_d :> Type;
  (** Parameter for usual [nPropS]/[nPropL] arguments *)
  #[canonical=no] nesx_pu : nesx_d → Type;
  (** Parameter for nominal [nPropS] arguments *)
  #[canonical=no] nesx_pns : nesx_d → Type;
  (** Parameter for nominal [nPropL] arguments *)
  #[canonical=no] nesx_pnl : nesx_d → Type;
}.
Add Printing Constructor nesx.

Arguments nesx_pu {Ξ} d : rename.
Arguments nesx_pns {Ξ} d : rename.
Arguments nesx_pnl {Ξ} d : rename.

(** ** [nesxsum]: Sum of [nesx]s *)

Section nesxsum.
  Context {I : Type} {Ξs : I → nesx}.

  #[projections(primitive)]
  Record nesxsum := Nesxsum {
    (** Index *)
    nesxsum_i : I;
    (** Proposition data *)
    nesxsum_d : Ξs nesxsum_i;
  }.
  Add Printing Constructor nesxsum.

  Canonical nesxsum_nesx := Nesx nesxsum
    (λ '(Nesxsum i d), (Ξs i).(nesx_pu) d)
    (λ '(Nesxsum i d), (Ξs i).(nesx_pns) d)
    (λ '(Nesxsum i d), (Ξs i).(nesx_pnl) d).
End nesxsum.

Arguments nesxsum {I} Ξs.

(** ** [nsubesx]: Inclusion between [nesx]s *)

Class nsubesx {Ξ' Ξ : nesx} : Type := Nsubesx {
  (** Inclusion between [nesx_d] *)
  nsubesx_d : Ξ'.(nesx_d) → Ξ.(nesx_d);
  (** Inclusion between [nesx_pu] *)
  nsubesx_pu d : Ξ.(nesx_pu) (nsubesx_d d) → Ξ'.(nesx_pu) d;
  (** Inclusion between [nesx_pns] *)
  nsubesx_pns d : Ξ.(nesx_pns) (nsubesx_d d) → Ξ'.(nesx_pns) d;
  (** Inclusion between [nesx_pnl] *)
  nsubesx_pnl d : Ξ.(nesx_pnl) (nsubesx_d d) → Ξ'.(nesx_pnl) d;
}.
Add Printing Constructor nsubesx.
Arguments nsubesx Ξ' Ξ : clear implicits.
Arguments Nsubesx {Ξ' Ξ}.

Notation "Ξ' ⊑esx Ξ" := (nsubesx Ξ' Ξ) (at level 70, no associativity)
  : nola_scope.

(** Identity [⊑esx] *)
#[export] Instance nsubesx_id {Ξ} : Ξ ⊑esx Ξ :=
  Nsubesx id (λ _, id) (λ _, id) (λ _, id).

(** Compose [⊑esx]s *)
Definition nsubesx_comp {Ξ'' Ξ' Ξ} (f : Ξ'' ⊑esx Ξ') (g : Ξ' ⊑esx Ξ)
  : Ξ'' ⊑esx Ξ := Nsubesx (g.(nsubesx_d) ∘ f.(nsubesx_d))
  (λ d, f.(nsubesx_pu) d ∘ g.(nsubesx_pu) (f.(nsubesx_d) d))
  (λ d, f.(nsubesx_pns) d ∘ g.(nsubesx_pns) (f.(nsubesx_d) d))
  (λ d, f.(nsubesx_pnl) d ∘ g.(nsubesx_pnl) (f.(nsubesx_d) d)).

(** Inclusion into [nesxsum] *)
Definition nsubesx_nessum {I Ξs} (i : I) : Ξs i ⊑esx nesxsum Ξs :=
  Nsubesx (Nesxsum i) (λ _, id) (λ _, id) (λ _, id).

(** ** [nsx]: Syntactic extension for [nProp] *)

#[projections(primitive)]
Record nsx : Type := Nsx {
  (** For both [nPropS] and [nPropL] *)
  nsx_s : nesx;
  (** For [nPropL] only *)
  nsx_l : nesx;
}.
Add Printing Constructor nsx.
