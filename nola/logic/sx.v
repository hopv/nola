
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

(** ** [Nsubesx]: Inclusion between [nesx]s *)

Class Nsubesx (Ξ' Ξ : nesx) := {
  (** Inclusion between [nesx_d] *)
  nsubesx_d : Ξ'.(nesx_d) → Ξ.(nesx_d);
  (** Inclusion between [nesx_pu] *)
  nsubesx_pu d : Ξ.(nesx_pu) (nsubesx_d d) → Ξ'.(nesx_pu) d;
  (** Inclusion between [nesx_pns] *)
  nsubesx_pns d : Ξ.(nesx_pns) (nsubesx_d d) → Ξ'.(nesx_pns) d;
  (** Inclusion between [nesx_pnl] *)
  nsubesx_pnl d : Ξ.(nesx_pnl) (nsubesx_d d) → Ξ'.(nesx_pnl) d;
}.
Notation "Ξ' ⊑esx Ξ" := (Nsubesx Ξ' Ξ) (at level 70, no associativity)
  : nola_scope.

(** [⊑esx] is reflexive *)
#[export] Instance Nsubesx_refl {Ξ} : Ξ ⊑esx Ξ := {
  nsubesx_d := id;
  nsubesx_pu _ := id; nsubesx_pns _ := id; nsubesx_pnl _ := id;
}.

(** ** [nsx]: Syntactic extension for [nProp] *)

#[projections(primitive)]
Record nsx : Type := Nsx {
  (** For both [nPropS] and [nPropL] *)
  nsx_s : nesx;
  (** For [nPropL] only *)
  nsx_l : nesx;
}.
Add Printing Constructor nsx.
