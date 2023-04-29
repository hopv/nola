(** * Conversion of [nProp] *)

From nola.logic Require Export prop.
From nola.util Require Import funext.
Import EqNotations.

(** ** [nlarge]: Turn [nProp Ξ σ Γ] into [nPropL Ξ Γ]

  Although the main interest is the case [σ = nS],
  we keep the function polymorphic over [σ] for ease of definition *)

Fixpoint nlarge {Ξ σ Γ} (P : nProp Ξ σ Γ) : nPropL Ξ Γ :=
  match P with
  | %ᵢₛ a => %ᵢₛ a
  | %ᵢₗ a => %ᵢₗ a
  | %ₒₛ a => %ₒₛ a
  | P ⊢!{i} Q => P ⊢!{i} Q
  | ⌜φ⌝ => ⌜φ⌝
  | P ∧ Q => nlarge P ∧ nlarge Q
  | P ∨ Q => nlarge P ∨ nlarge Q
  | P → Q => nlarge P → nlarge Q
  | P ∗ Q => nlarge P ∗ nlarge Q
  | P -∗ Q => nlarge P -∗ nlarge Q
  | ∀' Φ => ∀' nlarge ∘ Φ
  | ∃' Φ => ∃' nlarge ∘ Φ
  | ∀: V, P => ∀: V, nlarge P
  | ∃: V, P => ∃: V, nlarge P
  | □ P => □ nlarge P
  | ■ P => ■ nlarge P
  | ▷ P => ▷ P
  | |==> P => |==> nlarge P
  | +!! (d; Φᵤ; Φₙₛ; Φₙₗ) => +!! (d; nlarge ∘ Φᵤ; Φₙₛ; Φₙₗ)
  | +!!ₗ (d; Φᵤ; Φₙₛ; Φₙₗ) => +!!ₗ (d; nlarge ∘ Φᵤ; Φₙₛ; Φₙₗ)
  end%n.

(** ** [Nsmall]: [nPropL] that can be turned into [nPropS] *)

Class Nsmall {Ξ Γ} (P : nPropL Ξ Γ) := {
  (** [nsmall]: Turn [P : nPropL] into [nPropS] *)
  nsmall : nPropS Ξ Γ;
  (** [nlarge (nsmall P) = P] *)
  nsmall_eq : nlarge nsmall = P
}.
Arguments nsmall {Ξ Γ} P {_}.

(** [Nsmall] instances *)

#[export] Instance nsmall_nlarge {Ξ Γ P} : @Nsmall Ξ Γ (nlarge P) | 100 :=
  { nsmall := P; nsmall_eq := eq_refl }.
#[export] Instance nsmall_varis {Ξ Γ a} : @Nsmall Ξ Γ (%ᵢₛ a) :=
  { nsmall := %ᵢₛ a; nsmall_eq := eq_refl }.
#[export] Instance nsmall_deriv {Ξ Γ I i P Q} : @Nsmall Ξ Γ (P ⊢!{i @ I} Q) :=
  { nsmall := P ⊢!{i} Q; nsmall_eq := eq_refl }.
#[export] Instance nsmall_pure {Ξ Γ φ} : @Nsmall Ξ Γ ⌜φ⌝ :=
  { nsmall := ⌜φ⌝; nsmall_eq := eq_refl }.
#[export] Program Instance nsmall_and {Ξ Γ} `{!Nsmall P, !Nsmall Q}
  : @Nsmall Ξ Γ (P ∧ Q) := { nsmall := nsmall P ∧ nsmall Q }.
Next Obligation. move=>/= >. by rewrite !nsmall_eq. Qed.
#[export] Program Instance nsmall_or {Ξ Γ} `{!Nsmall P, !Nsmall Q}
  : @Nsmall Ξ Γ (P ∨ Q) := { nsmall := nsmall P ∨ nsmall Q }.
Next Obligation. move=>/= >. by rewrite !nsmall_eq. Qed.
#[export] Program Instance nsmall_impl {Ξ Γ} `{!Nsmall P, !Nsmall Q}
  : @Nsmall Ξ Γ (P → Q) := { nsmall := nsmall P → nsmall Q }.
Next Obligation. move=>/= >. by rewrite !nsmall_eq. Qed.
#[export] Program Instance nsmall_sep {Ξ Γ} `{!Nsmall P, !Nsmall Q}
  : @Nsmall Ξ Γ (P ∗ Q) := { nsmall := nsmall P ∗ nsmall Q }.
Next Obligation. move=>/= >. by rewrite !nsmall_eq. Qed.
#[export] Program Instance nsmall_wand {Ξ Γ} `{!Nsmall P, !Nsmall Q}
  : @Nsmall Ξ Γ (P -∗ Q) := { nsmall := nsmall P -∗ nsmall Q }.
Next Obligation. move=>/= >. by rewrite !nsmall_eq. Qed.
#[export] Program Instance nsmall_forall {Ξ Γ} `{!∀ x : A, Nsmall (Φ x)}
  : @Nsmall Ξ Γ (∀' Φ) := { nsmall := ∀ x, nsmall (Φ x) }.
Next Obligation. move=>/= >. f_equal. funext=>/= ?. by rewrite nsmall_eq. Qed.
#[export] Program Instance nsmall_exist {Ξ Γ} `{!∀ x : A, Nsmall (Φ x)}
  : @Nsmall Ξ Γ (∃' Φ) := { nsmall := ∃ x, nsmall (Φ x) }.
Next Obligation. move=>/= >. f_equal. funext=>/= ?. by rewrite nsmall_eq. Qed.
#[export] Program Instance nsmall_n_forall {Ξ Γ V} `{!Nsmall P}
  : @Nsmall Ξ Γ (∀: V, P) := { nsmall := ∀: V, nsmall P }.
Next Obligation. move=>/= >. by rewrite nsmall_eq. Qed.
#[export] Program Instance nsmall_n_exist {Ξ Γ V} `{!Nsmall P}
  : @Nsmall Ξ Γ (∃: V, P) := { nsmall := ∃: V, nsmall P }.
Next Obligation. move=>/= >. by rewrite nsmall_eq. Qed.
#[export] Program Instance nsmall_persistently {Ξ Γ} `{!Nsmall P}
  : @Nsmall Ξ Γ (□ P) := { nsmall := □ nsmall P }.
Next Obligation. move=>/= >. by rewrite nsmall_eq. Qed.
#[export] Program Instance nsmall_plainly {Ξ Γ} `{!Nsmall P}
  : @Nsmall Ξ Γ (■ P) := { nsmall := ■ nsmall P }.
Next Obligation. move=>/= >. by rewrite nsmall_eq. Qed.
#[export] Program Instance nsmall_later {Ξ Γ P}
  : @Nsmall Ξ Γ (▷ P) := { nsmall := ▷ P; nsmall_eq := eq_refl }.
#[export] Program Instance nsmall_bupd {Ξ Γ} `{!Nsmall P}
  : @Nsmall Ξ Γ (|==> P) := { nsmall := |==> nsmall P }.
Next Obligation. move=>/= >. by rewrite nsmall_eq. Qed.
#[export] Program Instance nsmall_sxs {Ξ Γ d Φₙₛ Φₙₗ}
  `{!∀ x, Nsmall (Φᵤ x)} : @Nsmall Ξ Γ (+!! (d; Φᵤ; Φₙₛ; Φₙₗ)) :=
  { nsmall := +!! (d; λ x, nsmall (Φᵤ x); Φₙₛ; Φₙₗ) }.
Next Obligation. move=>/= >. f_equal. funext=>/= ?. by rewrite nsmall_eq. Qed.

(** ** [nrewi eq P]: Rewrite the inner context of [P : nProp] with [eq] *)

Notation nrewi eq P := (rew[λ Γᵢ, nProp _ _ (; Γᵢ)] eq in P) (only parsing).

(** ** [ninserti], [ninserto]: Insert a variable to [nProp] *)

(** [ninserti]: Insert an inner variable to [nProp] *)

Fixpoint ninserti {Ξ σ Γₒ Γᵢ} (V : npvar) (i : nat) (P : nProp Ξ σ (Γₒ; Γᵢ))
  : nProp Ξ σ (Γₒ; tinsert V i Γᵢ) :=
  match P with
  | %ᵢₛ a => %ᵢₛ cinsert V i a
  | %ᵢₗ a => %ᵢₗ cinsert V i a
  | %ₒₛ a => %ₒₛ a
  | P ⊢!{j} Q =>
      nrewi tinsert_lapp (ninserti V _ P) ⊢!{j}
        nrewi tinsert_lapp (ninserti V _ Q)
  | ⌜φ⌝ => ⌜φ⌝
  | P ∧ Q => ninserti V i P ∧ ninserti V i Q
  | P ∨ Q => ninserti V i P ∨ ninserti V i Q
  | P → Q => ninserti V i P → ninserti V i Q
  | P ∗ Q => ninserti V i P ∗ ninserti V i Q
  | P -∗ Q => ninserti V i P -∗ ninserti V i Q
  | ∀' Φ => ∀ a, ninserti V i (Φ a)
  | ∃' Φ => ∃ a, ninserti V i (Φ a)
  | ∀: W, P => ∀: W, ninserti V i P
  | ∃: W, P => ∃: W, ninserti V i P
  | □ P => □ ninserti V i P
  | ■ P => ■ ninserti V i P
  | ▷ P => ▷ nrewi tinsert_lapp (ninserti V _ P)
  | |==> P => |==> ninserti V i P
  | +!! (d; Φᵤ; Φₙₛ; Φₙₗ) => +!! (d; λ a, ninserti V i (Φᵤ a);
      λ a, nrewi tinsert_lapp (ninserti V _ (Φₙₛ a));
      λ a, nrewi tinsert_lapp (ninserti V _ (Φₙₗ a)))
  | +!!ₗ (d; Φᵤ; Φₙₛ; Φₙₗ) => +!!ₗ (d; λ a, ninserti V i (Φᵤ a);
      λ a, nrewi tinsert_lapp (ninserti V _ (Φₙₛ a));
      λ a, nrewi tinsert_lapp (ninserti V _ (Φₙₗ a)))
  end%n.

(** [naddi]: Add an inner variable to [nProp] *)

Definition naddi {Ξ σ Γₒ Γᵢ} (V : npvar) (P : nProp Ξ σ (Γₒ; Γᵢ))
  : nProp Ξ σ (Γₒ; V ^:: Γᵢ) := ninserti V 0 P.

(** [ninserto]: Insert an outer variable to [nProp] *)

Fixpoint ninserto {Ξ σ Γₒ Γᵢ} (V : npvar) (i : nat) (P : nProp Ξ σ (Γₒ; Γᵢ))
  : nProp Ξ σ (tinsert V i Γₒ; Γᵢ) :=
  match P with
  | %ᵢₛ a => %ᵢₛ a
  | %ᵢₗ a => %ᵢₗ a
  | %ₒₛ a => %ₒₛ cinsert V i a
  | P ⊢!{j} Q =>
      nrewi tinsert_rapp (ninserti V _ P) ⊢!{j}
        nrewi tinsert_rapp (ninserti V _ Q)
  | ⌜φ⌝ => ⌜φ⌝
  | P ∧ Q => ninserto V i P ∧ ninserto V i Q
  | P ∨ Q => ninserto V i P ∨ ninserto V i Q
  | P → Q => ninserto V i P → ninserto V i Q
  | P ∗ Q => ninserto V i P ∗ ninserto V i Q
  | P -∗ Q => ninserto V i P -∗ ninserto V i Q
  | ∀' Φ => ∀ a, ninserto V i (Φ a)
  | ∃' Φ => ∃ a, ninserto V i (Φ a)
  | ∀: W, P => ∀: W, ninserto V (S i) P
  | ∃: W, P => ∃: W, ninserto V (S i) P
  | □ P => □ ninserto V i P
  | ■ P => ■ ninserto V i P
  | ▷ P => ▷ nrewi tinsert_rapp (ninserti V _ P)
  | |==> P => |==> ninserto V i P
  | +!! (d; Φᵤ; Φₙₛ; Φₙₗ) => +!! (d; λ a, ninserto V i (Φᵤ a);
      λ a, nrewi tinsert_rapp (ninserti V _ (Φₙₛ a));
      λ a, nrewi tinsert_rapp (ninserti V _ (Φₙₗ a)))
  | +!!ₗ (d; Φᵤ; Φₙₛ; Φₙₗ) =>
      +!!ₗ (d; λ a, ninserto V i (Φᵤ a);
        λ a, nrewi tinsert_rapp (ninserti V _ (Φₙₛ a));
        λ a, nrewi tinsert_rapp (ninserti V _ (Φₙₗ a)))
  end%n.

(** [naddo]: Add an outer variable to [nProp] *)

Definition naddo {Ξ σ Γₒ Γᵢ} (V : npvar) (P : nProp Ξ σ (Γₒ; Γᵢ))
  : nProp Ξ σ (V ^:: Γₒ; Γᵢ) := ninserto V 0 P.
