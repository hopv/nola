(** * Substitution for [nProp] *)

From nola.examples.logic Require Export prop.
Import EqNotations.

(** [nProp_rewi P eq]: Rewrite the inner context of [P : nProp (; Γᵢ)]
  using [eq] *)

Notation nProp_rewi P eq := (rew[λ Γᵢ, nProp _ (; Γᵢ)] eq in P) (only parsing).

(** ** [nlift]: Turn [nProp σ (;)] into [nProp σ Γ] *)

(** [nlifti]: Add inner variables at the bottom *)

Definition nlifti_rew {σ Γₒ Γᵢ Δ}
  (P : nProp σ (; (Γₒ ++ Γᵢ) ++ Δ)) : nProp σ (; Γₒ ++ (Γᵢ ++ Δ)) :=
  nProp_rewi P (eq_sym (app_assoc_def _ _ _)).
Fixpoint nlifti {Δ σ Γₒ Γᵢ} (P : nProp σ (Γₒ; Γᵢ)) : nProp σ (Γₒ; Γᵢ ++ Δ) :=
  match P with
  | ⌜φ⌝ => ⌜φ⌝
  | P ∧ Q => nlifti P ∧ nlifti Q
  | P ∨ Q => nlifti P ∨ nlifti Q
  | P → Q => nlifti P → nlifti Q
  | ∀' Φ => ∀' nlifti ∘ Φ
  | ∃' Φ => ∃' nlifti ∘ Φ
  | P ∗ Q => nlifti P ∗ nlifti Q
  | P -∗ Q => nlifti P -∗ nlifti Q
  | □ P => □ nlifti P
  | ■ P => ■ nlifti P
  | |==> P => |==> nlifti P
  | ▷ P => ▷ nlifti_rew (nlifti P)
  | P ⊢!{i} Q => nlifti_rew (nlifti P) ⊢!{i} nlifti_rew (nlifti Q)
  | (rec:ₛ' Φ) a => (rec:ₛ' nlifti ∘ Φ) a
  | (rec:ₗ' Φ) a => (rec:ₗ' nlifti ∘ Φ) a
  | ∀: V, P => ∀: V, nlifti P
  | ∃: V, P => ∃: V, nlifti P
  | %ᵢₛ s => %ᵢₛ cbylapp s _
  | %ᵢₗ s => %ᵢₗ cbylapp s _
  | %ₒₛ s => %ₒₛ s
  end%n.

(** [nliftoi]: Add outer and inner variables at the bottom *)
Definition nliftoi_rew {σ Γₒ Γᵢ Δₒ Δᵢ} : Γᵢ = [] →
  nProp σ (; (Γₒ ++ Γᵢ) ++ Δₒ ++ Δᵢ) → nProp σ (; (Γₒ ++ Δₒ) ++ Δᵢ) :=
  match Γᵢ with
  | _ :: _ => λ eq, match eq with end
  | [] => λ _ P, nProp_rewi P (eq_trans
      (eq_sym (app_assoc_def _ [] _)) (app_assoc_def _ Δₒ _))
  end.
Fixpoint nliftoi {Δₒ Δᵢ σ Γₒ Γᵢ} (P : nProp σ (Γₒ; Γᵢ))
  : Γᵢ = [] → nProp σ (Γₒ ++ Δₒ; Δᵢ) :=
  match P with
  | ⌜φ⌝ => λ _, ⌜φ⌝
  | P ∧ Q => λ eq, nliftoi P eq ∧ nliftoi Q eq
  | P ∨ Q => λ eq, nliftoi P eq ∨ nliftoi Q eq
  | P → Q => λ eq, nliftoi P eq → nliftoi Q eq
  | ∀' Φ => λ eq, ∀ a, nliftoi (Φ a) eq
  | ∃' Φ => λ eq, ∃ a, nliftoi (Φ a) eq
  | P ∗ Q => λ eq, nliftoi P eq ∗ nliftoi Q eq
  | P -∗ Q => λ eq, nliftoi P eq -∗ nliftoi Q eq
  | □ P => λ eq, □ nliftoi P eq
  | ■ P => λ eq, ■ nliftoi P eq
  | |==> P => λ eq, |==> nliftoi P eq
  | ▷ P => λ eq, ▷ nliftoi_rew eq (nlifti P)
  | P ⊢!{i} Q => λ eq,
      nliftoi_rew eq (nlifti P) ⊢!{i} nliftoi_rew eq (nlifti Q)
  | (rec:ₛ' Φ) a => λ eq, (rec:ₛ b, nliftoi (Φ b) eq) a
  | (rec:ₗ' Φ) a => λ eq, (rec:ₗ b, nliftoi (Φ b) eq) a
  | ∀: V, P => λ eq, ∀: V, nliftoi P eq
  | ∃: V, P => λ eq, ∃: V, nliftoi P eq
  | %ᵢₛ s => match s with
      #0 _ => λ eq, match eq with end | +/ _ => λ eq, match eq with end end
  | %ᵢₗ s => match s with
      #0 _ => λ eq, match eq with end | +/ _ => λ eq, match eq with end end
  | %ₒₛ s => λ _, %ₒₛ cbylapp s _
  end%n.

(** [nlift]: Turn [nProp σ (;)] into [nProp σ Γ] *)
Definition nlift {σ Γ} (P : nProp σ (;)) : nProp σ Γ := nliftoi P eq_refl.
