(** * Substitution for [nProp] *)

From nola.examples.logic Require Export prop.
Import EqNotations.

(** [nProp_rewi P eq]/[nProp_rewo P eq]: Rewrite the inner/outer context of
  [P : nProp (; Γᵢ)] using [eq] *)

Notation nProp_rewi P eq := (rew[λ Γᵢ, nProp _ (; Γᵢ)] eq in P) (only parsing).
Notation nProp_rewo P eq := (rew[λ Γₒ, nProp _ (Γₒ; )] eq in P) (only parsing).

(** ** [nlift]: Turn [nProp σ (;)] into [nProp σ Γ] *)

(** [nlifti]: Add inner variables at the bottom *)

Definition nlifti_rew {σ Γₒ Γᵢ Δ}
  (P : nProp σ (; (Γₒ ++ Γᵢ) ++ Δ)) : nProp σ (; Γₒ ++ (Γᵢ ++ Δ)) :=
  nProp_rewi P (eq_sym app_assoc_def).
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
  | |={E,E'}=> P => |={E,E'}=> nlifti P
  | ▷ P => ▷ nlifti_rew (nlifti P)
  | P ⊢!{i} Q => nlifti_rew (nlifti P) ⊢!{i} nlifti_rew (nlifti Q)
  | (rec:ₛ' Φ) a => (rec:ₛ' nlifti ∘ Φ) a
  | (rec:ₗ' Φ) a => (rec:ₗ' nlifti ∘ Φ) a
  | ∀: V, P => ∀: V, nlifti P
  | ∃: V, P => ∃: V, nlifti P
  | %ᵢₛ s => %ᵢₛ sbylapp s _
  | %ᵢₗ s => %ᵢₗ sbylapp s _
  | %ₒₛ s => %ₒₛ s
  end%n.

(** [nliftoi]: Add outer and inner variables at the bottom *)
Definition nliftoi_rew {σ Γₒ Γᵢ Δₒ Δᵢ} : Γᵢ = [] →
  nProp σ (; (Γₒ ++ Γᵢ) ++ Δₒ ++ Δᵢ) → nProp σ (; (Γₒ ++ Δₒ) ++ Δᵢ) :=
  match Γᵢ with
  | _ :: _ => λ eq, match eq with end
  | [] => λ _ P, nProp_rewi P (eq_trans
      (eq_sym (app_assoc_def (ys:=[]))) (app_assoc_def (ys:=Δₒ)))
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
  | |={E,E'}=> P => λ eq, |={E,E'}=> nliftoi P eq
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
  | %ₒₛ s => λ _, %ₒₛ sbylapp s _
  end%n.

(** [nlift]: Turn [nProp σ (;)] into [nProp σ Γ] *)
Definition nlift {σ Γ} (P : nProp σ (;)) : nProp σ Γ := nliftoi P eq_refl.

(** ** [nsubsti/nsubsto P Φs]: Substitute [Φs] for all the inner/outer variables
  of [P] *)

(** [nPred V]: Type of an instantiation of [V : npvar] *)
Definition nPred : npvar → Type := λ '(A →nP σ), A → nProp σ (;).

(** Apply to [nparg σ V] [nPred V] *)
Definition nparg_apply {σ V} : nparg σ V → nPred V → nProp σ (;) :=
  λ '(@! a) Φ, Φ a.
(** Apply to [npargS V] [nPred V] *)
Definition npargS_apply {σ V} : npargS V → nPred V → nProp σ (;) :=
  λ a Φ, nunsmall (nparg_apply a Φ).

(** [nPred_rews]: Rewrite the context of [plist nPred] with [eq] *)
Notation nPred_rews Φs eq := (rew[plist nPred] eq in Φs) (only parsing).

(** [nsubstli i P Φs]: Substitute [Φs] for all but the first [i] inner variables
  of [P] *)
Definition nsubsti_rew {σ Γₒ Γᵢ i}
  (P : nProp σ (; take (length Γₒ + i) (Γₒ ++ Γᵢ)))
  : nProp σ (; Γₒ ++ take i Γᵢ) := nProp_rewi P take_add_app_def.
Definition nsubsti_rew' {i Γₒ Γᵢ} (Φs : plist nPred (drop i Γᵢ))
  : plist nPred (drop (length Γₒ + i) (Γₒ ++ Γᵢ)) :=
  nPred_rews Φs (eq_sym drop_add_app_def).
Fixpoint nsubstli {σ Γₒ Γᵢ i} (P : nProp σ (Γₒ; Γᵢ))
  : plist nPred (drop i Γᵢ) → nProp σ (Γₒ; take i Γᵢ) :=
  match P with
  | ⌜φ⌝ => λ _, ⌜φ⌝
  | P ∧ Q => λ Φs, nsubstli P Φs ∧ nsubstli Q Φs
  | P ∨ Q => λ Φs, nsubstli P Φs ∨ nsubstli Q Φs
  | P → Q => λ Φs, nsubstli P Φs → nsubstli Q Φs
  | ∀' Φ => λ Φs, ∀ a, nsubstli (Φ a) Φs
  | ∃' Φ => λ Φs, ∃ a, nsubstli (Φ a) Φs
  | P ∗ Q => λ Φs, nsubstli P Φs ∗ nsubstli Q Φs
  | P -∗ Q => λ Φs, nsubstli P Φs -∗ nsubstli Q Φs
  | □ P => λ Φs, □ nsubstli P Φs
  | ■ P => λ Φs, ■ nsubstli P Φs
  | |==> P => λ Φs, |==> nsubstli P Φs
  | |={E,E'}=> P => λ Φs, |={E,E'}=> nsubstli P Φs
  | ▷ P => λ Φs, ▷ nsubsti_rew (nsubstli P (nsubsti_rew' Φs))
  | P ⊢!{j} Q => λ Φs,
      nsubsti_rew (nsubstli P (nsubsti_rew' Φs)) ⊢!{j}
        nsubsti_rew (nsubstli Q (nsubsti_rew' Φs))
  | (rec:ₛ' Φ) a => λ Φs, (rec:ₛ b, nsubstli (Φ b) Φs) a
  | (rec:ₗ' Φ) a => λ Φs, (rec:ₗ b, nsubstli (Φ b) Φs) a
  | ∀: V, P => λ Φs, ∀: V, nsubstli P Φs
  | ∃: V, P => λ Φs, ∃: V, nsubstli P Φs
  | %ᵢₛ s => λ Φs, match stakedrop _ s with
      inl s => %ᵢₛ s | inr s => nlift (spapply (λ _, npargS_apply) s Φs) end
  | %ᵢₗ s => λ Φs, match stakedrop _ s with
      inl s => %ᵢₗ s | inr s => nlift (spapply (λ _, nparg_apply) s Φs) end
  | %ₒₛ s => λ _, %ₒₛ s
  end%n.

(** [nsubsti P Φ]: Substitute [Φ] for the last inner variable of [P] *)
Definition nsubsti {σ Γᵢ V} (P : nProp σ (; Γᵢ ++ [V])) (Φ : nPred V)
  : nProp σ (; Γᵢ) :=
  nProp_rewi
    (nsubstli P (nPred_rews (-[Φ] : plist _ [_]) (eq_sym drop_app_def)))
    take_app_def.

(** [nsubstsi P Φs]: Substitute [Φs] for all the inner variables of [P],
  defined as iterative applications of [nsubsti] *)
Fixpoint nsubstsi' {σ Γᵢ}
  : nProp σ (; rev Γᵢ) → plist nPred (rev Γᵢ) → nProp σ (;) :=
  match Γᵢ with
  | [] => λ P _, P
  | _ :: _ => λ P Φs, nsubstsi' (nsubsti P (phd (punappr Φs))) (punappl Φs)
  end.
Definition nsubstsi {σ Γᵢ}
  : nProp σ (; Γᵢ) → plist nPred Γᵢ → nProp σ (;) :=
  rew[λ Γᵢ, nProp σ (; Γᵢ) → plist nPred Γᵢ → _] rev_invol_def in nsubstsi'.
Arguments nsubstsi {_ _} _ _ /.

(** [nsubstlo i P Φs]: Substitute [Φs] for all but the first [i] outer variables
  of [P] *)
  Definition nsubstlo_rew {σ Γₒ Γᵢ i}
  : Γᵢ = [] → nProp σ (; take i (Γₒ ++ Γᵢ)) → nProp σ (; take i Γₒ ++ []) :=
  match Γᵢ with _ :: _ => λ eq, match eq with end | [] => λ _ P, nProp_rewi P
    (eq_trans (f_equal _ app_nil_def) (eq_sym app_nil_def)) end.
Definition nsubstlo_rew' {i Γₒ Γᵢ} (Φs : plist nPred (drop i Γₒ))
  : Γᵢ = [] → plist nPred (drop i (Γₒ ++ Γᵢ)) :=
  match Γᵢ with _ :: _ => λ eq, match eq with end | [] => λ _,
    nPred_rews Φs (eq_sym (f_equal _ app_nil_def)) end.
Fixpoint nsubstlo {σ Γₒ Γᵢ i} (P : nProp σ (Γₒ; Γᵢ))
  : plist nPred (drop i Γₒ) → Γᵢ = [] → nProp σ (take i Γₒ; ) :=
  match P with
  | ⌜φ⌝ => λ _ _, ⌜φ⌝
  | P ∧ Q => λ Φs eq, nsubstlo P Φs eq ∧ nsubstlo Q Φs eq
  | P ∨ Q => λ Φs eq, nsubstlo P Φs eq ∨ nsubstlo Q Φs eq
  | P → Q => λ Φs eq, nsubstlo P Φs eq → nsubstlo Q Φs eq
  | ∀' Φ => λ Φs eq, ∀ a, nsubstlo (Φ a) Φs eq
  | ∃' Φ => λ Φs eq, ∃ a, nsubstlo (Φ a) Φs eq
  | P ∗ Q => λ Φs eq, nsubstlo P Φs eq ∗ nsubstlo Q Φs eq
  | P -∗ Q => λ Φs eq, nsubstlo P Φs eq -∗ nsubstlo Q Φs eq
  | □ P => λ Φs eq, □ nsubstlo P Φs eq
  | ■ P => λ Φs eq, ■ nsubstlo P Φs eq
  | |==> P => λ Φs eq, |==> nsubstlo P Φs eq
  | |={E,E'}=> P => λ Φs eq, |={E,E'}=> nsubstlo P Φs eq
  | ▷ P => λ Φs eq, ▷ nsubstlo_rew eq (nsubstli P (nsubstlo_rew' Φs eq))
  | P ⊢!{j} Q => λ Φs eq,
      nsubstlo_rew eq (nsubstli P (nsubstlo_rew' Φs eq)) ⊢!{j}
        nsubstlo_rew eq (nsubstli Q (nsubstlo_rew' Φs eq))
  | (rec:ₛ' Φ) a => λ Φs eq, (rec:ₛ b, nsubstlo (i:=S i) (Φ b) Φs eq) a
  | (rec:ₗ' Φ) a => λ Φs eq, (rec:ₗ b, nsubstlo (i:=S i) (Φ b) Φs eq) a
  | ∀: V, P => λ Φs eq, ∀: V, nsubstlo (i:=S i) P Φs eq
  | ∃: V, P => λ Φs eq, ∃: V, nsubstlo (i:=S i) P Φs eq
  | %ᵢₛ s => match s with
      #0 _ => λ _ eq, match eq with end | +/ _ => λ _ eq, match eq with end end
  | %ᵢₗ s => match s with
      #0 _ => λ _ eq, match eq with end | +/ _ => λ _ eq, match eq with end end
  | %ₒₛ s => λ Φs _, match stakedrop _ s with
      inl s => %ₒₛ s | inr s => nlift (spapply (λ _, npargS_apply) s Φs) end
  end%n.

(** [nsubsto P Φ]: Substitute [Φ] for the last outer variable of [P] *)
Definition nsubsto {σ Γₒ V} (P : nProp σ (Γₒ ++ [V]; )) (Φ : nPred V)
  : nProp σ (Γₒ; ) :=
  nProp_rewo
    (nsubstlo P (nPred_rews (-[Φ] : plist _ [_]) (eq_sym drop_app_def)) eq_refl)
    take_app_def.

(** [nsubstso P Φs]: Substitute [Φs] for all the outer variables of [P],
  defined as iterative applications of [nsubsto] *)
Fixpoint nsubstso' {σ Γₒ}
  : nProp σ (rev Γₒ; ) → plist nPred (rev Γₒ) → nProp σ (;) :=
  match Γₒ with
  | [] => λ P _, P
  | _ :: _ => λ P Φs,
      nsubstso' (nsubsto P (phd (punappr Φs))) (punappl Φs)
  end.
Definition nsubstso {σ Γₒ}
  : nProp σ (Γₒ; ) → plist nPred Γₒ → nProp σ (;) :=
  rew[λ Γₒ, nProp σ (Γₒ; ) → plist nPred Γₒ → _] rev_invol_def in nsubstso'.
Arguments nsubstso {_ _} _ _ /.
