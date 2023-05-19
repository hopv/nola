(** * Substitution for [nProp] *)

From nola.examples.logic Require Export prop.
From nola Require Export util.funext util.hgt.
Import EqNotations.

(** [nProp_rewi P eq]: Rewrite the inner context of [P : nProp (; Γⁱ)]
  using [eq] *)
Notation nProp_rewi P eq := (rew[λ Γⁱ, nProp _ (_; Γⁱ)] eq in P).

(** ** [nlift]: Turn [nProp σ (;)] into [nProp σ Γ] *)

(** [nlifti]: Add inner variables at the bottom *)

Definition nlifti_rew {σ Γᵒ Γⁱ Δ}
  (P : nProp σ (; (Γᵒ ++ Γⁱ) ++ Δ)) : nProp σ (; Γᵒ ++ (Γⁱ ++ Δ)) :=
  nProp_rewi P (eq_sym app_assoc_def).
Fixpoint nlifti {Δ σ Γᵒ Γⁱ} (P : nProp σ (Γᵒ; Γⁱ)) : nProp σ (Γᵒ; Γⁱ ++ Δ) :=
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
  | (rec:ˢ' Φ) a => (rec:ˢ' nlifti ∘ Φ) a
  | (rec:ˡ' Φ) a => (rec:ˡ' nlifti ∘ Φ) a
  | ∀: V, P => ∀: V, nlifti P
  | ∃: V, P => ∃: V, nlifti P
  | %ⁱˢ s => %ⁱˢ sbylapp s _
  | %ⁱˡ s => %ⁱˡ sbylapp s _
  | %ᵒˢ s => %ᵒˢ s
  | !ᵒˢ P => !ᵒˢ P
  end%n.

(** [nliftoi]: Add outer and inner variables at the bottom *)
Definition nliftoi_rew {σ Γᵒ Γⁱ Δᵒ Δⁱ} : Γⁱ = [] →
  nProp σ (; (Γᵒ ++ Γⁱ) ++ Δᵒ ++ Δⁱ) → nProp σ (; (Γᵒ ++ Δᵒ) ++ Δⁱ) :=
  match Γⁱ with
  | _ :: _ => λ eq, match eq with end
  | [] => λ _ P, nProp_rewi P (eq_trans
      (eq_sym (app_assoc_def (ys:=[]))) (app_assoc_def (ys:=Δᵒ)))
  end.
Fixpoint nliftoi {Δᵒ Δⁱ σ Γᵒ Γⁱ} (P : nProp σ (Γᵒ; Γⁱ))
  : Γⁱ = [] → nProp σ (Γᵒ ++ Δᵒ; Δⁱ) :=
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
  | (rec:ˢ' Φ) a => λ eq, (rec:ˢ b, nliftoi (Φ b) eq) a
  | (rec:ˡ' Φ) a => λ eq, (rec:ˡ b, nliftoi (Φ b) eq) a
  | ∀: V, P => λ eq, ∀: V, nliftoi P eq
  | ∃: V, P => λ eq, ∃: V, nliftoi P eq
  | %ⁱˢ s | %ⁱˡ s => seqnil s
  | %ᵒˢ s => λ _, %ᵒˢ sbylapp s _
  | !ᵒˢ P => λ _, !ᵒˢ P
  end%n.

(** [nlift]: Turn [nProp σ (;)] into [nProp σ Γ] *)
Definition nlift {σ Γ} (P : nProp σ (;)) : nProp σ Γ := nliftoi P eq_refl.

(** ** [nsubst P Φ]: Substitute [Φ] for the only outer variable of [P] *)

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
Definition nsubsti_rew {σ Γᵒ Γⁱ i}
  (P : nProp σ (; take (length Γᵒ + i) (Γᵒ ++ Γⁱ)))
  : nProp σ (; Γᵒ ++ take i Γⁱ) := nProp_rewi P take_add_app_def.
Definition nsubsti_rew' {i Γᵒ Γⁱ} (Φs : plist nPred (drop i Γⁱ))
  : plist nPred (drop (length Γᵒ + i) (Γᵒ ++ Γⁱ)) :=
  nPred_rews Φs (eq_sym drop_add_app_def).
Fixpoint nsubstli {σ Γᵒ Γⁱ i} (P : nProp σ (Γᵒ; Γⁱ))
  : plist nPred (drop i Γⁱ) → nProp σ (Γᵒ; take i Γⁱ) :=
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
  | (rec:ˢ' Φ) a => λ Φs, (rec:ˢ b, nsubstli (Φ b) Φs) a
  | (rec:ˡ' Φ) a => λ Φs, (rec:ˡ b, nsubstli (Φ b) Φs) a
  | ∀: V, P => λ Φs, ∀: V, nsubstli P Φs
  | ∃: V, P => λ Φs, ∃: V, nsubstli P Φs
  | %ⁱˢ s => λ Φs, match stakedrop _ s with
      inl s => %ⁱˢ s | inr s => nlift (spapply (λ _, npargS_apply) s Φs) end
  | %ⁱˡ s => λ Φs, match stakedrop _ s with
      inl s => %ⁱˡ s | inr s => nlift (spapply (λ _, nparg_apply) s Φs) end
  | %ᵒˢ s => λ _, %ᵒˢ s
  | !ᵒˢ P => λ _, !ᵒˢ P
  end%n.

(** [nsubstlo i P Φs]: Substitute [Φs] for all but the first [i] outer variables
  of [P] *)
Definition nsubstlo_rew {σ Γᵒ Γⁱ i}
  : Γⁱ = [] → nProp σ (; take i (Γᵒ ++ Γⁱ)) → nProp σ (; take i Γᵒ ++ []) :=
  match Γⁱ with _ :: _ => λ eq, match eq with end | [] => λ _ P, nProp_rewi P
    (eq_trans (f_equal _ app_nil_def) (eq_sym app_nil_def)) end.
Definition nsubstlo_rew' {i Γᵒ Γⁱ} (Φs : plist nPred (drop i Γᵒ))
  : Γⁱ = [] → plist nPred (drop i (Γᵒ ++ Γⁱ)) :=
  match Γⁱ with _ :: _ => λ eq, match eq with end | [] => λ _,
    nPred_rews Φs (eq_sym (f_equal _ app_nil_def)) end.
Fixpoint nsubstlo {σ Γᵒ Γⁱ i} (P : nProp σ (Γᵒ; Γⁱ))
  : plist nPred (drop i Γᵒ) → Γⁱ = [] → nProp σ (take i Γᵒ; ) :=
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
  | (rec:ˢ' Φ) a => λ Φs eq, (rec:ˢ b, nsubstlo (i:=S i) (Φ b) Φs eq) a
  | (rec:ˡ' Φ) a => λ Φs eq, (rec:ˡ b, nsubstlo (i:=S i) (Φ b) Φs eq) a
  | ∀: V, P => λ Φs eq, ∀: V, nsubstlo (i:=S i) P Φs eq
  | ∃: V, P => λ Φs eq, ∃: V, nsubstlo (i:=S i) P Φs eq
  | %ⁱˢ s | %ⁱˡ s => λ _, seqnil s
  | %ᵒˢ s => λ Φs _, match stakedrop _ s with
      inl s => %ᵒˢ s | inr s => !ᵒˢ (spapply (λ _, nparg_apply) s Φs) end
  | !ᵒˢ P => λ _ _, !ᵒˢ P
  end%n.

(** [nsubst P Φ]: Substitute [Φ] for the only outer variable of [P] *)
Definition nsubst {σ V} (P : nProp σ ([V]; )) (Φ : nPred V) : nProp σ (;) :=
  nsubstlo (i:=0) P -[Φ] eq_refl.

(** ** [nheight P]: Height of [P] *)

Fixpoint nheight {σ Γ} (P : nProp σ Γ) : hgt :=
  match P with
  | ⌜_⌝ => hgt_0
  | □ P | ■ P | |==> P | |={_,_}=> P => hgt_1 (nheight P)
  | P ∧ Q | P ∨ Q | P → Q | P ∗ Q | P -∗ Q => hgt_2 (nheight P) (nheight Q)
  | ∀' Φ | ∃' Φ => hgt_all (nheight ∘ Φ)
  | ▷ _ | _ ⊢!{_} _ => hgt_0
  | (rec:ˢ' Φ) a | (rec:ˡ' Φ) a => hgt_1 (nheight (Φ a))
  | ∀: _, P | ∃: _, P => hgt_1 (nheight P)
  | %ⁱˢ _ | %ⁱˡ _ | %ᵒˢ _ | !ᵒˢ _ => hgt_0
  end%n.

(** [nsubstlo] preserves [nheight] *)
Lemma nsubstlo_nheight {σ Γ i} {P : nProp σ Γ} {Φs eq} :
  nheight (nsubstlo (i:=i) P Φs eq) = nheight P.
Proof.
  move: σ Γ i P Φs eq. fix FIX 4=> ???.
  case=>//=; intros; try (f_equal; (apply FIX ||
    (funext=>/= ?; apply FIX) || apply (FIX _ (_ :: _; _)%nctx (S _))));
    try (by move: eq; case s); try (by case (stakedrop _ s)).
Qed.

(** [nsubst] preserves [nheight] *)
Lemma nsubst_nheight {σ V P Φ} : nheight (nsubst (σ:=σ) (V:=V) P Φ) = nheight P.
Proof. exact (nsubstlo_nheight (Γ:=(_;)%nctx) (i:=0)). Qed.
