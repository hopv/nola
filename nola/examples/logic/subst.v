(** * Substitution for [nProp] *)

From nola.examples.logic Require Export prop.
From nola Require Export util.funext hgt.
Import EqNotations.

(** [nProp_rewg P eq]: Rewrite the guarded context of [P : nProp (; Γᵍ)]
  using [eq] *)
Notation nProp_rewg P eq := (rew[λ Γᵍ, nProp _ (_; Γᵍ)] eq in P).

(** ** [nlift]: Turn [nProp σ (;)] into [nProp σ Γ] *)

(** [nliftg]: Add guarded variables at the bottom *)

Definition nliftg_rew {σ Γᵘ Γᵍ Δ}
  (P : nProp σ (; (Γᵘ ++ Γᵍ) ++ Δ)) : nProp σ (; Γᵘ ++ (Γᵍ ++ Δ)) :=
  nProp_rewg P (eq_sym app_assoc_def).
Fixpoint nliftg {Δ σ Γᵘ Γᵍ} (P : nProp σ (Γᵘ; Γᵍ)) : nProp σ (Γᵘ; Γᵍ ++ Δ) :=
  match P with
  | ⌜φ⌝ => ⌜φ⌝
  | P ∧ Q => nliftg P ∧ nliftg Q
  | P ∨ Q => nliftg P ∨ nliftg Q
  | P → Q => nliftg P → nliftg Q
  | ∀' Φ => ∀' nliftg ∘ Φ
  | ∃' Φ => ∃' nliftg ∘ Φ
  | P ∗ Q => nliftg P ∗ nliftg Q
  | P -∗ Q => nliftg P -∗ nliftg Q
  | □ P => □ nliftg P
  | ■ P => ■ nliftg P
  | |==> P => |==> nliftg P
  | |={E,E'}=> P => |={E,E'}=> nliftg P
  | ▷ P => ▷ nliftg_rew (nliftg P)
  | P ⊢!{i} Q => nliftg_rew (nliftg P) ⊢!{i} nliftg_rew (nliftg Q)
  | (rec:ˢ' Φ) a => (rec:ˢ' nliftg ∘ Φ) a
  | (rec:ˡ' Φ) a => (rec:ˡ' nliftg ∘ Φ) a
  | ∀: V, P => ∀: V, nliftg P
  | ∃: V, P => ∃: V, nliftg P
  | %ᵍˢ s => %ᵍˢ sbylapp s _
  | %ᵍˡ s => %ᵍˡ sbylapp s _
  | %ᵘˢ s => %ᵘˢ s
  | !ᵘˢ P => !ᵘˢ P
  end%n.

(** [nliftg] commutes with [nlarge] *)
Lemma nliftg_nlarge {σ Γ Δ} {P : nProp σ Γ} :
  nliftg (Δ:=Δ) (nlarge P) = nlarge (nliftg P).
Proof.
  move: σ Γ P. fix FIX 3=> σ Γ.
  case=>//= *; f_equal; try apply FIX; try (funext=> ?; apply FIX);
  apply (FIX _ (_ :: _; _)%nctx).
Qed.

(** [nliftug]: Add unguarded and guarded variables at the bottom *)
Definition nliftug_rew {σ Γᵘ Γᵍ Δᵘ Δᵍ} : Γᵍ = [] →
  nProp σ (; (Γᵘ ++ Γᵍ) ++ Δᵘ ++ Δᵍ) → nProp σ (; (Γᵘ ++ Δᵘ) ++ Δᵍ) :=
  match Γᵍ with
  | _ :: _ => λ eq, match eq with end
  | [] => λ _ P, nProp_rewg P (eq_trans
      (eq_sym (app_assoc_def (ys:=[]))) (app_assoc_def (ys:=Δᵘ)))
  end.
Fixpoint nliftug {Δᵘ Δᵍ σ Γᵘ Γᵍ} (P : nProp σ (Γᵘ; Γᵍ))
  : Γᵍ = [] → nProp σ (Γᵘ ++ Δᵘ; Δᵍ) :=
  match P with
  | ⌜φ⌝ => λ _, ⌜φ⌝
  | P ∧ Q => λ eq, nliftug P eq ∧ nliftug Q eq
  | P ∨ Q => λ eq, nliftug P eq ∨ nliftug Q eq
  | P → Q => λ eq, nliftug P eq → nliftug Q eq
  | ∀' Φ => λ eq, ∀ a, nliftug (Φ a) eq
  | ∃' Φ => λ eq, ∃ a, nliftug (Φ a) eq
  | P ∗ Q => λ eq, nliftug P eq ∗ nliftug Q eq
  | P -∗ Q => λ eq, nliftug P eq -∗ nliftug Q eq
  | □ P => λ eq, □ nliftug P eq
  | ■ P => λ eq, ■ nliftug P eq
  | |==> P => λ eq, |==> nliftug P eq
  | |={E,E'}=> P => λ eq, |={E,E'}=> nliftug P eq
  | ▷ P => λ eq, ▷ nliftug_rew eq (nliftg P)
  | P ⊢!{i} Q => λ eq,
      nliftug_rew eq (nliftg P) ⊢!{i} nliftug_rew eq (nliftg Q)
  | (rec:ˢ' Φ) a => λ eq, (rec:ˢ b, nliftug (Φ b) eq) a
  | (rec:ˡ' Φ) a => λ eq, (rec:ˡ b, nliftug (Φ b) eq) a
  | ∀: V, P => λ eq, ∀: V, nliftug P eq
  | ∃: V, P => λ eq, ∃: V, nliftug P eq
  | %ᵍˢ s | %ᵍˡ s => seqnil s
  | %ᵘˢ s => λ _, %ᵘˢ sbylapp s _
  | !ᵘˢ P => λ _, !ᵘˢ P
  end%n.

(** [nliftug] commutes with [nlarge] *)
Lemma nliftug_nlarge {σ Γ Δᵘ Δᵍ} {P : nProp σ Γ} {eq} :
  nliftug (Δᵘ:=Δᵘ) (Δᵍ:=Δᵍ) (nlarge P) eq = nlarge (nliftug P eq).
Proof.
  move: σ Γ P eq. fix FIX 3=> σ Γ.
  case=>//=; intros; f_equal; try apply FIX; try (funext=> ?; apply FIX);
  try apply (FIX _ (_ :: _; _)%nctx); by case: s eq.
Qed.

(** [nlift]: Turn [nProp σ (;)] into [nProp σ Γ] *)
Definition nlift {σ Γ} (P : nProp σ (;)) : nProp σ Γ := nliftug P eq_refl.

(** [nlift] commutes with [nlarge] *)
Lemma nlift_nlarge {σ Γ} {P : nProp σ (;)} :
  nlift (Γ:=Γ) (nlarge P) = nlarge (nlift P).
Proof. apply (nliftug_nlarge (Γ:=(;))). Qed.

(** ** [nsubst P Φ]: Substitute [Φ] for the only unguarded variable of [P] *)

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

(** [nsubstlg i P Φs]: Substitute [Φs] for all but the first [i] guarded
  variables of [P] *)
Definition nsubstlg_rew {σ Γᵘ Γᵍ i}
  (P : nProp σ (; take (length Γᵘ + i) (Γᵘ ++ Γᵍ)))
  : nProp σ (; Γᵘ ++ take i Γᵍ) := nProp_rewg P take_add_app_def.
Definition nsubstlg_rew' {i Γᵘ Γᵍ} (Φs : plist nPred (drop i Γᵍ))
  : plist nPred (drop (length Γᵘ + i) (Γᵘ ++ Γᵍ)) :=
  nPred_rews Φs (eq_sym drop_add_app_def).
Fixpoint nsubstlg {σ Γᵘ Γᵍ i} (P : nProp σ (Γᵘ; Γᵍ))
  : plist nPred (drop i Γᵍ) → nProp σ (Γᵘ; take i Γᵍ) :=
  match P with
  | ⌜φ⌝ => λ _, ⌜φ⌝
  | P ∧ Q => λ Φs, nsubstlg P Φs ∧ nsubstlg Q Φs
  | P ∨ Q => λ Φs, nsubstlg P Φs ∨ nsubstlg Q Φs
  | P → Q => λ Φs, nsubstlg P Φs → nsubstlg Q Φs
  | ∀' Φ => λ Φs, ∀ a, nsubstlg (Φ a) Φs
  | ∃' Φ => λ Φs, ∃ a, nsubstlg (Φ a) Φs
  | P ∗ Q => λ Φs, nsubstlg P Φs ∗ nsubstlg Q Φs
  | P -∗ Q => λ Φs, nsubstlg P Φs -∗ nsubstlg Q Φs
  | □ P => λ Φs, □ nsubstlg P Φs
  | ■ P => λ Φs, ■ nsubstlg P Φs
  | |==> P => λ Φs, |==> nsubstlg P Φs
  | |={E,E'}=> P => λ Φs, |={E,E'}=> nsubstlg P Φs
  | ▷ P => λ Φs, ▷ nsubstlg_rew (nsubstlg P (nsubstlg_rew' Φs))
  | P ⊢!{j} Q => λ Φs,
      nsubstlg_rew (nsubstlg P (nsubstlg_rew' Φs)) ⊢!{j}
        nsubstlg_rew (nsubstlg Q (nsubstlg_rew' Φs))
  | (rec:ˢ' Φ) a => λ Φs, (rec:ˢ b, nsubstlg (Φ b) Φs) a
  | (rec:ˡ' Φ) a => λ Φs, (rec:ˡ b, nsubstlg (Φ b) Φs) a
  | ∀: V, P => λ Φs, ∀: V, nsubstlg P Φs
  | ∃: V, P => λ Φs, ∃: V, nsubstlg P Φs
  | %ᵍˢ s => λ Φs, match stakedrop _ s with
      inl s => %ᵍˢ s | inr s => nlift (spapply (λ _, npargS_apply) s Φs) end
  | %ᵍˡ s => λ Φs, match stakedrop _ s with
      inl s => %ᵍˡ s | inr s => nlift (spapply (λ _, nparg_apply) s Φs) end
  | %ᵘˢ s => λ _, %ᵘˢ s
  | !ᵘˢ P => λ _, !ᵘˢ P
  end%n.

(** [nsubstlg] commutes with [nlarge] *)
Lemma nsubstlg_nlarge {σ Γ i} {P : nProp σ Γ} {Φs} :
  nsubstlg (i:=i) (nlarge P) Φs = nlarge (nsubstlg P Φs).
Proof.
  move: σ Γ i P Φs. fix FIX 4=> σ Γ i.
  case=>//=; intros; try (f_equal;
    apply (FIX _ (_;_)%nctx) || (funext=>/= ?; apply FIX));
  case (stakedrop i s)=>//= ?; rewrite -nlift_nlarge; f_equal;
  rewrite (spapply_in nlarge); f_equal; do 3 funext=> ?; symmetry;
  [apply nlarge_nunsmall|apply nlarge_id].
Qed.

(** [nsubstlu i P Φs]: Substitute [Φs] for all but the first [i] unguarded
  variables of [P] *)
Definition nsubstlu_rew {σ Γᵘ Γᵍ i}
  : Γᵍ = [] → nProp σ (; take i (Γᵘ ++ Γᵍ)) → nProp σ (; take i Γᵘ ++ []) :=
  match Γᵍ with _ :: _ => λ eq, match eq with end | [] => λ _ P, nProp_rewg P
    (eq_trans (f_equal _ app_nil_def) (eq_sym app_nil_def)) end.
Definition nsubstlu_rew' {i Γᵘ Γᵍ} (Φs : plist nPred (drop i Γᵘ))
  : Γᵍ = [] → plist nPred (drop i (Γᵘ ++ Γᵍ)) :=
  match Γᵍ with _ :: _ => λ eq, match eq with end | [] => λ _,
    nPred_rews Φs (eq_sym (f_equal _ app_nil_def)) end.
Fixpoint nsubstlu {σ Γᵘ Γᵍ i} (P : nProp σ (Γᵘ; Γᵍ))
  : plist nPred (drop i Γᵘ) → Γᵍ = [] → nProp σ (take i Γᵘ; ) :=
  match P with
  | ⌜φ⌝ => λ _ _, ⌜φ⌝
  | P ∧ Q => λ Φs eq, nsubstlu P Φs eq ∧ nsubstlu Q Φs eq
  | P ∨ Q => λ Φs eq, nsubstlu P Φs eq ∨ nsubstlu Q Φs eq
  | P → Q => λ Φs eq, nsubstlu P Φs eq → nsubstlu Q Φs eq
  | ∀' Φ => λ Φs eq, ∀ a, nsubstlu (Φ a) Φs eq
  | ∃' Φ => λ Φs eq, ∃ a, nsubstlu (Φ a) Φs eq
  | P ∗ Q => λ Φs eq, nsubstlu P Φs eq ∗ nsubstlu Q Φs eq
  | P -∗ Q => λ Φs eq, nsubstlu P Φs eq -∗ nsubstlu Q Φs eq
  | □ P => λ Φs eq, □ nsubstlu P Φs eq
  | ■ P => λ Φs eq, ■ nsubstlu P Φs eq
  | |==> P => λ Φs eq, |==> nsubstlu P Φs eq
  | |={E,E'}=> P => λ Φs eq, |={E,E'}=> nsubstlu P Φs eq
  | ▷ P => λ Φs eq, ▷ nsubstlu_rew eq (nsubstlg P (nsubstlu_rew' Φs eq))
  | P ⊢!{j} Q => λ Φs eq,
      nsubstlu_rew eq (nsubstlg P (nsubstlu_rew' Φs eq)) ⊢!{j}
        nsubstlu_rew eq (nsubstlg Q (nsubstlu_rew' Φs eq))
  | (rec:ˢ' Φ) a => λ Φs eq, (rec:ˢ b, nsubstlu (i:=S i) (Φ b) Φs eq) a
  | (rec:ˡ' Φ) a => λ Φs eq, (rec:ˡ b, nsubstlu (i:=S i) (Φ b) Φs eq) a
  | ∀: V, P => λ Φs eq, ∀: V, nsubstlu (i:=S i) P Φs eq
  | ∃: V, P => λ Φs eq, ∃: V, nsubstlu (i:=S i) P Φs eq
  | %ᵍˢ s | %ᵍˡ s => λ _, seqnil s
  | %ᵘˢ s => λ Φs _, match stakedrop _ s with
      inl s => %ᵘˢ s | inr s => !ᵘˢ (spapply (λ _, nparg_apply) s Φs) end
  | !ᵘˢ P => λ _ _, !ᵘˢ P
  end%n.

(** [nsubstlu] commutes with [nlarge] *)
Lemma nsubstlu_nlarge {σ Γ i} {P : nProp σ Γ} {Φs eq} :
  nsubstlu (i:=i) (nlarge P) Φs eq = nlarge (nsubstlu P Φs eq).
Proof.
  move: σ Γ i P Φs eq. fix FIX 4=> σ Γ i.
  case=>//=; intros; f_equal; try apply FIX; try (funext=>/= ?; apply FIX);
  try apply (FIX _ (_ :: _; _)%nctx (S _)); try (by case: s eq);
  by case (stakedrop i s).
Qed.

(** [nsubst P Φ]: Substitute [Φ] for the only unguarded variable of [P] *)
Definition nsubst {σ V} (P : nProp σ ([V]; )) (Φ : nPred V) : nProp σ (;) :=
  nsubstlu (i:=0) P -[Φ] eq_refl.

(** [nsubst] commutes with [nlarge] *)
Lemma nsubst_nlarge {σ V} {P : nProp σ ([V]; )} {Φ} :
  nsubst (nlarge P) Φ = nlarge (nsubst P Φ).
Proof. apply (nsubstlu_nlarge (Γ:=([_];)) (i:=0)). Qed.

(** [nsubst] commutes with [nsubstlu] *)

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
  | %ᵍˢ _ | %ᵍˡ _ | %ᵘˢ _ | !ᵘˢ _ => hgt_0
  end%n.

(** [nsubstlu] preserves [nheight] *)
Lemma nsubstlu_nheight {σ Γ i} {P : nProp σ Γ} {Φs eq} :
  nheight (nsubstlu (i:=i) P Φs eq) = nheight P.
Proof.
  move: σ Γ i P Φs eq. fix FIX 4=> ???.
  case=>//=; intros; try (f_equal; (apply FIX ||
    (funext=>/= ?; apply FIX) || apply (FIX _ (_::_;_)%nctx (S _))));
    try (by move: eq; case s); try (by case (stakedrop _ s)).
Qed.

(** [nsubst] preserves [nheight] *)
Lemma nsubst_nheight {σ V P Φ} : nheight (nsubst (σ:=σ) (V:=V) P Φ) = nheight P.
Proof. exact (nsubstlu_nheight (Γ:=([_];)) (i:=0)). Qed.
