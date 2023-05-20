(** * Substitution for [nProp] *)

From nola.examples.logic Require Export prop.
From nola Require Export util.funext hgt.
Import EqNotations.

(** ** [nlift]: Turn [nProp σ (;ᵞ)] into [nProp σ Γ] *)

(** [nliftg]: Add guarded variables at the bottom *)

Fixpoint nliftg {Δ σ Γ} (P : nProp σ Γ) : nProp σ (Γ.ᵞu;ᵞ Γ.ᵞg ++ Δ) :=
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
  | ▷ P => ▷ rew app_assoc'_g in nliftg P
  | P ⊢{i} Q => rew app_assoc'_g in nliftg P ⊢{i} rew app_assoc'_g in nliftg Q
  | ∀: V, P => ∀: V, nliftg P
  | ∃: V, P => ∃: V, nliftg P
  | (rec:ˢ' Φ) a => (rec:ˢ' nliftg ∘ Φ) a
  | (rec:ˡ' Φ) a => (rec:ˡ' nliftg ∘ Φ) a
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
  apply (FIX _ (_::_;ᵞ_)).
Qed.

(** [nliftug]: Add unguarded and guarded variables at the bottom *)
Fixpoint nliftug {Δᵘ Δᵍ σ Γ} (P : nProp σ Γ)
  : Γ.ᵞg = [] → nProp σ (Γ.ᵞu ++ Δᵘ;ᵞ Δᵍ) :=
  match P with
  | ⌜φ⌝ => λ _, ⌜φ⌝
  | P ∧ Q => λ gn, nliftug P gn ∧ nliftug Q gn
  | P ∨ Q => λ gn, nliftug P gn ∨ nliftug Q gn
  | P → Q => λ gn, nliftug P gn → nliftug Q gn
  | ∀' Φ => λ gn, ∀ a, nliftug (Φ a) gn
  | ∃' Φ => λ gn, ∃ a, nliftug (Φ a) gn
  | P ∗ Q => λ gn, nliftug P gn ∗ nliftug Q gn
  | P -∗ Q => λ gn, nliftug P gn -∗ nliftug Q gn
  | □ P => λ gn, □ nliftug P gn
  | ■ P => λ gn, ■ nliftug P gn
  | |==> P => λ gn, |==> nliftug P gn
  | |={E,E'}=> P => λ gn, |={E,E'}=> nliftug P gn
  | ▷ P => λ gn, ▷ rew app_assoc_eq_nil_g gn in nliftg P
  | P ⊢{i} Q => λ gn,
      rew app_assoc_eq_nil_g gn in nliftg P ⊢{i}
        rew app_assoc_eq_nil_g gn in nliftg P
  | ∀: V, P => λ gn, ∀: V, nliftug P gn
  | ∃: V, P => λ gn, ∃: V, nliftug P gn
  | (rec:ˢ' Φ) a => λ gn, (rec:ˢ b, nliftug (Φ b) gn) a
  | (rec:ˡ' Φ) a => λ gn, (rec:ˡ b, nliftug (Φ b) gn) a
  | %ᵍˢ s | %ᵍˡ s => seqnil s
  | %ᵘˢ s => λ _, %ᵘˢ sbylapp s _
  | !ᵘˢ P => λ _, !ᵘˢ P
  end%n.

(** [nliftug] commutes with [nlarge] *)
Lemma nliftug_nlarge {σ Γ Δᵘ Δᵍ} {P : nProp σ Γ} {gn} :
  nliftug (Δᵘ:=Δᵘ) (Δᵍ:=Δᵍ) (nlarge P) gn = nlarge (nliftug P gn).
Proof.
  move: σ Γ P gn. fix FIX 3=> σ Γ.
  case=>//=; intros; f_equal; try apply FIX; try (funext=> ?; apply FIX);
  try apply (FIX _ (_::_;ᵞ_)); by case: s gn.
Qed.

(** [nlift]: Turn [nProp σ (;ᵞ)] into [nProp σ Γ] *)
Definition nlift {σ Γ} (P : nProp σ (;ᵞ)) : nProp σ Γ := nliftug P eq_refl.

(** [nlift] commutes with [nlarge] *)
Lemma nlift_nlarge {σ Γ} {P : nProp σ (;ᵞ)} :
  nlift (Γ:=Γ) (nlarge P) = nlarge (nlift P).
Proof. apply (nliftug_nlarge (Γ:=(;ᵞ))). Qed.

(** ** [nsubst P Φ]: Substitute [Φ] for the only unguarded variable of [P] *)

(** [nPred V]: Type of an instantiation of [V : npvar] *)
Definition nPred : npvar → Type := λ '(A →nP σ), A → nProp σ (;ᵞ).

(** Apply to [nparg σ V] [nPred V] *)
Definition nparg_apply {σ V} : nparg σ V → nPred V → nProp σ (;ᵞ) :=
  λ '(@! a) Φ, Φ a.
(** Apply to [npargS V] [nPred V] *)
Definition npargS_apply {σ V} : npargS V → nPred V → nProp σ (;ᵞ) :=
  λ a Φ, nunsmall (nparg_apply a Φ).

(** [nsubstlg i P Φs]: Substitute [Φs] for all but the first [i] guarded
  variables of [P] *)
Fixpoint nsubstlg {σ Γ i} (P : nProp σ Γ)
  : plist nPred (drop i Γ.ᵞg) → nProp σ (Γ.ᵞu;ᵞ take i Γ.ᵞg) :=
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
  | ▷ P => λ Φs, ▷ rew take_add_app_g in nsubstlg P (rew drop_add_app'_d in Φs)
  | P ⊢{j} Q => λ Φs,
      rew take_add_app_g in nsubstlg P (rew drop_add_app'_d in Φs) ⊢{j}
        rew take_add_app_g in nsubstlg Q (rew drop_add_app'_d in Φs)
  | ∀: V, P => λ Φs, ∀: V, nsubstlg P Φs
  | ∃: V, P => λ Φs, ∃: V, nsubstlg P Φs
  | (rec:ˢ' Φ) a => λ Φs, (rec:ˢ b, nsubstlg (Φ b) Φs) a
  | (rec:ˡ' Φ) a => λ Φs, (rec:ˡ b, nsubstlg (Φ b) Φs) a
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
    apply (FIX _ (_;ᵞ_)) || (funext=>/= ?; apply FIX));
  case (stakedrop i s)=>//= ?; rewrite -nlift_nlarge; f_equal;
  rewrite (spapply_in nlarge); f_equal; do 3 funext=> ?; symmetry;
  [apply nlarge_nunsmall|apply nlarge_id].
Qed.

(** [nsubstlu i P Φs]: Substitute [Φs] for all but the first [i] unguarded
  variables of [P] *)
Fixpoint nsubstlu {σ Γ i} (P : nProp σ Γ)
  : plist nPred (drop i Γ.ᵞu) → Γ.ᵞg = [] → nProp σ (take i Γ.ᵞu;ᵞ ) :=
  match P with
  | ⌜φ⌝ => λ _ _, ⌜φ⌝
  | P ∧ Q => λ Φs gn, nsubstlu P Φs gn ∧ nsubstlu Q Φs gn
  | P ∨ Q => λ Φs gn, nsubstlu P Φs gn ∨ nsubstlu Q Φs gn
  | P → Q => λ Φs gn, nsubstlu P Φs gn → nsubstlu Q Φs gn
  | ∀' Φ => λ Φs gn, ∀ a, nsubstlu (Φ a) Φs gn
  | ∃' Φ => λ Φs gn, ∃ a, nsubstlu (Φ a) Φs gn
  | P ∗ Q => λ Φs gn, nsubstlu P Φs gn ∗ nsubstlu Q Φs gn
  | P -∗ Q => λ Φs gn, nsubstlu P Φs gn -∗ nsubstlu Q Φs gn
  | □ P => λ Φs gn, □ nsubstlu P Φs gn
  | ■ P => λ Φs gn, ■ nsubstlu P Φs gn
  | |==> P => λ Φs gn, |==> nsubstlu P Φs gn
  | |={E,E'}=> P => λ Φs gn, |={E,E'}=> nsubstlu P Φs gn
  | ▷ P => λ Φs gn,
      ▷ rew f_app_eq_nil_out_g gn in nsubstlg P (rew f_app_eq_nil_d gn in Φs)
  | P ⊢{j} Q => λ Φs gn,
      rew f_app_eq_nil_out_g gn in nsubstlg P (rew f_app_eq_nil_d gn in Φs) ⊢{j}
        rew f_app_eq_nil_out_g gn in nsubstlg Q (rew f_app_eq_nil_d gn in Φs)
  | ∀: V, P => λ Φs gn, ∀: V, nsubstlu (i:=S i) P Φs gn
  | ∃: V, P => λ Φs gn, ∃: V, nsubstlu (i:=S i) P Φs gn
  | (rec:ˢ' Φ) a => λ Φs gn, (rec:ˢ b, nsubstlu (i:=S i) (Φ b) Φs gn) a
  | (rec:ˡ' Φ) a => λ Φs gn, (rec:ˡ b, nsubstlu (i:=S i) (Φ b) Φs gn) a
  | %ᵍˢ s | %ᵍˡ s => λ _, seqnil s
  | %ᵘˢ s => λ Φs _, match stakedrop _ s with
      inl s => %ᵘˢ s | inr s => !ᵘˢ (spapply (λ _, nparg_apply) s Φs) end
  | !ᵘˢ P => λ _ _, !ᵘˢ P
  end%n.

(** [nsubstlu] commutes with [nlarge] *)
Lemma nsubstlu_nlarge {σ Γ i} {P : nProp σ Γ} {Φs gn} :
  nsubstlu (i:=i) (nlarge P) Φs gn = nlarge (nsubstlu P Φs gn).
Proof.
  move: σ Γ i P Φs gn. fix FIX 4=> σ Γ i.
  case=>//=; intros; f_equal; try apply FIX; try (funext=>/= ?; apply FIX);
  try apply (FIX _ (_::_;ᵞ_) (S _)); try (by case: s gn);
  by case (stakedrop i s).
Qed.

(** [nsubst P Φ]: Substitute [Φ] for the only unguarded variable of [P] *)
Definition nsubst {σ V} (P : nProp σ ([V];ᵞ )) (Φ : nPred V) : nProp σ (;ᵞ) :=
  nsubstlu (i:=0) P -[Φ] eq_refl.

(** [nsubst] commutes with [nlarge] *)
Lemma nsubst_nlarge {σ V} {P : nProp σ ([V];ᵞ )} {Φ} :
  nsubst (nlarge P) Φ = nlarge (nsubst P Φ).
Proof. apply (nsubstlu_nlarge (Γ:=([_];ᵞ)) (i:=0)). Qed.

(** ** [nheight P]: Height of [P] *)

Fixpoint nheight {σ Γ} (P : nProp σ Γ) : hgt :=
  match P with
  | ⌜_⌝ => hgt_0
  | □ P | ■ P | |==> P | |={_,_}=> P => hgt_1 (nheight P)
  | P ∧ Q | P ∨ Q | P → Q | P ∗ Q | P -∗ Q => hgt_2 (nheight P) (nheight Q)
  | ∀' Φ | ∃' Φ => hgt_all (nheight ∘ Φ)
  | ▷ _ | _ ⊢{_} _ => hgt_0
  | ∀: _, P | ∃: _, P => hgt_1 (nheight P)
  | (rec:ˢ' Φ) a | (rec:ˡ' Φ) a => hgt_1 (nheight (Φ a))
  | %ᵍˢ _ | %ᵍˡ _ | %ᵘˢ _ | !ᵘˢ _ => hgt_0
  end%n.

(** [nsubstlu] preserves [nheight] *)
Lemma nsubstlu_nheight {σ Γ i} {P : nProp σ Γ} {Φs gn} :
  nheight (nsubstlu (i:=i) P Φs gn) = nheight P.
Proof.
  move: σ Γ i P Φs gn. fix FIX 4=> ???.
  case=>//=; intros; try (f_equal; (apply FIX ||
    (funext=>/= ?; apply FIX) || apply (FIX _ (_::_;ᵞ_) (S _))));
    try (by move: gn; case s); try (by case (stakedrop _ s)).
Qed.

(** [nsubst] preserves [nheight] *)
Lemma nsubst_nheight {σ V P Φ} : nheight (nsubst (σ:=σ) (V:=V) P Φ) = nheight P.
Proof. exact (nsubstlu_nheight (Γ:=([_];ᵞ)) (i:=0)). Qed.
