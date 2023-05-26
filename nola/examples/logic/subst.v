(** * Substitution for [nProp] *)

From nola.examples.logic Require Export prop.
From nola Require Export util.funext hgt.
Import EqNotations.

(** ** [nlift]: Turn [nProp κ (;ᵞ)] into [nProp κ Γ] *)

(** [nliftg]: Add guarded variables at the bottom *)

Fixpoint nliftg {Δ κ Γ} (P : nProp κ Γ) : nProp κ (Γ.ᵞu;ᵞ Γ.ᵞg ++ Δ) :=
  match P with
  | n_0 c => n_0 c | n_1 c P => n_1 c (nliftg P)
  | n_2 c P Q => n_2 c (nliftg P) (nliftg Q)
  | n_g1 c P => n_g1 c (rew app_assoc'_g in nliftg P)
  | ∀' Φ => ∀' (nliftg ∘ Φ) | ∃' Φ => ∃' (nliftg ∘ Φ)
  | ∀: V, P => ∀: V, nliftg P | ∃: V, P => ∃: V, nliftg P
  | rec:ˢ' Φ a => (rec:ˢ' (nliftg ∘ Φ)) a
  | rec:ˡ' Φ a => (rec:ˡ' (nliftg ∘ Φ)) a
  | %ᵍˢ s => %ᵍˢ sbylapp s _ | %ᵍˡ s => %ᵍˡ sbylapp s _ | %ᵘˢ s => %ᵘˢ s
  | !ᵘˢ P => !ᵘˢ P
  end%n.

(** [nliftg] commutes with [nlarge] *)
Lemma nliftg_nlarge {κ Γ Δ} {P : nProp κ Γ} :
  nliftg (Δ:=Δ) (nlarge P) = nlarge (nliftg P).
Proof.
  move: κ Γ P. fix FIX 3=> κ Γ.
  case=>//= *; f_equal; try apply FIX; try (funext=> ?; apply FIX);
  apply (FIX _ (_::_;ᵞ_)).
Qed.

(** [nliftug]: Add unguarded and guarded variables at the bottom *)
Fixpoint nliftug {Δᵘ Δᵍ κ Γ} (P : nProp κ Γ)
  : Γ.ᵞg = [] → nProp κ (Γ.ᵞu ++ Δᵘ;ᵞ Δᵍ) :=
  match P with
  | n_0 c => λ _, n_0 c | n_1 c P => λ gn, n_1 c (nliftug P gn)
  | n_2 c P Q => λ gn, n_2 c (nliftug P gn) (nliftug Q gn)
  | n_g1 c P => λ gn, n_g1 c (rew app_assoc_eq_nil_g gn in nliftg P)
  | ∀' Φ => λ gn, ∀ a, nliftug (Φ a) gn | ∃' Φ => λ gn, ∃ a, nliftug (Φ a) gn
  | ∀: V, P => λ gn, ∀: V, nliftug P gn | ∃: V, P => λ gn, ∃: V, nliftug P gn
  | rec:ˢ' Φ a => λ gn, (rec:ˢ b, nliftug (Φ b) gn) a
  | rec:ˡ' Φ a => λ gn, (rec:ˡ b, nliftug (Φ b) gn) a
  | %ᵍˢ s | %ᵍˡ s => seqnil s | %ᵘˢ s => λ _, %ᵘˢ sbylapp s _
  | !ᵘˢ P => λ _, !ᵘˢ P
  end%n.

(** [nliftug] commutes with [nlarge] *)
Lemma nliftug_nlarge {κ Γ Δᵘ Δᵍ} {P : nProp κ Γ} {gn} :
  nliftug (Δᵘ:=Δᵘ) (Δᵍ:=Δᵍ) (nlarge P) gn = nlarge (nliftug P gn).
Proof.
  move: κ Γ P gn. fix FIX 3=> κ Γ.
  case=>//=; intros; f_equal; try apply FIX; try (funext=> ?; apply FIX);
  try apply (FIX _ (_::_;ᵞ_)); by case: s gn.
Qed.

(** [nlift]: Turn [nProp κ (;ᵞ)] into [nProp κ Γ] *)
Definition nlift {κ Γ} (P : nProp κ (;ᵞ)) : nProp κ Γ := nliftug P eq_refl.

(** [nlift] commutes with [nlarge] *)
Lemma nlift_nlarge {κ Γ} {P : nProp κ (;ᵞ)} :
  nlift (Γ:=Γ) (nlarge P) = nlarge (nlift P).
Proof. apply (nliftug_nlarge (Γ:=(;ᵞ))). Qed.

(** ** [nsubst P Φ]: Substitute [Φ] for the only unguarded variable of [P] *)

(** [nPred V]: Type of an instantiation of [V : npvar] *)
Definition nPred : npvar → Type := λ '(A →nP κ), A → nProp κ (;ᵞ).
Bind Scope nProp_scope with nPred.

(** Apply to [nparg κ V] [nPred V] *)
Definition nparg_apply {κ V} : nparg κ V → nPred V → nProp κ (;ᵞ) :=
  λ '(@! a) Φ, Φ a.
(** Apply to [npargS V] [nPred V] *)
Definition npargS_apply {κ V} : npargS V → nPred V → nProp κ (;ᵞ) :=
  λ a Φ, nunsmall (nparg_apply a Φ).

(** [nsubstlg i P Φs]: Substitute [Φs] for all but the first [i] guarded
  variables of [P] *)
Fixpoint nsubstlg {κ Γ i} (P : nProp κ Γ)
  : plist nPred (drop i Γ.ᵞg) → nProp κ (Γ.ᵞu;ᵞ take i Γ.ᵞg) :=
  match P with
  | n_0 c => λ _, n_0 c | n_1 c P => λ Φs, n_1 c (nsubstlg P Φs)
  | n_2 c P Q => λ Φs, n_2 c (nsubstlg P Φs) (nsubstlg Q Φs)
  | n_g1 c P => λ Φs, n_g1 c
      (rew take_add_app_g in nsubstlg P (rew drop_add_app'_d in Φs))
  | ∀' Φ => λ Φs, ∀ a, nsubstlg (Φ a) Φs | ∃' Φ => λ Φs, ∃ a, nsubstlg (Φ a) Φs
  | ∀: V, P => λ Φs, ∀: V, nsubstlg P Φs | ∃: V, P => λ Φs, ∃: V, nsubstlg P Φs
  | rec:ˢ' Φ a => λ Φs, (rec:ˢ b, nsubstlg (Φ b) Φs) a
  | rec:ˡ' Φ a => λ Φs, (rec:ˡ b, nsubstlg (Φ b) Φs) a
  | %ᵍˢ s => λ Φs, match stakedrop _ s with
      inl s => %ᵍˢ s | inr s => nlift (spapply (λ _, npargS_apply) s Φs) end
  | %ᵍˡ s => λ Φs, match stakedrop _ s with
      inl s => %ᵍˡ s | inr s => nlift (spapply (λ _, nparg_apply) s Φs) end
  | %ᵘˢ s => λ _, %ᵘˢ s | !ᵘˢ P => λ _, !ᵘˢ P
  end%n.

(** [nsubstlg] commutes with [nlarge] *)
Lemma nsubstlg_nlarge {κ Γ i} {P : nProp κ Γ} {Φs} :
  nsubstlg (i:=i) (nlarge P) Φs = nlarge (nsubstlg P Φs).
Proof.
  move: κ Γ i P Φs. fix FIX 4=> κ Γ i.
  case=>//=; intros; try (f_equal;
    apply (FIX _ (_;ᵞ_)) || (funext=>/= ?; apply FIX));
  case (stakedrop i s)=>//= ?; rewrite -nlift_nlarge; f_equal;
  rewrite (spapply_in nlarge); f_equal; do 3 funext=> ?; symmetry;
  [apply nlarge_nunsmall|apply nlarge_id].
Qed.

(** [nsubstlu i P Φs]: Substitute [Φs] for all but the first [i] unguarded
  variables of [P] *)
Fixpoint nsubstlu {κ Γ i} (P : nProp κ Γ)
  : plist nPred (drop i Γ.ᵞu) → Γ.ᵞg = [] → nProp κ (take i Γ.ᵞu;ᵞ ) :=
  match P with
  | n_0 c => λ _ _, n_0 c | n_1 c P => λ Φs gn, n_1 c (nsubstlu P Φs gn)
  | n_2 c P Q => λ Φs gn, n_2 c (nsubstlu P Φs gn) (nsubstlu Q Φs gn)
  | n_g1 c P => λ Φs gn, n_g1 c
      (rew f_app_eq_nil_out_g gn in nsubstlg P (rew f_app_eq_nil_d gn in Φs))
  | ∀' Φ => λ Φs gn, ∀ a, nsubstlu (Φ a) Φs gn
  | ∃' Φ => λ Φs gn, ∃ a, nsubstlu (Φ a) Φs gn
  | ∀: V, P => λ Φs gn, ∀: V, nsubstlu (i:=S i) P Φs gn
  | ∃: V, P => λ Φs gn, ∃: V, nsubstlu (i:=S i) P Φs gn
  | rec:ˢ' Φ a => λ Φs gn, (rec:ˢ b, nsubstlu (i:=S i) (Φ b) Φs gn) a
  | rec:ˡ' Φ a => λ Φs gn, (rec:ˡ b, nsubstlu (i:=S i) (Φ b) Φs gn) a
  | %ᵍˢ s | %ᵍˡ s => λ _, seqnil s
  | %ᵘˢ s => λ Φs _, match stakedrop _ s with
      inl s => %ᵘˢ s | inr s => !ᵘˢ (spapply (λ _, nparg_apply) s Φs) end
  | !ᵘˢ P => λ _ _, !ᵘˢ P
  end%n.

(** [nsubstlu] commutes with [nlarge] *)
Lemma nsubstlu_nlarge {κ Γ i} {P : nProp κ Γ} {Φs gn} :
  nsubstlu (i:=i) (nlarge P) Φs gn = nlarge (nsubstlu P Φs gn).
Proof.
  move: κ Γ i P Φs gn. fix FIX 4=> κ Γ i.
  case=>//=; intros; f_equal; try apply FIX; try (funext=>/= ?; apply FIX);
  try apply (FIX _ (_::_;ᵞ_) (S _)); try (by case: s gn);
  by case (stakedrop i s).
Qed.

(** [nsubst P Φ]: Substitute [Φ] for the only unguarded variable of [P] *)
Definition nsubst {κ V} (P : nProp κ ([V];ᵞ )) (Φ : nPred V) : nProp κ (;ᵞ) :=
  nsubstlu (i:=0) P -[Φ] eq_refl.

(** [nsubst] commutes with [nlarge] *)
Lemma nsubst_nlarge {κ V} {P : nProp κ ([V];ᵞ )} {Φ} :
  nsubst (nlarge P) Φ = nlarge (nsubst P Φ).
Proof. apply (nsubstlu_nlarge (Γ:=([_];ᵞ)) (i:=0)). Qed.

(** ** [nheight P]: Height of [P] *)

Fixpoint nheight {κ Γ} (P : nProp κ Γ) : hgt :=
  match P with
  | n_0 _ | n_g1 _ _ | %ᵍˢ _ | %ᵍˡ _ | %ᵘˢ _ | !ᵘˢ _ => Hgt₀
  | n_1 _ P | ∀: _, P | ∃: _, P => Hgt₁ (nheight P)
  | n_2 _ P Q => Hgt₂ (nheight P) (nheight Q)
  | ∀' Φ | ∃' Φ => Hgtᶠ (nheight ∘ Φ)
  | rec:ˢ' Φ a | rec:ˡ' Φ a => Hgt₁ (nheight (Φ a))
  end%n.

(** [nsubstlu] preserves [nheight] *)
Lemma nsubstlu_nheight {κ Γ i} {P : nProp κ Γ} {Φs gn} :
  nheight (nsubstlu (i:=i) P Φs gn) = nheight P.
Proof.
  move: κ Γ i P Φs gn. fix FIX 4=> ???.
  case=>//=; intros; try (f_equal; (apply FIX ||
    (funext=>/= ?; apply FIX) || apply (FIX _ (_::_;ᵞ_) (S _))));
    try (by move: gn; case s); try (by case (stakedrop _ s)).
Qed.

(** [nsubst] preserves [nheight] *)
Lemma nsubst_nheight {κ V P Φ} : nheight (nsubst (κ:=κ) (V:=V) P Φ) = nheight P.
Proof. exact (nsubstlu_nheight (Γ:=([_];ᵞ)) (i:=0)). Qed.
