(** * Substitution for [nProp] *)

From nola.examples.logic Require Export prop.
From nola.util Require Export funext hgt.
Import EqNotations.

(** ** [nlift]: Turn [nProp κ (;ᵞ)] into [nProp κ Γ] *)

(** [nliftg]: Add guarded variables at the bottom *)

Fixpoint nliftg {Δ κ Γ} (P : nProp κ Γ) : nProp κ (Γ.ᵞu;ᵞ Γ.ᵞg ++ Δ) :=
  match P with
  | n_0 c => n_0 c | n_l0 c => n_l0 c | n_1 c P => n_1 c (nliftg P)
  | n_2 c P Q => n_2 c (nliftg P) (nliftg Q)
  | n_g1 c P => n_g1 c (rew ctxeq_g app_assoc'_d in nliftg P)
  | ∀' Φ => ∀ a, nliftg (Φ a) | ∃' Φ => ∃ a, nliftg (Φ a)
  | n_wpw W s E e Φ => n_wpw (nliftg W) s E e (λ v, nliftg (Φ v))
  | n_twpw W s E e Φ => n_twpw (nliftg W) s E e (λ v, nliftg (Φ v))
  | ∀: V, P => ∀: V, nliftg P | ∃: V, P => ∃: V, nliftg P
  | rec:ˢ' Φ a => (rec:ˢ b, nliftg (Φ b)) a
  | rec:ˡ' Φ a => (rec:ˡ b, nliftg (Φ b)) a
  | %ᵍˢ s => %ᵍˢ sbylapp s _ | %ᵍˡ s => %ᵍˡ sbylapp s _ | %ᵘˢ s => %ᵘˢ s
  | !ᵘˢ P => !ᵘˢ P
  end%n.

(** [nliftg] commutes with [↑ˡ] *)
Lemma nliftg_nlarge {κ Γ Δ} {P : nProp κ Γ} :
  nliftg (Δ:=Δ) (↑ˡ P) = ↑ˡ (nliftg P).
Proof.
  move: κ Γ P. fix FIX 3=> κ Γ.
  case=>//= *; f_equal; try apply FIX; try (funext=> ?; apply FIX);
    apply (FIX _ (_::_;ᵞ_)).
Qed.

(** [nliftug]: Add unguarded and guarded variables at the bottom *)
Fixpoint nliftug {Δᵘ Δᵍ κ Γ} (P : nProp κ Γ)
  : Γ.ᵞg = [] → nProp κ (Γ.ᵞu ++ Δᵘ;ᵞ Δᵍ) :=
  match P with
  | n_0 c => λ _, n_0 c | n_l0 c => λ _, n_l0 c
  | n_1 c P => λ gn, n_1 c (nliftug P gn)
  | n_2 c P Q => λ gn, n_2 c (nliftug P gn) (nliftug Q gn)
  | n_g1 c P => λ gn, n_g1 c (rew app_assoc_eq_nil_g gn in nliftg P)
  | ∀' Φ => λ gn, ∀ a, nliftug (Φ a) gn | ∃' Φ => λ gn, ∃ a, nliftug (Φ a) gn
  | n_wpw W s E e Φ => λ gn, n_wpw (nliftug W gn) s E e (λ v, nliftug (Φ v) gn)
  | n_twpw W s E e Φ => λ gn,
      n_twpw (nliftug W gn) s E e (λ v, nliftug (Φ v) gn)
  | ∀: V, P => λ gn, ∀: V, nliftug P gn | ∃: V, P => λ gn, ∃: V, nliftug P gn
  | rec:ˢ' Φ a => λ gn, (rec:ˢ b, nliftug (Φ b) gn) a
  | rec:ˡ' Φ a => λ gn, (rec:ˡ b, nliftug (Φ b) gn) a
  | %ᵍˢ s | %ᵍˡ s => seqnil s | %ᵘˢ s => λ _, %ᵘˢ sbylapp s _
  | !ᵘˢ P => λ _, !ᵘˢ P
  end%n.

(** [nliftug] commutes with [↑ˡ] *)
Lemma nliftug_nlarge {κ Γ Δᵘ Δᵍ} {P : nProp κ Γ} {gn} :
  nliftug (Δᵘ:=Δᵘ) (Δᵍ:=Δᵍ) (↑ˡ P) gn = ↑ˡ (nliftug P gn).
Proof.
  move: κ Γ P gn. fix FIX 3=> κ Γ.
  case=>//=; intros; f_equal; try apply FIX; try (funext=> ?; apply FIX);
  try apply (FIX _ (_::_;ᵞ_)); by case: s gn.
Qed.

(** [nlift]: Turn [nProp κ (;ᵞ)] into [nProp κ Γ] *)
Definition nlift {κ Γ} (P : nProp κ (;ᵞ)) : nProp κ Γ := nliftug P eq_refl.
Arguments nlift {_ _} _ /.

(** [nlift] commutes with [↑ˡ] *)
Lemma nlift_nlarge {κ Γ} {P : nProp κ (;ᵞ)} :
  nlift (Γ:=Γ) (↑ˡ P) = ↑ˡ (nlift P).
Proof. apply (nliftug_nlarge (Γ:=(;ᵞ))). Qed.

(** ** [P /: Φ]: Substitute [Φ] for [P]'s only unguarded variable *)

(** [nPred V]: Type of an instantiation of [V : npvar] *)
Definition nPred : npvar → Type := λ '(A →nP κ), A → nProp κ (;ᵞ).
Bind Scope nProp_scope with nPred.

(** Apply to [nparg κ V] [nPred V] *)
Definition napply {κ V} : nparg κ V → nPred V → nProp κ (;ᵞ) :=
  λ '(@! a) Φ, Φ a.

(** [nsubstlg P Φ]: Substitute [Φ] for [P]'s last guarded variable *)
Fixpoint nsubstlg {κ Γ Γᵍ V} (P : nProp κ Γ) (Φ : nPred V)
  : Γ.ᵞg = Γᵍ ++ [V] → nProp κ (Γ.ᵞu;ᵞ Γᵍ) :=
  match P with
  | n_0 c => λ _, n_0 c | n_l0 c => λ _, n_l0 c
  | n_1 c P => λ eq, n_1 c (nsubstlg P Φ eq)
  | n_2 c P Q => λ eq, n_2 c (nsubstlg P Φ eq) (nsubstlg Q Φ eq)
  | n_g1 c P => λ eq, n_g1 c (nsubstlg P Φ (eq_app_assoc_d eq))
  | ∀' Ψ => λ eq, ∀ a, nsubstlg (Ψ a) Φ eq
  | ∃' Ψ => λ eq, ∃ a, nsubstlg (Ψ a) Φ eq
  | n_wpw W s E e Ψ => λ eq,
      n_wpw (nsubstlg W Φ eq) s E e (λ v, nsubstlg (Ψ v) Φ eq)
  | n_twpw W s E e Ψ => λ eq,
      n_twpw (nsubstlg W Φ eq) s E e (λ v, nsubstlg (Ψ v) Φ eq)
  | ∀: V, P => λ eq, ∀: V, nsubstlg P Φ eq
  | ∃: V, P => λ eq, ∃: V, nsubstlg P Φ eq
  | rec:ˢ' Ψ a => λ eq, (rec:ˢ b, nsubstlg (Ψ b) Φ eq) a
  | rec:ˡ' Ψ a => λ eq, (rec:ˡ b, nsubstlg (Ψ b) Φ eq) a
  | %ᵍˢ s => λ eq, match sunapp (rew eq in s) with
      inl s => %ᵍˢ s | inr s => nlift (nunsmall (napply (sunsingl s) Φ)) end
  | %ᵍˡ s => λ eq, match sunapp (rew eq in s) with
      inl s => %ᵍˡ s | inr s => nlift (napply (sunsingl s) Φ) end
  | %ᵘˢ s => λ _, %ᵘˢ s | !ᵘˢ P => λ _, !ᵘˢ P
  end%n.

(** [nsubstlg] commutes with [↑ˡ] *)
Lemma nsubstlg_nlarge {κ Γ V Γᵍ} {P : nProp κ Γ} {Φ} {eq : Γ.ᵞg = Γᵍ ++ [V] } :
  nsubstlg (↑ˡ P) Φ eq = ↑ˡ (nsubstlg P Φ eq).
Proof.
  move: κ Γ P Φ eq. fix FIX 3=> κ Γ.
  case=>//=; intros;
    try (f_equal; apply (FIX _ (_;ᵞ_)) || (funext=>/= ?; apply FIX));
    subst=>/=; case (sunapp s)=>//= ?; rewrite -nlift_nlarge /=; f_equal;
    symmetry; [apply nlarge_nunsmall|apply nlarge_id].
Qed.

(** [nsubstlu i P Φ]: Substitute [Φ] for [P]'s last unguarded variable *)
Fixpoint nsubstlu {κ Γ Γᵘ V} (P : nProp κ Γ) (Φ : nPred V)
  : Γ.ᵞu = Γᵘ ++ [V] → Γ.ᵞg = [] → nProp κ (Γᵘ;ᵞ ) :=
  match P with
  | n_0 c => λ _ _, n_0 c | n_l0 c => λ _ _, n_l0 c
  | n_1 c P => λ eq gn, n_1 c (nsubstlu P Φ eq gn)
  | n_2 c P Q => λ eq gn, n_2 c (nsubstlu P Φ eq gn) (nsubstlu Q Φ eq gn)
  | n_g1 c P => λ eq gn, n_g1 c
      (rew ctxeq_g app_nil'_d in nsubstlg P Φ (eq_trans (app_eq_nil_d gn) eq))
  | ∀' Ψ => λ eq gn, ∀ a, nsubstlu (Ψ a) Φ eq gn
  | ∃' Ψ => λ eq gn, ∃ a, nsubstlu (Ψ a) Φ eq gn
  | n_wpw W s E e Ψ => λ eq gn,
      n_wpw (nsubstlu W Φ eq gn) s E e (λ v, nsubstlu (Ψ v) Φ eq gn)
  | n_twpw W s E e Ψ => λ eq gn,
      n_twpw (nsubstlu W Φ eq gn) s E e (λ v, nsubstlu (Ψ v) Φ eq gn)
  | ∀: V, P => λ eq gn, ∀: V, nsubstlu P Φ (f_equal _ eq) gn
  | ∃: V, P => λ eq gn, ∃: V, nsubstlu P Φ (f_equal _ eq) gn
  | rec:ˢ' Ψ a => λ eq gn, (rec:ˢ b, nsubstlu (Ψ b) Φ (f_equal _ eq) gn) a
  | rec:ˡ' Ψ a => λ eq gn, (rec:ˡ b, nsubstlu (Ψ b) Φ (f_equal _ eq) gn) a
  | %ᵍˢ s | %ᵍˡ s => λ _, seqnil s
  | %ᵘˢ s => λ eq _, match sunapp (rew eq in s) with
      inl s => %ᵘˢ s | inr s => !ᵘˢ (napply (sunsingl s) Φ) end
  | !ᵘˢ P => λ _ _, !ᵘˢ P
  end%n.

(** [nsubstlu] commutes with [↑ˡ] *)
Lemma nsubstlu_nlarge {κ Γ Γᵘ V}
  {P : nProp κ Γ} {Φ} {eq : Γ.ᵞu = Γᵘ ++ [V] } {gn} :
  nsubstlu (↑ˡ P) Φ eq gn = ↑ˡ (nsubstlu P Φ eq gn).
Proof.
  move: κ Γ Γᵘ P Φ eq gn. fix FIX 4=> κ Γ Γᵘ.
  case=>//=; intros; f_equal; try apply FIX; try (funext=>/= ?; apply FIX);
    try (by case: s gn). subst=>/=. by case (sunapp s).
Qed.

(** [P /: Φ]: Substitute [Φ] for [P]'s only unguarded variable *)
Definition nsubst {κ V} (P : nProp κ ([V];ᵞ )) (Φ : nPred V) : nProp κ (;ᵞ) :=
  nsubstlu (Γᵘ:=[]) P Φ eq_refl eq_refl.
Infix "/:" := nsubst (at level 25, no associativity).

(** [/:=] commutes with [↑ˡ] *)
Lemma nsubst_nlarge {κ V} {P : nProp κ ([V];ᵞ )} {Φ} : ↑ˡ P /: Φ = ↑ˡ (P /: Φ).
Proof. exact nsubstlu_nlarge. Qed.

(** ** [nhgt P]: Height of [P] *)

Fixpoint nhgt {κ Γ} (P : nProp κ Γ) : hgt :=
  match P with
  | n_0 _ | n_l0 _ | n_g1 _ _ | %ᵍˢ _ | %ᵍˡ _ | %ᵘˢ _ | !ᵘˢ _ => Hgt₀
  | n_1 _ P | ∀: _, P | ∃: _, P => Hgt₁ (nhgt P)
  | n_2 _ P Q => Hgt₂ (nhgt P) (nhgt Q)
  | ∀' Φ | ∃' Φ => Hgtᶠ (λ a, nhgt (Φ a))
  | n_wpw W _ _ _ Φ | n_twpw W _ _ _ Φ =>
      Hgt₂ (nhgt W) (Hgtᶠ (λ a, nhgt (Φ a)))
  | rec:ˢ' Φ a | rec:ˡ' Φ a => Hgt₁ (nhgt (Φ a))
  end%n.

(** [nsubstlu] preserves [nhgt] *)
Lemma nsubstlu_nhgt {κ Γ Γᵘ V}
  {P : nProp κ Γ} {Φ} {eq : Γ.ᵞu = Γᵘ ++ [V] } {gn} :
  nhgt (nsubstlu P Φ eq gn) = nhgt P.
Proof.
  move: κ Γ Γᵘ P Φ eq gn. fix FIX 4=> ???.
  case=>//=; intros;
    try (f_equal; (apply FIX || (try f_equal); funext=>/= ?; apply FIX));
    try (by case: s gn). subst=>/=. by case (sunapp s).
Qed.

(** [/:=] preserves [nhgt] *)
Lemma nsubst_nhgt {κ V} {P : nProp κ ([V];ᵞ )} {Φ} : nhgt (P /: Φ) = nhgt P.
Proof. exact nsubstlu_nhgt. Qed.
