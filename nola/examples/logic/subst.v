(** * Substitution for [nProp] *)

From nola.examples.logic Require Export prop.
From nola.util Require Export funext hgt.
Import EqNotations.

(** ** [nlift]: Turn [nProp κ (;ᵞ)] into [nProp κ Γ] *)

(** [nliftg]: Turn [nProp κ (;ᵞ)] into [nProp κ (;ᵞ Γᵍ)] *)
Fixpoint nliftg {κ Γᵍ} (P : nProp κ (;ᵞ)) : nProp κ (;ᵞ Γᵍ) :=
  match Γᵍ with [] => P | _ :: _ => ¢ᵍ (nliftg P) end.

(** [nliftg] commutes with [↑ˡ] *)
Lemma nliftg_nlarge {κ Γᵍ P} : nliftg (Γᵍ:=Γᵍ) (↑ˡ P) = ↑ˡ (nliftg (κ:=κ) P).
Proof. by elim Γᵍ; [done|]=>/= ??->. Qed.

(** [nliftu]: Turn [nProp κ (;ᵞ Γᵍ)] into [nProp κ (Γᵘ;ᵞ Γᵍ)] *)
Fixpoint nliftu {κ Γᵘ Γᵍ} (P : nProp κ (;ᵞ Γᵍ)) : nProp κ (Γᵘ;ᵞ Γᵍ) :=
  match Γᵘ with [] => P | _ :: _ => ¢ᵘ (nliftu P) end.

(** [nliftu] commutes with [↑ˡ] *)
Lemma nliftu_nlarge {κ Γᵘ Γᵍ P} :
  nliftu (Γᵘ:=Γᵘ) (Γᵍ:=Γᵍ) (↑ˡ P) = ↑ˡ (nliftu (κ:=κ) P).
Proof. by elim Γᵘ; [done|]=>/= ??->. Qed.

(** [nlift]: Turn [nProp κ (;ᵞ)] into [nProp κ Γᵘ] *)
Definition nlift {κ Γ} (P : nProp κ (;ᵞ)) : nProp κ Γ := nliftu (nliftg P).
Arguments nlift {κ Γ} P /.

(** [nlift] commutes with [↑ˡ] *)
Lemma nlift_nlarge {κ Γ P} : nlift (Γ:=Γ) (↑ˡ P) = ↑ˡ (nlift (κ:=κ) P).
Proof. by rewrite/= nliftg_nlarge nliftu_nlarge. Qed.

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
  | ¢ᵘ P => λ eq, ¢ᵘ (nsubstlg P Φ eq)
  | ¢ᵍ{Δᵍ} P => match Γᵍ with
    | _::_ => λ eq, ¢ᵍ (nsubstlg P Φ (f_equal tail eq))
    | [] => match Δᵍ, P with [], _ => λ _, P
      | _::_, _ => λ eq : _::_ = _, match eq with end end end
  | %ᵍˢ s => λ eq, match sunapp (rew eq in s) with
      inl s => %ᵍˢ s | inr s => nlift (nunsmall (napply (sunsingl s) Φ)) end
  | %ᵍˡ s => λ eq, match sunapp (rew eq in s) with
      inl s => %ᵍˡ s | inr s => nlift (napply (sunsingl s) Φ) end
  | %ᵘˢ s => λ _, %ᵘˢ s | !ᵘˢ P => λ _, !ᵘˢ P
  end%n.

(** [nsubstlg] on [¢ᵍ P] for [P : nProp κ (;ᵞ)] *)
Fact nsubstlg_n_constg {κ V} {P : nProp κ (;ᵞ)} {Φ : nPred V} {eq : [V] = _} :
  nsubstlg (¢ᵍ P) Φ eq = P.
Proof. done. Qed.

(** [nsubstlg] commutes with [↑ˡ] *)
Lemma nsubstlg_nlarge {κ Γ V Γᵍ} {P : nProp κ Γ} {Φ} {eq : Γ.ᵞg = Γᵍ ++ [V] } :
  nsubstlg (↑ˡ P) Φ eq = ↑ˡ (nsubstlg P Φ eq).
Proof.
  move: κ Γ Γᵍ P Φ eq. fix FIX 4=> κ Γ Γᵍ.
  case=>//=; intros;
    try (f_equal; try (funext=> ?); apply (FIX _ (_;ᵞ_)));
    try (destruct Γᵍ=>/=; [by destruct Γᵍ0|f_equal; apply (FIX _ (;ᵞ_))]);
    subst=>/=; case (sunapp s)=>//= ?; rewrite -nliftu_nlarge -nliftg_nlarge;
    do 2 f_equal; symmetry; [apply nlarge_nunsmall|apply nlarge_id].
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
  | ¢ᵘ{Δᵘ} P => match Γᵘ with
    | _::_ => λ eq gn, ¢ᵘ (nsubstlu P Φ (f_equal tail eq) gn)
    | [] => match Δᵘ, P with [], _ => λ _ gn, rew ctxeq_g gn in P
      | _::_, _ => λ eq : _::_ = _, match eq with end end end
  | ¢ᵍ P => λ _ (gn : _::_ = _), match gn with end
  | %ᵍˢ s | %ᵍˡ s => λ _, seqnil s
  | %ᵘˢ s => λ eq _, match sunapp (rew eq in s) with
      inl s => %ᵘˢ s | inr s => !ᵘˢ (napply (sunsingl s) Φ) end
  | !ᵘˢ P => λ _ _, !ᵘˢ P
  end%n.

(** [nsubstlu] commutes with [↑ˡ] *)
Lemma nsubstlu_nlarge {κ Γ Γᵘ V P Φ eq gn} :
  nsubstlu (↑ˡ P) Φ eq gn = ↑ˡ (@nsubstlu κ Γ Γᵘ V P Φ eq gn).
Proof.
  move: κ Γ Γᵘ P Φ eq gn. fix FIX 4=> κ Γ Γᵘ.
  case=>//=; intros; f_equal; try apply FIX; try (funext=>/= ?; apply FIX);
    try (by case: s gn); subst=>/=; try by case (sunapp s).
  destruct Γᵘ=>/=; [by destruct Γᵘ0|f_equal; apply FIX].
Qed.

(** [P /: Φ]: Substitute [Φ] for [P]'s only unguarded variable *)
Definition nsubst {κ V} (P : nProp κ ([V];ᵞ )) (Φ : nPred V) : nProp κ (;ᵞ) :=
  nsubstlu (Γᵘ:=[]) P Φ eq_refl eq_refl.
Infix "/:" := nsubst (at level 25, no associativity).

(** [/:] on [¢ᵘ] *)
Fact nsubst_n_constu {κ V} {P : nProp κ _} {Φ : nPred V} : ¢ᵘ P /: Φ = P.
Proof. done. Qed.

(** [/:] commutes with [↑ˡ] *)
Lemma nsubst_nlarge {κ V} {P : nProp κ ([V];ᵞ )} {Φ} : ↑ˡ P /: Φ = ↑ˡ (P /: Φ).
Proof. exact nsubstlu_nlarge. Qed.

(** ** [nhgt P]: Height of [P] *)

Fixpoint nhgt {κ Γ} (P : nProp κ Γ) : hgt :=
  match P with
  | n_0 _ | n_l0 _ | n_g1 _ _ | ¢ᵍ _ | %ᵍˢ _ | %ᵍˡ _ | %ᵘˢ _ | !ᵘˢ _ => Hgt₀
  | ¢ᵘ P => nhgt P | n_1 _ P | ∀: _, P | ∃: _, P => Hgt₁ (nhgt P)
  | n_2 _ P Q => Hgt₂ (nhgt P) (nhgt Q) | ∀' Φ | ∃' Φ => Hgtᶠ (λ a, nhgt (Φ a))
  | n_wpw W _ _ _ Φ | n_twpw W _ _ _ Φ => Hgt₂ (nhgt W) (Hgtᶠ (λ a, nhgt (Φ a)))
  | rec:ˢ' Φ a | rec:ˡ' Φ a => Hgt₁ (nhgt (Φ a))
  end%n.

(** [nsubstlu] preserves [nhgt] *)
Lemma nsubstlu_nhgt {κ Γ Γᵘ V P Φ eq gn} :
  nhgt (@nsubstlu κ Γ Γᵘ V P Φ eq gn) = nhgt P.
Proof.
  move: κ Γ Γᵘ P Φ eq gn. fix FIX 4=> ?? Γᵘ.
  case=>//=; intros;
    try (f_equal; try f_equal; try (funext=> ?); apply FIX);
    try (by case: s gn); subst=>/=; try by case (sunapp s).
  destruct Γᵘ=>/=; [by destruct Γᵘ0=>/=|f_equal; apply FIX].
Qed.

(** [/:] preserves [nhgt] *)
Lemma nsubst_nhgt {κ V} {P : nProp κ ([V];ᵞ )} {Φ} : nhgt (P /: Φ) = nhgt P.
Proof. exact nsubstlu_nhgt. Qed.
