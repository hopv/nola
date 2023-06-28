(** * Substitution for [type] *)

From nola.examples.type Require Export type.
From nola.util Require Export hgt.
Import EqNotations.

(** ** [tlift]: Turn [type i (;ᵞ)] into [type i Γ] *)

(** [tliftg]: Turn [type i (;ᵞ)] into [type i (;ᵞ Γᵍ)] *)
Fixpoint tliftg {i Γᵍ} (T : type i (;ᵞ)) : type i (;ᵞ Γᵍ) :=
  match Γᵍ with [] => T | _ :: _ => ¢ᵍ (tliftg T) end.

(** [tliftg] commutes with [↑ᵗ] *)
Lemma tliftg_tbump `{ij : ! i ≤ⁿ j} {Γᵍ T} :
  tliftg (↑ᵗ T) = ↑ᵗ{ij} (tliftg (Γᵍ:=Γᵍ) T).
Proof. by elim Γᵍ; [done|]=>/= ??->. Qed.

(** [tliftu]: Turn [type i (;ᵞ Γᵍ)] into [type i (Γᵘ;ᵞ Γᵍ)] *)
Fixpoint tliftu {i Γᵘ Γᵍ} (T : type i (;ᵞ Γᵍ)) : type i (Γᵘ;ᵞ Γᵍ) :=
  match Γᵘ with [] => T | _ :: _ => ¢ᵘ (tliftu T) end.

(** [tliftu] commutes with [↑ᵗ] *)
Lemma tliftu_tbump `{ij : ! i ≤ⁿ j}  {Γᵘ Γᵍ T}:
  tliftu (↑ᵗ T) = ↑ᵗ{ij} (tliftu (Γᵘ:=Γᵘ) (Γᵍ:=Γᵍ) T).
Proof. by elim Γᵘ; [done|]=>/= ??->. Qed.

(** [tlift]: Turn [type i (;ᵞ)] into [type i Γᵘ] *)
Definition tlift {i Γ} (T : type i (;ᵞ)) : type i Γ := tliftu (tliftg T).
Arguments tlift {i Γ} T /.

(** [tlift] commutes with [↑ᵗ] *)
Lemma tlift_tbump `{ij : ! i ≤ⁿ j} {Γ T} :
  tlift (↑ᵗ T) = ↑ᵗ{ij} (tlift (Γ:=Γ) T).
Proof. by rewrite/= tliftg_tbump tliftu_tbump. Qed.

(** ** [T /: U]: Substitute [U] for [T]'s only unguarded variable *)

(** [tsubstlg V T]: Substitute [V] for [T]'s last guarded variable *)
Fixpoint tsubstlg {i Γ Γᵍ k} (V : type k (;ᵞ)) (T : type i Γ)
  : Γ.ᵞg = Γᵍ ++ [k] → type i (Γ.ᵞu;ᵞ Γᵍ) :=
  match T with
  | ℕ => λ _, ℕ
  | ref[o] T => λ eq, ref[o] tsubstlg V T (eq_app_assoc_d eq)
  | ▽ T => λ eq, ▽ tsubstlg V T (eq_app_assoc_d eq)
  | T ∧ᵗ U => λ eq, tsubstlg V T eq ∧ᵗ tsubstlg V U eq
  | T →(j) U => λ eq, tsubstlg V T eq →(j) tsubstlg V U eq
  | ∀: j, T => λ eq, ∀: j, tsubstlg V T eq
  | ∃: j, T => λ eq, ∃: j, tsubstlg V T eq
  | recᵗ: j, T => λ eq, recᵗ: j, tsubstlg V T eq
  | ¢ᵘ T => λ eq, ¢ᵘ (tsubstlg V T eq)
  | ¢ᵍ{Δᵍ} T => match Γᵍ with
    | _::_ => λ eq, ¢ᵍ (tsubstlg V T (f_equal tail eq))
    | [] => match Δᵍ, T with [], _ => λ _, T
      | _::_, _ => λ eq : _::_ = _, match eq with end end end
  | %ᵍ s => λ eq, match sunapp (rew eq in s) with
      inl s => %ᵍ s | inr s => tlift (↑ᵗ{sunsingl s} V) end
  | %ᵘ s => λ _, %ᵘ s | !ᵘ T => λ _, !ᵘ T
  end.

(** [T /:ᵍ V]: Substitute [V] for [T]'s only unguarded variable *)
Definition tsubstg {i k} (T : type i (;ᵞ [k])) (V : type k (;ᵞ))
  : type i (;ᵞ) := tsubstlg (Γᵍ:=[]) V T eq_refl.
Arguments tsubstg {_ _} _ _ /.
Infix "/:ᵍ" := tsubstg (at level 25, no associativity).

(** [/:ᵍ] on [¢ᵍ T] *)
Fact tsubstg_t_constg {i k} {T : type i (;ᵞ)} {V : type k (;ᵞ)} :
  ¢ᵍ T /:ᵍ V = T.
Proof. done. Qed.

(** [tsubstlg] commutes with [↑ᵗ] *)
Lemma tsubstlg_tbump `{ij : ! i ≤ⁿ j} {k V Γ Γᵍ T eq} :
  tsubstlg V (↑ᵗ T) eq = ↑ᵗ{ij} (@tsubstlg i Γ Γᵍ k V T eq).
Proof.
  move: i j Γ Γᵍ T ij eq. fix FIX 5=> i j Γ Γᵍ.
  case=>//=; intros; try (f_equal; apply (FIX _ _ (_;ᵞ_))).
  - destruct Γᵍ=>/=; [by destruct Γᵍ0|]. f_equal. apply (FIX _ _ (_;ᵞ_)).
  - subst=>/=. rewrite sunapp_strans. case: (sunapp s)=>//= ?.
    rewrite -tliftu_tbump -tliftg_tbump. do 2 f_equal; symmetry.
    apply tbump_tbump.
Qed.

(** [tsubstlu V T]: Substitute [V] for [T]'s last unguarded variable *)
Fixpoint tsubstlu {i Γ Γᵘ k} (V : type k (;ᵞ)) (T : type i Γ)
  : Γ.ᵞu = Γᵘ ++ [k] → Γ.ᵞg = [] → type i (Γᵘ;ᵞ ) :=
  match T with
  | ℕ => λ _ _, ℕ
  | ref[o] T => λ eq gn, ref[o]
      rew ctxeq_g app_nil'_d in tsubstlg V T (eq_trans (app_eq_nil_d gn) eq)
  | ▽ T => λ eq gn, ▽
      rew ctxeq_g app_nil'_d in tsubstlg V T (eq_trans (app_eq_nil_d gn) eq)
  | T ∧ᵗ U => λ eq gn, tsubstlu V T eq gn ∧ᵗ tsubstlu V U eq gn
  | T →(j) U => λ eq gn, tsubstlu V T eq gn →(j) tsubstlu V U eq gn
  | ∀: j, T => λ eq gn, ∀: j, tsubstlu V T (f_equal _ eq) gn
  | ∃: j, T => λ eq gn, ∃: j, tsubstlu V T (f_equal _ eq) gn
  | recᵗ: j, T => λ eq gn, recᵗ: j, tsubstlu V T (f_equal _ eq) gn
  | ¢ᵘ{Δᵘ} T => match Γᵘ with
    | _::_ => λ eq gn, ¢ᵘ (tsubstlu V T (f_equal tail eq) gn)
    | [] => match Δᵘ, T with [], _ => λ _ gn, rew ctxeq_g gn in T
      | _::_, _ => λ eq : _::_ = _, match eq with end end end
  | ¢ᵍ T => λ _ (gn : _::_ = _), match gn with end
  | %ᵍ s => λ _, seqnil s
  | %ᵘ s => λ eq _, match sunapp (rew eq in s) with
      inl s => %ᵘ s | inr s => !ᵘ{sunsingl s} V end
  | !ᵘ T => λ _ _, !ᵘ T
  end.

(** [tsubstlu] commutes with [↑ᵗ] *)
Lemma tsubstlu_tbump `{ij : ! i ≤ⁿ j} {k V Γ Γᵘ T eq gn} :
  tsubstlu V (↑ᵗ T) eq gn = ↑ᵗ{ij} (@tsubstlu i Γ Γᵘ k V T eq gn).
Proof.
  move: i j Γ Γᵘ T ij eq gn. fix FIX 5=> i j Γ Γᵘ.
  case=>//=; intros; f_equal; try apply FIX; try apply FIX; try (by case: s gn);
    subst=>/=.
  - destruct Γᵘ=>/=; [by destruct Γᵘ0|]. f_equal. apply FIX.
  - rewrite sunapp_strans. case: (sunapp s)=>//= ?. f_equal. apply proof_irrel.
Qed.

(** [T /: V]: Substitute [V] for [T]'s only unguarded variable *)
Definition tsubst {i k} (T : type i ([k];ᵞ )) V : type i (;ᵞ) :=
  tsubstlu (Γᵘ:=[]) V T eq_refl eq_refl.
Arguments tsubst {_ _} _ _ /.
Infix "/:" := tsubst (at level 25, no associativity).

(** [/:] on [¢ᵘ] *)
Fact tsubst_n_constu {i k} {V : type k (;ᵞ)} {T : type i (;ᵞ)} : ¢ᵘ T /: V = T.
Proof. done. Qed.

(** [/:] commutes with [↑ᵗ] *)
Lemma tsubst_tbump `{ij : ! i ≤ⁿ j} {k V} {T : type i ([k];ᵞ )} :
  ↑ᵗ T /: V = ↑ᵗ{ij} (T /: V).
Proof. exact tsubstlu_tbump. Qed.

(** ** [thgt T]: Height of [T] *)

Fixpoint thgt {i Γ} (T : type i Γ) : hgt :=
  match T with
  | ℕ | ref[_] _ | ▽ _ | ¢ᵍ _ | %ᵍ _ | %ᵘ _ | !ᵘ _ => Hgt₀
  | ¢ᵘ T => thgt T | ∀: _, T | ∃: _, T | recᵗ: _, T => Hgt₁ (thgt T)
  | T ∧ᵗ U | T →(_) U => Hgt₂ (thgt T) (thgt U)
  end.

(** [tsubstlu] preserves [thgt] *)
Lemma tsubstlu_thgt {i Γ Γᵘ k V T eq gn} :
  thgt (@tsubstlu i Γ Γᵘ k V T eq gn) = thgt T.
Proof.
  move: i Γ Γᵘ T eq gn. fix FIX 4=> ?? Γᵘ.
  case=>//=; intros; try (f_equal; apply FIX); try (by case: s gn);
    try by case (sunapp _).
  subst. destruct Γᵘ=>/=; [by destruct Γᵘ0=>/=|]. f_equal. apply FIX.
Qed.

(** [/:] preserves [thgt] *)
Lemma tsubst_thgt {i k} {T : type i ([k];ᵞ )} {V} : thgt (T /: V) = thgt T.
Proof. exact tsubstlu_thgt. Qed.

(** [↑ᵗ] preserves [thgt] *)
Lemma tbump_thgt `{ij : ! i ≤ⁿ j} {Γ} {T : type i Γ} : thgt (↑ᵗ{ij} T) = thgt T.
Proof.
  move: i Γ T ij. fix FIX 3=> i Γ T. case T=>//= >; f_equal; apply FIX.
Qed.
