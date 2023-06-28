(** * [tintp]: Interpretation of [type] as [iProp] *)

From nola.examples.type Require Export subst iris.
From nola.examples.heap_lang Require Export notation.
Import EqNotations.

(** Modification of [tsubst] *)
Definition tsubst' {i k Γᵘ Γᵍ} (T : type i (k :: Γᵘ;ᵞ Γᵍ))
  (un : Γᵘ = []) (gn : Γᵍ = []) : type k (;ᵞ) → type i (;ᵞ) :=
  tsubst (rew ctxeq_ug (f_equal (_ ::.) un) gn in T).
Arguments tsubst' {_ _ _ _} _ _ _ /.

(** [tsubst'] preserves [thgt] *)
Lemma tsubst'_thgt {i k Γᵘ Γᵍ} {T : type i (k :: Γᵘ;ᵞ Γᵍ)} {un gn V} :
  thgt (tsubst' T un gn V) = thgt T.
Proof. subst. apply tsubst_thgt. Qed.

(** ** [tintp]: Interpretation of [type] as [iProp] *)

Section tintp.
  Context
    (* Iris resources *) `{!tintpGS L Σ}
    (* Strong interpretation *) (s : tsintp_ty Σ).

  (** [tintp']: Interpretation of [type], taking an inducive hypothesis *)
  Fixpoint tintp' {i Γ} (T : type i Γ) (H : hAcc (thgt T))
    : (∀ k, k <ⁿ i → type k (;ᵞ) → val → iProp Σ) →
      Γ.ᵞu = [] → Γ.ᵞg = [] → val → iProp Σ :=
    match T, H with
    | ℕ, _ => λ _ _ _ v, ∃ n : nat, ⌜v = # n⌝
    | ref[o] T, _ => λ _ un gn v, ∃ l,
        tinv s (l +ₗ o) (rew eq_nil_ug_g un gn in T)
    | T ∧ᵗ U, _ => λ IH un gn v,
        tintp' T (H ‼ʰ 0) IH un gn v ∗ tintp' U (H ‼ʰ 1) IH un gn v
    | T →{ji}(j) U, _ => λ IH un gn v, □ ∀ u,
        tintp' T (H ‼ʰ 0) IH un gn u -∗
          WP[tinv_wsat' j (λ k kj, IH k (nlt_nle_trans kj ji))]
            v u [{ w, tintp' U (H ‼ʰ 1) IH un gn w }]
    | ∀: _, T, _ => λ IH un gn v, ∀ V,
        tintp' (tsubst' T un gn V) (H ‼ʰ[tsubst'_thgt] 0) IH eq_refl eq_refl v
    | ∃: _, T, _ => λ IH un gn v, ∃ V,
        tintp' (tsubst' T un gn V) (H ‼ʰ[tsubst'_thgt] 0) IH eq_refl eq_refl v
    | (recᵗ: j, T), _ => λ IH un gn, tintp'
        (↑ˡ (tsubst' T un gn (rew ctxeq_ug un gn in (recᵗ: j, T))))
        (H ‼ʰ[eq_trans tbump_thgt tsubst'_thgt] 0) IH eq_refl eq_refl
    | ¢ᵘ _, _ => λ _ (un : _::_ = _), match un with end
    | ¢ᵍ _, _ => λ _ _ (gn : _::_ = _), match gn with end
    | %ᵍ s, _ => λ _ _, seqnil s | %ᵘ s, _ => λ _, seqnil s
    | !ᵘ T, _ => λ IH _ _, IH _ _ T
    end%I.

  (** [tintp_lt]: Interpretation of [type i] over any [i <ⁿ M] *)
  Fixpoint tintp_lt M `{iM : ! i <ⁿ M} (T : type i (;ᵞ)) : val → iProp Σ :=
    match M, iM with 0, _ => nlt_no0 | S M', _ =>
      tintp' T hwf (λ k ki, tintp_lt M' (iM:=nlt_nlt_S_trans ki iM))
        eq_refl eq_refl
    end.
End tintp.
Arguments tintp_lt : simpl never.

(** Notations, which will be printed in (partial) interpretation, yay! *)
Notation "⟦ T ⟧{ i } ( s , H ; k , ki , U , IH )" :=
  (tintp' s (Γ:=(;ᵞ)) (i:=i) T H (λ k ki U, IH) eq_refl eq_refl)
  (only parsing) : nola_scope.
Notation "⟦ T ⟧ ( s , H ; k , ki , U , IH )" := ⟦ T ⟧{_}(s, H; k, ki, U, IH)
  (format "'[' ⟦  T  ⟧ '/  ' ( s ,  H ;  k ,  ki ,  U ,  '/  ' IH ) ']'")
  : nola_scope.
Notation "⟦ T ⟧ ( s ; k , ki , U , IH )" := ⟦ T ⟧(s, hwf; k, ki, U, IH)
  (format "'[' ⟦  T  ⟧ '/  ' ( s ;  k ,  ki ,  U ,  '/  ' IH ) ']'")
  : nola_scope.
(** Interpretation for [T : type i (;ᵞ)] *)
Notation tintp s i T := ⟦ T ⟧{i}(s, hwf;
  k, ki, U, tintp_lt s i (iM:=nlt_nlt_S_trans ki nlt_refl) U) (only parsing).
Notation "⟦ T ⟧{ i } ( s )" := (tintp s i T) (only parsing) : nola_scope.
Notation "⟦ T ⟧ ( s )" := ⟦ T ⟧{_}(s) (format "'[' ⟦  T  ⟧ '/  ' ( s ) ']'")
  : nola_scope.
