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
    (* Derivability *) (s : tderiv_ty Σ).

  (** Interpret [tc_0] *)
  Definition tcintp0 (c : tcon0) v : iProp Σ :=
    match c with
    | ⟨ℕ⟩ => ∃ n : nat, ⌜v = # n⌝ | ⟨𝔹⟩ => ∃ b : bool, ⌜v = # b⌝
    | ⟨𝟙⟩ => ⌜v = # ()⌝ | ⟨⊤ᵗ⟩ => True
    end.
  #[export] Instance tcintp0_persistent {c v} : Persistent (tcintp0 c v).
  Proof. case c; exact _. Qed.

  (** Interpret [tc_2] *)
  Definition tcintp2 (c : tcon2) (Φ Ψ : val -d> iProp Σ) : val -d> iProp Σ :=
    λ v, match c with
    | ⟨∧ᵗ⟩ => Φ v ∗ Ψ v | ⟨×⟩ => ∃ u u', ⌜v = (u, u')%V⌝ ∗ Φ u ∗ Ψ u'
    end%I.
  #[export] Instance tcintp2_persistent
    `{!∀ v, Persistent (Φ v), !∀ v, Persistent (Ψ v)} {c v} :
    Persistent (tcintp2 c Φ Ψ v).
  Proof. case c; exact _. Qed.
  #[export] Instance tcincp2_proper :
    Proper ((=) ==> (≡) ==> (≡) ==> (=) ==> (⊣⊢)) tcintp2.
  Proof. solve_proper. Qed.

  (** [tintp']: Interpretation of [type], taking an inducive hypothesis *)
  Fixpoint tintp' {i Γ} (T : type i Γ) (H : hAcc (thgt T))
    : (∀ k, k <ⁿ i → type k (;ᵞ) → val → iProp Σ) →
      Γ.ᵞu = [] → Γ.ᵞg = [] → val → iProp Σ :=
    match T, H with
    | t_0 c, _ => λ _ _ _, tcintp0 c
    | t_2 c T U, _ => λ IH un gn, tcintp2 c
        (tintp' T (H ‼ʰ 0) IH un gn) (tintp' U (H ‼ʰ 1) IH un gn)
    | T →{ji}(j) U, _ => λ IH un gn v, □ ∀ u,
        tintp' T (H ‼ʰ 0) IH un gn u -∗
          WP[tinv_wsat' j (λ k kj, IH k (nlt_nle_trans kj ji))]
            v u [{ tintp' U (H ‼ʰ 1) IH un gn }]
    | ▽ T, _ => λ _ un gn v, tguard s (rew eq_nil_ug_g un gn in T) v
    | ref[o] T, _ => λ _ un gn v, ∃ l : loc, ⌜v = # l⌝ ∗
        tref s (l +ₗ o) (rew eq_nil_ug_g un gn in T)
    | ∀: _, T, _ => λ IH un gn v, ∀ V,
        tintp' (tsubst' T un gn V) (H ‼ʰ[tsubst'_thgt] 0) IH eq_refl eq_refl v
    | ∃: _, T, _ => λ IH un gn v, ∃ V,
        tintp' (tsubst' T un gn V) (H ‼ʰ[tsubst'_thgt] 0) IH eq_refl eq_refl v
    | recᵗ: j, T, _ => λ IH un gn, tintp'
        (↑ᵗ tsubst' T un gn (rew ctxeq_ug un gn in recᵗ: j, T))
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
Notation "⟦ T ⟧{ i } ( s , H ; IH )" :=
  (tintp' s (Γ:=(;ᵞ)) (i:=i) T H IH eq_refl eq_refl) (only parsing)
  : nola_scope.
Notation "⟦ T ⟧ ( s , H ; IH )" := ⟦ T ⟧{_}(s, H; IH)
  (format "'[' ⟦  T  ⟧ '/  ' ( s ,  H ;  '/  ' IH ) ']'") : nola_scope.
Notation "⟦ T ⟧ ( s ; IH )" := ⟦ T ⟧(s, hwf; IH)
  (format "'[' ⟦  T  ⟧ '/  ' ( s ;  '/  ' IH ) ']'") : nola_scope.
(** Interpretation for [T : type i (;ᵞ)] *)
Notation tintp s i T := ⟦ T ⟧{i}(s, hwf; λ k ki, tintp_lt s i (iM:=ki))
  (only parsing).
Notation "⟦ T ⟧{ i } ( s )" := (tintp s i T) (only parsing) : nola_scope.
Notation "⟦ T ⟧ ( s )" := ⟦ T ⟧{_}(s) (format "'[' ⟦  T  ⟧ '/  ' ( s ) ']'")
  : nola_scope.

(** Utility *)
Notation tinv_wsat_lt_f s M M' f :=
  (tinv_wsat' M (λ i iM, tintp_lt s M' (iM:=f i iM))) (only parsing).
Notation tinv_wsat_lt s M M' := (tinv_wsat' M (λ i iM, tintp_lt s M')).
Notation tinv_wsat s M := (tinv_wsat' M (λ i _ T, ⟦ T ⟧{i}(s))).
Notation tninv_wsat s i := (ninv_wsat (tinvd_intp (λ T, ⟦ T ⟧{i}(s)))).

(** ** Lemmas on [⟦ ⟧] etc. *)
Section tintp.
  Context (* Iris resources *) `{!tintpGS L Σ}.

  (** [tintp] etc. are persistent *)
  #[export] Instance tintp'_persistent
    {s i Γ T H un gn v} `{IHP : !∀ k ki T v, Persistent (IH k ki T v)} :
    Persistent (tintp' s (i:=i) (Γ:=Γ) T H IH un gn v).
  Proof.
    move: i Γ T H un gn v IH IHP. fix FIX 4=> i Γ T H.
    case: T H=>//=; intros; case H=>/= ?; try exact _; by apply (seqnil s0).
  Qed.
  #[export] Instance tintp_lt_persisent `{iM : ! i <ⁿ M} {s T v} :
    Persistent (tintp_lt s M T v).
  Proof.
    move: M i iM T v. elim=>/= >; [apply nlt_no0|apply tintp'_persistent].
  Qed.
  #[export] Instance tintp_persistent {s i T v} : Persistent (⟦ T ⟧{i}(s) v).
  Proof. exact _. Qed.

  (** [tintp'] is proper over [IH] *)
  Lemma tintp'_eq {s i Γ T H IH IH' un gn v} :
    (∀ k ki T v, IH k ki T v ⊣⊢ IH' k ki T v) →
    tintp' s T H IH un gn v ⊣⊢ tintp' s (i:=i) (Γ:=Γ) T H IH' un gn v.
  Proof.
    move: i Γ T H un gn v IH IH'. fix FIX 4=> i Γ T H.
    case: T H=>//=; intros; case H=>//= ?; try (f_equiv=> >; by apply FIX);
      try by apply FIX.
    do 3 f_equiv=> >; [by apply FIX|].
    apply twpw_proper=> >; by [f_equiv=> >|apply FIX].
  Qed.
  (** Equality between [tintp_lt]s *)
  Lemma tintp_lt_eq `{iM : ! i <ⁿ M, iM' : ! i <ⁿ M'} {s T v} :
    tintp_lt s M T v ⊣⊢ tintp_lt s M' T v.
  Proof.
    move: M M' i iM iM' T v. fix FIX 1=> M M'.
    case: M M'=> [|M][|M']/= i ?? T v; try apply nlt_no0.
    apply tintp'_eq=> >. apply FIX.
  Qed.
  (** [tintp_lt] into [tintp] *)
  Lemma tintp_lt_tintp `{iM : ! i <ⁿ M} {s T v} :
    tintp_lt s M T v ⊣⊢ ⟦ T ⟧(s) v.
  Proof.
    case: M iM; try (unfold nlt; lia). move=> ??.
    apply tintp'_eq=> >. exact tintp_lt_eq.
  Qed.

  (** Simplify [tintp'] over [↑ᵗ] *)
  Lemma tintp'_tbump `{ij : ! i ≤ⁿ j} {s Γ T H IH IH' un gn v} :
    (∀ k kj ki T v, IH k kj T v ⊣⊢ IH' k ki T v) →
    tintp' s (↑ᵗ{ij} T) H IH un gn v ⊣⊢ tintp' s (Γ:=Γ) T hwf IH' un gn v.
  Proof.
    move: i Γ T ij H un gn v IH IH'. fix FIX 5=> i Γ T ij H.
    case: T ij H=>//=; intros; subst; case H=>//= he;
      try (by apply (seqnil s0)); try (f_equiv=> >; by apply FIX);
      try (f_equiv=> ?; rewrite rew_eq_hwf; move: tsubst'_thgt;
        rewrite /tsubst'/= tsubstlu_tbump=> ?; by apply FIX).
    - do 3 f_equiv=> >; [by apply FIX|].
      apply twpw_proper=> >; by [f_equiv=> >|apply FIX].
    - rewrite rew_eq_hwf. move: tbump_thgt. rewrite -tbump_tbump=> ?.
      by apply FIX.
  Qed.
  (** Simplify [tintp] over [↑ᵗ] *)
  Lemma tintp_tbump `{ij : ! i ≤ⁿ j} {s T v} : ⟦ ↑ᵗ{ij} T ⟧(s) v ⊣⊢ ⟦ T ⟧(s) v.
  Proof. apply tintp'_tbump=> >. exact tintp_lt_eq. Qed.

  (** Simplify [tinv_wsat_lt] into [tinv_wsat] *)
  Lemma tinv_wsat_lt_tinv_wsat {s M M' f} :
    tinv_wsat_lt_f s M M' f ⊣⊢ tinv_wsat s M.
  Proof. f_equiv=> >. exact tintp_lt_tintp. Qed.
  Lemma twpw_tinv_wsat_lt_tinv_wsat {s M M' f e Φ} :
    WP[tinv_wsat_lt_f s M M' f] e [{ Φ }] ⊣⊢ WP[tinv_wsat s M] e [{ Φ }].
  Proof. apply twpw_proper; [exact tinv_wsat_lt_tinv_wsat|done]. Qed.

  (** Take out [tninv_wsat] out of [tinv_wsat] *)
  Lemma tinv_wsat_tninv_wsat `{! i <ⁿ M, ! i <ⁿ L} {s} :
    tinv_wsat s M -∗ tninv_wsat s i ∗ (tninv_wsat s i -∗ tinv_wsat s M).
  Proof. iIntros "tw". iApply (tinv_wsat'_ninv_wsat with "tw"). Qed.

  (** Inclusion between [tinv_wsat]s *)
  Lemma tinv_wsat_incl `{! M ≤ⁿ M'} {s} :
    tinv_wsat s M' -∗ tinv_wsat s M ∗ (tinv_wsat s M -∗ tinv_wsat s M').
  Proof. by apply tinv_wsat'_incl. Qed.

  (** Get inequality out of [tinv_wsat] *)
  Lemma fupdw_tinv_wsat_le {s M E E' P} :
    (⌜M ≤ⁿ L⌝ =[tinv_wsat s M]{E,E'}=∗ P) =[tinv_wsat s M]{E,E'}=∗ P.
  Proof. exact fupdw_tinv_wsat'_le. Qed.
End tintp.
