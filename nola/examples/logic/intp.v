(** * [nintp]: Interpretation of [nProp] as [iProp] *)

From nola.examples.logic Require Export subst iris.
Import EqNotations.

(** Modification of [nsubst] *)
Definition nsubst' {κ V Γᵘ Γᵍ} (P : nProp κ (V :: Γᵘ;ᵞ Γᵍ))
  (un : Γᵘ = []) (gn : Γᵍ = []) : nPred V → nProp κ (;ᵞ) :=
  nsubst (rew ctxeq_ug (f_equal (_ ::.) un) gn in P).
Arguments nsubst' {_ _ _ _} _ _ _ /.

(** [nsubst'] preserves [nhgt] *)
Lemma nsubst'_nhgt {κ V Γᵘ Γᵍ} {P : nProp κ (V :: Γᵘ;ᵞ Γᵍ)} {un gn Φ} :
  nhgt (nsubst' P un gn Φ) = nhgt P.
Proof. subst. apply nsubst_nhgt. Qed.

(** ** [nintp]: Interpretation of [nProp] as [iProp] *)

Section ncintp.
  Context (* Iris resources *) `{!nintpGS Σ}.

  (** Interpret basic connectives *)
  Definition ncintp0 (c : ncon0) : iProp Σ :=
    match c with
    | ⟨⌜φ⌝⟩ => ⌜φ⌝
    | nc_na_own p E => na_own p E | nc_cinv_own γ q => cinv_own γ q
    | ⟨↦{dq}|l,v⟩ => l ↦{dq} v | ⟨↦_J|l,v⟩ => l ↦_J v | ⟨↦□_J|l⟩ => l ↦_J □
    | nc_meta_token l E => meta_token l E
    | nc_steps_lb n => steps_lb n | nc_proph p pvs => proph p pvs
    end.
  Definition ncintpl0 (c : nconl0) (niS : nPropS (;ᵞ) -d> iProp Σ) : iProp Σ :=
    match c with nc_inv_wsat => ninv_wsat' niS end.
  Definition ncintp1 (c : ncon1) (P : iProp Σ) : iProp Σ :=
    match c with
    | ⟨◇⟩ => ◇ P | ⟨□⟩ => □ P | ⟨■⟩ => ■ P
    | ⟨|==>⟩ => |==> P | ⟨|={E,E'}=>⟩ => |={E,E'}=> P
    end.
  Definition ncintp2 (c : ncon2) (P Q : iProp Σ) : iProp Σ :=
    match c with
    | ⟨∧⟩ => P ∧ Q | ⟨∨⟩ => P ∨ Q | ⟨→⟩ => P → Q | ⟨∗⟩ => P ∗ Q | ⟨-∗⟩ => P -∗ Q
    | ⟨|=[]=>⟩ => |=[P]=> Q | ⟨|=[]{E,E'}=>⟩ => |=[P]{E,E'}=> Q
    end.
  Definition ncintpg1 (c : ncong1) (P : nPropL (;ᵞ))
    (ni : nderiv_ty Σ -d> discrete_fun (λ κ, nProp κ (;ᵞ) -d> iProp Σ))
    : nderiv_ty Σ -d> iProp Σ :=
    λ d, match c with
    | ⟨▷⟩ => ▷ ni d _ P
    | ⟨○⟩ => ⸨ P ⸩(d)
    | nc_ag γ => nag γ P
    | nc_inv N => nninv d N P | nc_na_inv p N => na_nninv d p N P
    end%I.

  (** [ncintp] is non-expansive *)
  #[export] Instance ncintpl0_ne {c} : NonExpansive (ncintpl0 c).
  Proof. solve_proper. Qed.
  #[export] Instance ncintp1_ne {c} : NonExpansive (ncintp1 c).
  Proof. solve_proper. Qed.
  #[export] Instance ncintp2_ne {c} : NonExpansive2 (ncintp2 c).
  Proof. solve_proper. Qed.

  (** [ncintpg] is contractive *)
  #[export] Instance ncintpg1_contr {c P} : Contractive (ncintpg1 c P).
  Proof. case c=>//= ??? leq d/=. f_contractive. apply (leq d _ _). Qed.

  (** [ncintp] is proper *)
  #[export] Instance ncintp1_proper : Proper ((=) ==> (≡) ==> (≡)) ncintp1.
  Proof. solve_proper. Qed.
  #[export] Instance ncintp2_proper :
    Proper ((=) ==> (≡) ==> (≡) ==> (≡)) ncintp2.
  Proof. solve_proper. Qed.
End ncintp.

Section nintp_gen.
  Context
    (* Iris resources *) `{!nintpGS Σ}
    (* Interpretation used contractively *)
    (ni : nderiv_ty Σ → ∀ κ, nProp κ (;ᵞ) → iProp Σ)
    (* Derivability *) (d : nderiv_ty Σ).

  (** [nintpS_gen P] : Evaluate small [P] *)
  Fixpoint nintpS_gen {κ Γ} (P : nProp κ Γ) (H : hAcc (nhgt P))
    : κ = nS → Γ.ᵞu = [] → Γ.ᵞg = [] → iProp Σ :=
    match P, H with
    | n_0 c, _ => λ _ _ _, ncintp0 c
    | n_1 c P, _ => λ κS un gn, ncintp1 c (nintpS_gen P (H ‼ʰ 0) κS un gn)
    | n_2 c P Q, _ => λ κS un gn, ncintp2 c
        (nintpS_gen P (H ‼ʰ 0) κS un gn) (nintpS_gen Q (H ‼ʰ 1) κS un gn)
    | n_g1 c P, _ => λ _ un gn, ncintpg1 c (rew eq_nil_ug_g un gn in P) ni d
    | (∀' Φ)%n, _ => λ κS un gn, ∀ a, nintpS_gen (Φ a) (H ‼ʰ a) κS un gn
    | (∃' Φ)%n, _ => λ κS un gn, ∃ a, nintpS_gen (Φ a) (H ‼ʰ a) κS un gn
    | n_wpw W d E e Φ, _ => λ κS un gn, wpw (nintpS_gen W (H ‼ʰ 0) κS un gn)
        d E e (λ v, nintpS_gen (Φ v) (H ‼ʰ 1 ‼ʰ v) κS un gn)
    | n_twpw W d E e Φ, _ => λ κS un gn, twpw (nintpS_gen W (H ‼ʰ 0) κS un gn)
        d E e (λ v, nintpS_gen (Φ v) (H ‼ʰ 1 ‼ʰ v) κS un gn)
    | (∀: V, P)%n, _ => λ κS un gn, ∀ Φ, nintpS_gen
        (nsubst' P un gn Φ) (H ‼ʰ[nsubst'_nhgt] 0) κS eq_refl eq_refl
    | (∃: V, P)%n, _ => λ κS un gn, ∃ Φ, nintpS_gen
        (nsubst' P un gn Φ) (H ‼ʰ[nsubst'_nhgt] 0) κS eq_refl eq_refl
    | (rec:ˢ' Φ a)%n, _ => λ _ un gn, nintpS_gen
        (nsubst' (Φ a) un gn (rew[λ _,_] ctxeq_ug un gn in rec:ˢ' Φ)%n)
        (H ‼ʰ[nsubst'_nhgt] 0) eq_refl eq_refl eq_refl
    | (%ᵍˢ s)%n, _ => λ _ _, seqnil s
    | (¢ᵘ _)%n, _ => λ _ (un : _::_ = _), match un with end
    | (¢ᵍ _)%n, _ => λ _ _ (gn : _::_ = _), match gn with end
    | n_l0 _, _ | (rec:ˡ' _ _)%n, _ | (%ᵍˡ _)%n, _ | (%ᵘˢ _)%n, _ | (!ᵘˢ _)%n, _
      => λ κS, match κS with end
    end%I.
  Local Notation nintpS P := (nintpS_gen P hwf eq_refl eq_refl eq_refl).

  (** [nintp_gen P] : Evaluate [P] *)
  Fixpoint nintp_gen {κ Γ} (P : nProp κ Γ) (H : hAcc (nhgt P))
    : Γ.ᵞu = [] → Γ.ᵞg = [] → iProp Σ :=
    match P, H with
    | n_0 c, _ => λ _ _, ncintp0 c
    | n_l0 c, _ => λ _ _, ncintpl0 c (λ P, nintpS P)
    | n_1 c P, _ => λ un gn, ncintp1 c (nintp_gen P (H ‼ʰ 0) un gn)
    | n_2 c P Q, _ => λ un gn, ncintp2 c
        (nintp_gen P (H ‼ʰ 0) un gn) (nintp_gen Q (H ‼ʰ 1) un gn)
    | n_g1 c P, _ => λ un gn, ncintpg1 c (rew eq_nil_ug_g un gn in P) ni d
    | (∀' Φ)%n, _ => λ un gn, ∀ a, nintp_gen (Φ a) (H ‼ʰ a) un gn
    | (∃' Φ)%n, _ => λ un gn, ∃ a, nintp_gen (Φ a) (H ‼ʰ a) un gn
    | n_wpw W d E e Φ, _ => λ un gn, wpw (nintp_gen W (H ‼ʰ 0) un gn)
        d E e (λ v, nintp_gen (Φ v) (H ‼ʰ 1 ‼ʰ v) un gn)
    | n_twpw W d E e Φ, _ => λ un gn, twpw (nintp_gen W (H ‼ʰ 0) un gn)
        d E e (λ v, nintp_gen (Φ v) (H ‼ʰ 1 ‼ʰ v) un gn)
    | (∀: V, P)%n, _ => λ un gn, ∀ Φ,
        nintp_gen (nsubst' P un gn Φ) (H ‼ʰ[nsubst'_nhgt] 0) eq_refl eq_refl
    | (∃: V, P)%n, _ => λ un gn, ∃ Φ,
        nintp_gen (nsubst' P un gn Φ) (H ‼ʰ[nsubst'_nhgt] 0) eq_refl eq_refl
    | (rec:ˢ' Φ a)%n, _ => λ un gn, nintp_gen
        (nsubst' (Φ a) un gn (rew[λ _,_] ctxeq_ug un gn in rec:ˢ' Φ)%n)
        (H ‼ʰ[nsubst'_nhgt] 0) eq_refl eq_refl
    | (rec:ˡ' Φ a)%n, _ => λ un gn, nintp_gen
        (nsubst' (Φ a) un gn (rew[λ _,_] ctxeq_ug un gn in rec:ˡ' Φ)%n)
        (H ‼ʰ[nsubst'_nhgt] 0) eq_refl eq_refl
    | (¢ᵘ _)%n, _ => λ un : _::_ = _, match un with end
    | (¢ᵍ _)%n, _ => λ _ (gn : _::_ = _), match gn with end
    | (%ᵍˢ s)%n, _ | (%ᵍˡ s)%n, _ => λ _, seqnil s | (%ᵘˢ s)%n, _ => seqnil s
    | (!ᵘˢ P)%n, _ => λ _ _, nintpS P
    end%I.
End nintp_gen.

Section nintp.
  Context (* Iris resources *) `{!nintpGS Σ}.

  (** [nintpS_gen]/[nintp_gen] typed as a discrete function *)
  Definition nintpS_gen' : (_ -d> _ -d> _ -d> iProp Σ) ->
    _ -d> _ -d> _ -d> _ -d> _ -d> _ -d> _ -d> _ -d> iProp Σ :=
    λ ni d κ Γ (P : nProp κ Γ), nintpS_gen ni d P.
  Definition nintp_gen' : (_ -d> _ -d> _ -d> iProp Σ) ->
    _ -d> _ -d> _ -d> _ -d> _ -d> _ -d> _ -d> iProp Σ :=
    λ ni d κ Γ (P : nProp κ Γ), nintp_gen ni d P.

  (** [nintpS_gen] is contractive *)
  #[export] Instance nintpS_gen_contractive : Contractive nintpS_gen'.
  Proof.
    unfold nintpS_gen'=> i ni ni' nInvd d + + + + + + +. fix FIX 4=> κ Γ P H.
    case: P H=>/=; intros; case H=>//= ?; try (by f_equiv=> >; apply FIX);
    try (by apply ncintpg1_contr; apply nInvd);
    [apply wpw_ne=> >|apply twpw_ne=> >]; by apply FIX.
  Qed.

  (** [nintp_gen] is contractive *)
  #[export] Instance nintp_gen_contractive : Contractive nintp_gen'.
  Proof.
    unfold nintp_gen'=> i ni ni' nInvd d + + + + + +. fix FIX 4=> κ Γ P H.
    case: P H=>/=; intros; case H=>//= ?; try (by f_equiv=> >; apply FIX);
      try (by apply ncintpg1_contr; apply nInvd);
      try (by try (f_equiv=> ?); apply nintpS_gen_contractive);
      [apply wpw_ne=> >|apply twpw_ne=> >]; by apply FIX.
  Qed.

  (** [nintp_pre]: Generator of [nintp_fp] *)
  Definition nintp_pre
    : (_ -d> _ -d> _ -d> iProp Σ) -> (_ -d> _ -d> _ -d> iProp Σ)
    := λ ni d κ (P : nProp κ (;ᵞ)), nintp_gen' ni d _ _ P hwf eq_refl eq_refl.
  #[export] Instance nintp_pre_contractive : Contractive nintp_pre.
  Proof. move=> ???????. by apply nintp_gen_contractive. Qed.

  (** [nintp_fp]: Fixpoint interpretation of [nProp κ (;ᵞ)] *)
  Definition nintp_fp : _ → ∀ κ, nProp κ (;ᵞ) → iProp Σ := fixpoint nintp_pre.
End nintp.

(** Notations, which will be printed in (partial) interpretation, yay! *)

Notation "⟦ P ⟧ᶠ ( d )" := (nintp_fp d _ P)
  (format "'[' ⟦  P  ⟧ᶠ '/  ' ( d ) ']'") : nola_scope.

Notation "⟦ P ⟧{ κ } ( d , H )" :=
  (@nintp_gen _ _ nintp_fp d κ (;ᵞ) P H eq_refl eq_refl) (only parsing)
  : nola_scope.
Notation "⟦ P ⟧{ κ } ( d )" := (⟦ P ⟧{κ}(d, hwf)) (only parsing) : nola_scope.
Notation "⟦ P ⟧ ( d , H )" := ⟦ P ⟧{_}(d, H)
  (format "'[' ⟦  P  ⟧ '/  ' ( d ,  H ) ']'") : nola_scope.
Notation "⟦ P ⟧ ( d )" := ⟦ P ⟧(d, hwf)
  (format "'[' ⟦  P  ⟧ '/  ' ( d ) ']'") : nola_scope.
Notation nintp d P := ⟦ P ⟧(d) (only parsing).

Notation "⟦ P ⟧ˢ ( d , H )" :=
  (@nintpS_gen _ _ nintp_fp d nS (;ᵞ) P H eq_refl eq_refl eq_refl)
  (format "'[' ⟦  P  ⟧ˢ '/  ' ( d ,  H ) ']'") : nola_scope.
Notation "⟦ P ⟧ˢ ( d )" := ⟦ P ⟧ˢ(d, hwf)
  (format "'[' ⟦  P  ⟧ˢ '/  ' ( d ) ']'") : nola_scope.
Notation nintpS d P := ⟦ P ⟧ˢ(d) (only parsing).

(** Utility *)
Notation nninv_wsat d := (ninv_wsat' (λ P, ⟦ P ⟧ˢ(d))).

(** ** Lemmas on [⟦ ⟧] etc. *)
Section nintp.
  Context (* Iris resources *) `{!nintpGS Σ}.

  (** [⟦ ⟧ᶠ] coincides with [⟦ ⟧] *)
  Lemma nintp_fp_nintp {d κ P} : ⟦ P ⟧ᶠ(d) ⊣⊢ ⟦ P ⟧{κ}(d).
  Proof. unfold nintp_fp. apply (fixpoint_unfold nintp_pre). Qed.

  (** [nintpS_gen] coincides with [nintp_gen] *)
  Lemma nintpS_gen_nintp_gen {ni d κ Γ} {P : nProp κ Γ} {H κS un gn} :
    nintpS_gen ni d P H κS un gn ⊣⊢ nintp_gen ni d P H un gn.
  Proof.
    move: κ Γ P H κS un gn. fix FIX 4=> κ Γ P H.
    case: P H; intros; case H=>//= ?; try apply wpw_proper=> >;
      try apply twpw_proper=> >; try f_equiv=> >; apply FIX.
  Qed.
  (** [⟦ ⟧ˢ] coincides with [⟦ ⟧] *)
  Lemma nintpS_nintp {d P} : ⟦ P ⟧ˢ(d) ⊣⊢ ⟦ P ⟧(d).
  Proof. exact nintpS_gen_nintp_gen. Qed.

  (** Simplify [nintp_gen] over [↑ˡ] *)
  Lemma nintp_gen_nlarge {ni d κ Γ} {P : nProp κ Γ} {H un gn} :
    nintp_gen ni d (↑ˡ P) H un gn ⊣⊢ nintp_gen ni d P hwf un gn.
  Proof.
    move: κ Γ P H un gn. fix FIX 4=> κ Γ P H.
    case: P H=>//=; intros; case H=>/= he; try apply wpw_proper=> >;
      try apply twpw_proper=> >; try f_equiv=> >; try apply FIX;
      try apply leibniz_equiv_iff, proof_irrel;
      rewrite rew_eq_hwf; move: nsubst'_nhgt=>/=; subst;
      rewrite (nsubstlu_nlarge (P:=P))=> ?; apply FIX.
  Qed.
  (** Simplify [⟦ ⟧] over [↑ˡ] *)
  Lemma nintp_nlarge {d κ P} : ⟦ ↑ˡ P ⟧(d) ⊣⊢ ⟦ P ⟧{κ}(d).
  Proof. exact nintp_gen_nlarge. Qed.
  (** [⟦ ⟧ˢ] coincides with [⟦ ⟧] over [↑ˡ] *)
  Lemma nintpS_nintp_nlarge {d P} : ⟦ P ⟧ˢ(d) ⊣⊢ ⟦ ↑ˡ P ⟧(d).
  Proof. by rewrite nintpS_nintp nintp_nlarge. Qed.
End nintp.
