(** * [nintp]: Interpretation of [nProp] as [iProp] *)

From nola.examples.logic Require Export subst iris.
Import EqNotations.

(** Modification of [nsubst] *)
Local Definition nsubst' {κ V Γᵘ Γᵍ} (P : nProp κ (V :: Γᵘ;ᵞ Γᵍ))
  (un : Γᵘ = []) (gn : Γᵍ = []) : nPred V → nProp κ (;ᵞ) :=
  nsubst (rew ctxeq_ug (f_equal (_ ::.) un) gn in P).
Arguments nsubst' {_ _ _ _} _ _ _ /.

(** [nsubst'] preserves [nhgt] *)
Local Lemma nsubst'_nhgt {κ V Γᵘ Γᵍ} {P : nProp κ (V :: Γᵘ;ᵞ Γᵍ)} {un gn Φ} :
  nhgt (nsubst' P un gn Φ) = nhgt P.
Proof. subst. apply nsubst_nhgt. Qed.

(** ** [nintp]: Interpretation of [nProp] as [iProp] *)

Section nintp.
  Context (* Iris resources *) `{!nintpGS Σ}.

  (** Interpret basic connectives *)
  Local Definition ncintp0 (c : ncon0) : iProp Σ :=
    match c with
    | nc_pure φ => ⌜φ⌝
    | nc_na_own p E => na_own p E | nc_cinv_own γ q => cinv_own γ q
    | nc_mapsto l dq v => l ↦{dq} v
    | nc_inv_mapsto_own l v J => l ↦_J v | nc_inv_mapsto l J => l ↦_J □
    | nc_meta_token l E => meta_token l E
    | nc_steps_lb n => steps_lb n | nc_proph p pvs => proph p pvs
    | nc_lft_tok α q => q.[α] | nc_lft_dead α => [†α] | nc_lft_eter α => [∞α]
    | nc_lft_sincl α β => α ⊑□ β
    | nc_proph_tok ξ q => q:[ξ] | nc_proph_toks ξl q => q:∗[ξl]
    | nc_proph_obs φπ => .⟨φπ⟩ | nc_proph_wsat => proph_wsat
    | nc_val_obs γ X x => val_obs γ X x
    | nc_proph_ctrl γ X x ξ => proph_ctrl γ X x ξ
    end.
  Local Definition ncintpl0 (c : nconl0)
    (niS : nPropS (;ᵞ) -d> iProp Σ) : iProp Σ :=
    match c with
    | nc_sinv_wsat => sinv_wsat niS
    | nc_inv_wsat => inv_wsat niS | nc_na_inv_wsat => na_inv_wsat niS
    | nc_borrow_wsat => borrow_wsat'' niS
    end.
  Local Definition ncintp1 (c : ncon1) (P : iProp Σ) : iProp Σ :=
    match c with
    | nc_except_0 => ◇ P | nc_persistently => □ P | nc_plainly => ■ P
    | nc_bupd => |==> P | nc_fupd E E' => |={E,E'}=> P
    end.
  Local Definition ncintp2 (c : ncon2) (P Q : iProp Σ) : iProp Σ :=
    match c with
    | nc_and => P ∧ Q | nc_or => P ∨ Q | nc_impl => P → Q
    | nc_sep => P ∗ Q | nc_wand => P -∗ Q
    | nc_bupdw => |=[P]=> Q | nc_fupdw E E' => |=[P]{E,E'}=> Q
    end.
  Local Definition ncintpwpw (c : nconwpw) (W : iProp Σ) (Φ : val -d> iProp Σ)
    : iProp Σ := match c with
    | nc_wpw s E e => wpw W s E e Φ | nc_twpw s E e => twpw W s E e Φ
    end.
  Local Definition ncintpg1 (c : ncong1) (P : nPropL (;ᵞ))
    (ni : nderiv_ty Σ -d> discrete_fun (λ κ, nProp κ (;ᵞ) -d> iProp Σ))
    : nderiv_ty Σ -d> iProp Σ :=
    λ δ, match c with
    | nc_later => ▷ ni δ _ P
    | nc_indir => ⸨ P ⸩(δ)
    | nc_sinv => sinv δ P
    | nc_inv N => ninv δ N P | nc_na_inv p N => na_ninv δ p N P
    | nc_borc α => borc δ α P | nc_bor α => bor δ α P
    | nc_obor α q => obor δ α q P | nc_lend α => lend δ α P
    end%I.
  Local Definition ncintpg1f (c : ncong1f) (Φ : Qp → nPropL (;ᵞ))
    (ni : nderiv_ty Σ -d> discrete_fun (λ κ, nProp κ (;ᵞ) -d> iProp Σ))
    : nderiv_ty Σ -d> iProp Σ :=
    λ δ, match c with nc_fbor α => fbor δ α Φ end.

  (** [ncintp] is non-expansive *)
  Local Instance ncintpl0_ne {c} : NonExpansive (ncintpl0 c).
  Proof. solve_proper. Qed.
  Local Instance ncintp1_ne {c} : NonExpansive (ncintp1 c).
  Proof. solve_proper. Qed.
  Local Instance ncintp2_ne {c} : NonExpansive2 (ncintp2 c).
  Proof. solve_proper. Qed.
  Local Instance ncintpwpw_ne {c} : NonExpansive2 (ncintpwpw c).
  Proof. move=> ???????. case c=> >; by [apply wpw_ne|apply twpw_ne]. Qed.

  (** [ncintpg] is contractive *)
  Local Instance ncintpg1_contr {c P} : Contractive (ncintpg1 c P).
  Proof. case c=>//= ??? leq δ/=. f_contractive. apply (leq δ _ _). Qed.
  Local Instance ncintpg1f_contr {c Φ} : Contractive (ncintpg1f c Φ).
  Proof. by case c. Qed.

  (** [ncintp] is proper *)
  Local Instance ncintp1_proper : Proper ((=) ==> (≡) ==> (≡)) ncintp1.
  Proof. solve_proper. Qed.
  Local Instance ncintp2_proper :
    Proper ((=) ==> (≡) ==> (≡) ==> (≡)) ncintp2.
  Proof. solve_proper. Qed.
  Local Instance ncintpwpw_proper :
    Proper ((=) ==> (≡) ==> (≡) ==> (≡)) ncintpwpw.
  Proof.
    move=> c ?<-??????. case c=> >; by [apply wpw_proper|apply twpw_proper].
  Qed.

  Section nintp.
    Context
      (* Interpretation used contractively *)
      (ni : nderiv_ty Σ → ∀ κ, nProp κ (;ᵞ) → iProp Σ)
      (* Derivability *) (δ : nderiv_ty Σ).

    (** [nintpS_gen P] : Evaluate small [P] *)
    Fixpoint nintpS_gen {κ Γ} (P : nProp κ Γ) (H : hAcc (nhgt P))
      : κ = nS → Γ.ᵞu = [] → Γ.ᵞg = [] → iProp Σ :=
      match P, H with
      | n_0 c, _ => λ _ _ _, ncintp0 c
      | n_1 c P, _ => λ κS un gn, ncintp1 c (nintpS_gen P (H ‼ʰ 0) κS un gn)
      | n_2 c P Q, _ => λ κS un gn, ncintp2 c
          (nintpS_gen P (H ‼ʰ 0) κS un gn) (nintpS_gen Q (H ‼ʰ 1) κS un gn)
      | n_cwpw c W Φ, _ => λ κS un gn, ncintpwpw c
          (nintpS_gen W (H ‼ʰ 0) κS un gn)
          (λ v, nintpS_gen (Φ v) (H ‼ʰ 1 ‼ʰ v) κS un gn)
      | n_g1 c P, _ => λ _ un gn, ncintpg1 c (rew eq_nil_ug_g un gn in P) ni δ
      | n_g1f c Φ, _ => λ _ un gn,
          ncintpg1f c (λ q, rew eq_nil_ug_g un gn in Φ q) ni δ
      | (∀' Φ)%n, _ => λ κS un gn, ∀ a, nintpS_gen (Φ a) (H ‼ʰ a) κS un gn
      | (∃' Φ)%n, _ => λ κS un gn, ∃ a, nintpS_gen (Φ a) (H ‼ʰ a) κS un gn
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
      | n_l0 _, _ | (rec:ˡ' _ _)%n, _ | (%ᵍˡ _)%n, _ | (%ᵘˢ _)%n, _
        | (!ᵘˢ _)%n, _ => λ κS, match κS with end
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
      | n_cwpw c W Φ, _ => λ un gn, ncintpwpw c
          (nintp_gen W (H ‼ʰ 0) un gn)
          (λ v, nintp_gen (Φ v) (H ‼ʰ 1 ‼ʰ v) un gn)
      | n_g1 c P, _ => λ un gn, ncintpg1 c (rew eq_nil_ug_g un gn in P) ni δ
      | n_g1f c Φ, _ => λ un gn,
          ncintpg1f c (λ q, rew eq_nil_ug_g un gn in Φ q) ni δ
      | (∀' Φ)%n, _ => λ un gn, ∀ a, nintp_gen (Φ a) (H ‼ʰ a) un gn
      | (∃' Φ)%n, _ => λ un gn, ∃ a, nintp_gen (Φ a) (H ‼ʰ a) un gn
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
  End nintp.

  (** [nintpS_gen]/[nintp_gen] typed as a discrete function *)
  Definition nintpS_gen' : (_ -d> _ -d> _ -d> iProp Σ) ->
    _ -d> _ -d> _ -d> _ -d> _ -d> _ -d> _ -d> _ -d> iProp Σ :=
    λ ni δ κ Γ (P : nProp κ Γ), nintpS_gen ni δ P.
  Definition nintp_gen' : (_ -d> _ -d> _ -d> iProp Σ) ->
    _ -d> _ -d> _ -d> _ -d> _ -d> _ -d> _ -d> iProp Σ :=
    λ ni δ κ Γ (P : nProp κ Γ), nintp_gen ni δ P.

  (** [nintpS_gen] is contractive *)
  #[export] Instance nintpS_gen_contractive : Contractive nintpS_gen'.
  Proof.
    unfold nintpS_gen'=> i ni ni' nid δ + + + + + + +. fix FIX 4=> κ Γ P H.
    case: P H=>/=; intros; case H=>//= ?; try (by f_equiv=> >; apply FIX).
    by apply ncintpg1_contr.
  Qed.

  (** [nintp_gen] is contractive *)
  #[export] Instance nintp_gen_contractive : Contractive nintp_gen'.
  Proof.
    unfold nintp_gen'=> i ni ni' nInvd δ + + + + + +. fix FIX 4=> κ Γ P H.
    case: P H=>/=; intros; case H=>//= ?; try (by f_equiv=> >; apply FIX);
      try (by apply ncintpg1_contr);
      try (f_equiv=> ?); try (f_equiv; [apply FIX|]=> ?);
      by apply nintpS_gen_contractive.
  Qed.

  (** [nintp_pre]: Generator of [nintp_fp] *)
  Definition nintp_pre
    : (_ -d> _ -d> _ -d> iProp Σ) -> (_ -d> _ -d> _ -d> iProp Σ)
    := λ ni δ κ (P : nProp κ (;ᵞ)), nintp_gen' ni δ _ _ P hwf eq_refl eq_refl.
  #[export] Instance nintp_pre_contractive : Contractive nintp_pre.
  Proof. move=> ???????. by apply nintp_gen_contractive. Qed.

  (** [nintp_fp]: Fixpoint interpretation of [nProp κ (;ᵞ)] *)
  Definition nintp_fp : _ → ∀ κ, nProp κ (;ᵞ) → iProp Σ := fixpoint nintp_pre.
End nintp.

(** Notations, which will be printed in (partial) interpretation, yay! *)

Notation "⟦ P ⟧ᶠ ( δ )" := (nintp_fp δ _ P)
  (format "'[' ⟦  P  ⟧ᶠ '/  ' ( δ ) ']'") : nola_scope.

Notation "⟦ P ⟧{ κ } ( δ , H )" :=
  (@nintp_gen _ _ nintp_fp δ κ (;ᵞ) P H eq_refl eq_refl) (only parsing)
  : nola_scope.
Notation "⟦ P ⟧{ κ } ( δ )" := (⟦ P ⟧{κ}(δ, hwf)) (only parsing) : nola_scope.
Notation "⟦ P ⟧ ( δ , H )" := ⟦ P ⟧{_}(δ, H)
  (format "'[' ⟦  P  ⟧ '/  ' ( δ ,  H ) ']'") : nola_scope.
Notation "⟦ P ⟧ ( δ )" := ⟦ P ⟧(δ, hwf)
  (format "'[' ⟦  P  ⟧ '/  ' ( δ ) ']'") : nola_scope.
Notation nintp δ P := ⟦ P ⟧(δ) (only parsing).

Notation "⟦ P ⟧ˢ ( δ , H )" :=
  (@nintpS_gen _ _ nintp_fp δ nS (;ᵞ) P H eq_refl eq_refl eq_refl)
  (format "'[' ⟦  P  ⟧ˢ '/  ' ( δ ,  H ) ']'") : nola_scope.
Notation "⟦ P ⟧ˢ ( δ )" := ⟦ P ⟧ˢ(δ, hwf)
  (format "'[' ⟦  P  ⟧ˢ '/  ' ( δ ) ']'") : nola_scope.
Notation nintpS δ P := ⟦ P ⟧ˢ(δ) (only parsing).

(** Utility *)
Notation sinv_wsat' δ := (sinv_wsat (λ P, ⟦ P ⟧ˢ(δ))).
Notation inv_wsat' δ := (inv_wsat (λ P, ⟦ P ⟧ˢ(δ))).
Notation na_inv_wsat' δ := (na_inv_wsat (λ P, ⟦ P ⟧ˢ(δ))).
Notation borrow_wsat' δ := (borrow_wsat'' (λ P, ⟦ P ⟧ˢ(δ))).

(** ** Lemmas on [⟦ ⟧] etc. *)
Section nintp.
  Context (* Iris resources *) `{!nintpGS Σ}.
  Local Existing Instance ncintp1_proper.
  Local Existing Instance ncintp2_proper.
  Local Existing Instance ncintpwpw_proper.

  (** [⟦ ⟧ᶠ] coincides with [⟦ ⟧] *)
  Lemma nintp_fp_nintp {δ κ P} : ⟦ P ⟧ᶠ(δ) ⊣⊢ ⟦ P ⟧{κ}(δ).
  Proof. unfold nintp_fp. apply (fixpoint_unfold nintp_pre). Qed.

  (** [nintpS_gen] coincides with [nintp_gen] *)
  Local Lemma nintpS_gen_nintp_gen {ni δ κ Γ} {P : nProp κ Γ} {H κS un gn} :
    nintpS_gen ni δ P H κS un gn ⊣⊢ nintp_gen ni δ P H un gn.
  Proof.
    move: κ Γ P H κS un gn. fix FIX 4=> κ Γ P H.
    case: P H; intros; case H=>//= ?; try f_equiv=> >; apply FIX.
  Qed.
  (** [⟦ ⟧ˢ] coincides with [⟦ ⟧] *)
  Lemma nintpS_nintp {δ P} : ⟦ P ⟧ˢ(δ) ⊣⊢ ⟦ P ⟧(δ).
  Proof. exact nintpS_gen_nintp_gen. Qed.

  (** Simplify [nintp_gen] over [↑ˡ] *)
  Local Lemma nintp_gen_nlarge {ni δ κ Γ} {P : nProp κ Γ} {H un gn} :
    nintp_gen ni δ (↑ˡ P) H un gn ⊣⊢ nintp_gen ni δ P hwf un gn.
  Proof.
    move: κ Γ P H un gn. fix FIX 4=> κ Γ P H.
    case: P H=>//=; intros; case H=>/= he; try f_equiv=> >; try (by apply FIX);
      try (by apply leibniz_equiv_iff, proof_irrel);
      try (by f_equal; apply proof_irrel);
      rewrite rew_eq_hwf; move: nsubst'_nhgt=>/=; subst;
      rewrite (nsubstlu_nlarge (P:=P))=> ?; apply FIX.
  Qed.
  (** Simplify [⟦ ⟧] over [↑ˡ] *)
  Lemma nintp_nlarge {δ κ P} : ⟦ ↑ˡ P ⟧(δ) ⊣⊢ ⟦ P ⟧{κ}(δ).
  Proof. exact nintp_gen_nlarge. Qed.
  (** [⟦ ⟧ˢ] coincides with [⟦ ⟧] over [↑ˡ] *)
  Lemma nintpS_nintp_nlarge {δ P} : ⟦ P ⟧ˢ(δ) ⊣⊢ ⟦ ↑ˡ P ⟧(δ).
  Proof. by rewrite nintpS_nintp nintp_nlarge. Qed.
End nintp.
