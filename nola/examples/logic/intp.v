(** * [nintp]: Interpretation of [nProp] as [iProp] *)

From nola.examples.logic Require Export subst iris.
Import EqNotations.

(** Modification of [nsubst] *)
Definition nsubst' {κ Γᵘ Γᵍ V} (P : nProp κ (V :: Γᵘ;ᵞ Γᵍ))
  (un : Γᵘ = []) (gn : Γᵍ = []) : nPred V → nProp κ (;ᵞ) :=
  nsubst (rew ctxeq_ug (f_equal (_ ::.) un) gn in P).
Arguments nsubst' {_ _ _ _} _ _ _ /.

(** [nsubst'] preserves [nheight] *)
Lemma nsubst'_nheight {κ Γᵘ Γᵍ V} {P : nProp κ (V :: Γᵘ;ᵞ Γᵍ)} {un gn Φ} :
  nheight (nsubst' P un gn Φ) = nheight P.
Proof. subst. apply nsubst_nheight. Qed.

(** ** [nintp]: Interpretation of [nProp] as [iProp] *)

Section ncintp.
  Context (* Iris resources *) `{!nintpGS Σ}.

  (** Interpret basic connectives *)
  Definition ncintp0 (c : ncon0) : iProp Σ :=
    match c with
    | ⟨⌜φ⌝⟩%nc => ⌜φ⌝
    | ⟨↦{dq}|l,v⟩%nc => l ↦{dq} v
    | ⟨↦_J|l,v⟩%nc => l ↦_J v | ⟨↦□_J|l⟩%nc => l ↦_J □
    | nc_meta_token l E => meta_token l E
    | nc_steps_lb n => steps_lb n | nc_proph p pvs => proph p pvs
    end.
  Definition ncintpl0 (c : nconl0) (niS : nPropS (;ᵞ) → iProp Σ) : iProp Σ :=
    match c with nc_inv_wsat => ninv_wsat niS end.
  Definition ncintp1 (c : ncon1) (P : iProp Σ) : iProp Σ :=
    match c with
    | ⟨□⟩%nc => □ P | ⟨■⟩%nc => ■ P
    | ⟨|==>⟩%nc => |==> P | ⟨|={E,E'}=>⟩%nc => |={E,E'}=> P
    end.
  Definition ncintp2 (c : ncon2) (P Q : iProp Σ) : iProp Σ :=
    match c with
    | ⟨∧⟩%nc => P ∧ Q | ⟨∨⟩%nc => P ∨ Q | ⟨→⟩%nc => P → Q
    | ⟨∗⟩%nc => P ∗ Q | ⟨-∗⟩%nc => P -∗ Q
    end.
  Definition ncintpg1 (c : ncong1) (P : nPropL (;ᵞ))
    (ni : nsintp_ty Σ → ∀ κ, nProp κ (;ᵞ) → iProp Σ) (s : nsintp_ty Σ)
    : iProp Σ :=
    match c with
    | ⟨▷⟩%nc => ▷ ni s _ P
    | ⟨○(i)⟩%nc => ⸨ P ⸩(s,i)
    | nc_inv i N => nninv s i N P
    end.

  (** [ncintp] is non-expansive *)
  #[export] Instance ncintp1_ne {c} : NonExpansive (ncintp1 c).
  Proof. solve_proper. Qed.
  #[export] Instance ncintp2_ne {c} : NonExpansive2 (ncintp2 c).
  Proof. solve_proper. Qed.

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
    (ni : nsintp_ty Σ → ∀ κ, nProp κ (;ᵞ) → iProp Σ)
    (* Strong interpretation *) (s : nsintp_ty Σ).

  (** [nintpS_gen P] : Evaluate small [P] *)
  Fixpoint nintpS_gen {κ Γ} (P : nProp κ Γ) (H : hAcc (nheight P))
    : κ = nS → Γ.ᵞu = [] → Γ.ᵞg = [] → iProp Σ :=
    match P, H with
    | n_0 c, _ => λ _ _ _, ncintp0 c
    | n_1 c P, _ => λ κS un gn, ncintp1 c (nintpS_gen P (H ‼ʰ 0) κS un gn)
    | n_2 c P Q, _ => λ κS un gn, ncintp2 c
        (nintpS_gen P (H ‼ʰ 0) κS un gn) (nintpS_gen Q (H ‼ʰ 1) κS un gn)
    | n_g1 c P, _ => λ _ un gn, ncintpg1 c (rew app_eq_nil_ug_g un gn in P) ni s
    | (∀' Φ)%n, _ => λ κS un gn, ∀ a, nintpS_gen (Φ a) (H ‼ʰ a) κS un gn
    | (∃' Φ)%n, _ => λ κS un gn, ∃ a, nintpS_gen (Φ a) (H ‼ʰ a) κS un gn
    | (∀: V, P)%n, _ => λ κS un gn, ∀ Φ, nintpS_gen
        (nsubst' P un gn Φ) (H ‼ʰ[nsubst'_nheight] 0) κS eq_refl eq_refl
    | (∃: V, P)%n, _ => λ κS un gn, ∃ Φ, nintpS_gen
        (nsubst' P un gn Φ) (H ‼ʰ[nsubst'_nheight] 0) κS eq_refl eq_refl
    | (rec:ˢ' Φ a)%n, _ => λ _ un gn, nintpS_gen
        (nsubst' (Φ a) un gn (rew[λ _,_] ctxeq_ug un gn in rec:ˢ' Φ)%n)
        (H ‼ʰ[nsubst'_nheight] 0) eq_refl eq_refl eq_refl
    | (%ᵍˢ s)%n, _ => λ _ _, seqnil s
    | n_l0 _, _ | n_wp _ _ _ _, _ | n_twp _ _ _ _, _ | (rec:ˡ' _ _)%n, _
    | (%ᵍˡ _)%n, _ | (%ᵘˢ _)%n, _ | (!ᵘˢ _)%n, _
      => λ κS, match κS with end
    end%I.
  Local Notation nintpS P := (nintpS_gen P hwf eq_refl eq_refl eq_refl).

  (** [nintp_gen P] : Evaluate [P] *)
  Fixpoint nintp_gen {κ Γ} (P : nProp κ Γ) (H : hAcc (nheight P))
    : Γ.ᵞu = [] → Γ.ᵞg = [] → iProp Σ :=
    match P, H with
    | n_0 c, _ => λ _ _, ncintp0 c
    | n_l0 c, _ => λ _ _, ncintpl0 c (λ P, nintpS P)
    | n_1 c P, _ => λ un gn, ncintp1 c (nintp_gen P (H ‼ʰ 0) un gn)
    | n_2 c P Q, _ => λ un gn, ncintp2 c
        (nintp_gen P (H ‼ʰ 0) un gn) (nintp_gen Q (H ‼ʰ 1) un gn)
    | n_g1 c P, _ => λ un gn, ncintpg1 c (rew app_eq_nil_ug_g un gn in P) ni s
    | (∀' Φ)%n, _ => λ un gn, ∀ a, nintp_gen (Φ a) (H ‼ʰ a) un gn
    | (∃' Φ)%n, _ => λ un gn, ∃ a, nintp_gen (Φ a) (H ‼ʰ a) un gn
    | n_wp s E e Φ, _ => λ un gn, wpw (ninv_wsat (λ P, nintpS P))
        s E e (λ v, nintp_gen (Φ v) (H ‼ʰ v) un gn)
    | n_twp s E e Φ, _ => λ un gn, twpw (ninv_wsat (λ P, nintpS P))
        s E e (λ v, nintp_gen (Φ v) (H ‼ʰ v) un gn)
    | (∀: V, P)%n, _ => λ un gn, ∀ Φ,
        nintp_gen (nsubst' P un gn Φ) (H ‼ʰ[nsubst'_nheight] 0) eq_refl eq_refl
    | (∃: V, P)%n, _ => λ un gn, ∃ Φ,
        nintp_gen (nsubst' P un gn Φ) (H ‼ʰ[nsubst'_nheight] 0) eq_refl eq_refl
    | (rec:ˢ' Φ a)%n, _ => λ un gn, nintp_gen
        (nsubst' (Φ a) un gn (rew[λ _,_] ctxeq_ug un gn in rec:ˢ' Φ)%n)
        (H ‼ʰ[nsubst'_nheight] 0) eq_refl eq_refl
    | (rec:ˡ' Φ a)%n, _ => λ un gn, nintp_gen
        (nsubst' (Φ a) un gn (rew[λ _,_] ctxeq_ug un gn in rec:ˡ' Φ)%n)
        (H ‼ʰ[nsubst'_nheight] 0) eq_refl eq_refl
    | (%ᵍˢ s)%n, _ | (%ᵍˡ s)%n, _ => λ _, seqnil s | (%ᵘˢ s)%n, _ => seqnil s
    | (!ᵘˢ P)%n, _ => λ _ _, nintpS P
    end%I.
End nintp_gen.

Section nintp.
  Context (* Iris resources *) `{!nintpGS Σ}.

  (** [nintpS_gen]/[nintp_gen] typed as a discrete function *)
  Definition nintpS_gen' : (_ -d> _ -d> _ -d> iProp Σ) ->
    _ -d> _ -d> _ -d> _ -d> _ -d> _ -d> _ -d> _ -d> iProp Σ :=
    λ ni s κ Γ (P : nProp κ Γ), nintpS_gen ni s P.
  Definition nintp_gen' : (_ -d> _ -d> _ -d> iProp Σ) ->
    _ -d> _ -d> _ -d> _ -d> _ -d> _ -d> _ -d> iProp Σ :=
    λ ni s κ Γ (P : nProp κ Γ), nintp_gen ni s P.

  (** [nintpS_gen] is contractive *)
  #[export] Instance nintpS_gen_contractive : Contractive nintpS_gen'.
  Proof.
    unfold nintpS_gen'=> i ni ni' nid s + + + + + + +. fix FIX 4=> κ Γ P H.
    case: P H=>/=; intros; case H=>//= ?;
    try (by f_equiv=> >; apply FIX); case c=>//=; by f_contractive; apply nid.
  Qed.

  (** [nintp_gen] is contractive *)
  #[export] Instance nintp_gen_contractive : Contractive nintp_gen'.
  Proof.
    unfold nintp_gen'=> i ni ni' nid s + + + + + +. fix FIX 4=> κ Γ P H.
    case: P H=>/=; intros; case H=>//= ?; try (by f_equiv=> >; apply FIX);
      try (case c=>//=; by f_contractive; apply nid);
      try (try (case c=>/=; f_equiv=> ?); by apply nintpS_gen_contractive);
      [apply wpw_ne=> >; [|by apply FIX]|apply twpw_ne=> >; [|by apply FIX]];
      f_equiv=> ?; by apply nintpS_gen_contractive.
  Qed.

  (** [nintp_pre]: Generator of [nintp_fp] *)
  Definition nintp_pre
    : (_ -d> _ -d> _ -d> iProp Σ) -> (_ -d> _ -d> _ -d> iProp Σ)
    := λ ni s κ (P : nProp κ (;ᵞ)), nintp_gen' ni s _ _ P hwf eq_refl eq_refl.
  #[export] Instance nintp_pre_contractive : Contractive nintp_pre.
  Proof. move=> ???????. by apply nintp_gen_contractive. Qed.

  (** [nintp_fp]: Fixpoint interpretation of [nProp κ (;ᵞ)] *)
  Definition nintp_fp : _ → ∀ κ, nProp κ (;ᵞ) → iProp Σ := fixpoint nintp_pre.
End nintp.

(** Notations, which will be printed in (partial) interpretation, yay! *)

Notation "⟦ P ⟧ᶠ ( s )" := (nintp_fp s _ P)
  (format "'[' ⟦  P  ⟧ᶠ '/  ' ( s ) ']'") : nola_scope.
Notation "⟦ P ⟧{ κ } ( s , H )" :=
  (@nintp_gen _ _ nintp_fp s κ (;ᵞ) P H eq_refl eq_refl) (only parsing)
  : nola_scope.
Notation "⟦ P ⟧{ κ } ( s )" := (⟦ P ⟧{κ}(s, hwf)) (only parsing) : nola_scope.
Notation "⟦ P ⟧ ( s , H )" := ⟦ P ⟧{_}(s, H)
  (format "'[' ⟦  P  ⟧ '/  ' ( s ,  H ) ']'") : nola_scope.
Notation "⟦ P ⟧ ( s )" := ⟦ P ⟧(s, hwf)
  (format "'[' ⟦  P  ⟧ '/  ' ( s ) ']'") : nola_scope.
Notation nintp s P := ⟦ P ⟧(s) (only parsing).
Notation "⟦ P ⟧ˢ ( s , H )" :=
  (@nintpS_gen _ _ nintp_fp s nS (;ᵞ) P H eq_refl eq_refl eq_refl)
  (format "'[' ⟦  P  ⟧ˢ '/  ' ( s ,  H ) ']'") : nola_scope.
Notation "⟦ P ⟧ˢ ( s )" := ⟦ P ⟧ˢ(s, hwf)
  (format "'[' ⟦  P  ⟧ˢ '/  ' ( s ) ']'") : nola_scope.
Notation nintpS s P := ⟦ P ⟧ˢ(s) (only parsing).
Notation "⟦ s ⟧ˢ" := (Swrap (λ iP, ⟦ sarg_data iP ⟧(s))) (format "⟦ s ⟧ˢ ")
  : nola_scope.

(** ** Facts on [⟦ ⟧] etc. *)
Section nintp_facts.
  Context (* Iris resources *) `{!nintpGS Σ}.

  (** [⟦ ⟧ᶠ] coincides with [⟦ ⟧] *)
  Lemma nintp_fp_nintp {s κ P} : ⟦ P ⟧ᶠ(s) ⊣⊢ ⟦ P ⟧{κ}(s).
  Proof. unfold nintp_fp. apply (fixpoint_unfold nintp_pre). Qed.

  (** [nintpS_gen] coincides with [nintp_gen] *)
  Lemma nintpS_gen_nintp_gen {ni s κ Γ} {P : nProp κ Γ} {H κS un gn} :
    nintpS_gen ni s P H κS un gn ⊣⊢ nintp_gen ni s P H un gn.
  Proof.
    move: κ Γ P H κS un gn. fix FIX 4=> κ Γ P H.
    case: P H; intros; case H=>//= ?; try f_equiv=> >; apply FIX.
  Qed.
  (** [⟦ ⟧ˢ] coincides with [⟦ ⟧] *)
  Lemma nintpS_nintp {s P} : ⟦ P ⟧ˢ(s) ⊣⊢ ⟦ P ⟧(s).
  Proof. exact nintpS_gen_nintp_gen. Qed.

  (** Simplify [nintp_gen] over [nlarge] *)
  Lemma nintp_gen_nlarge {ni s κ Γ} {P : nProp κ Γ} {H un gn} :
    nintp_gen ni s (nlarge P) H un gn ⊣⊢ nintp_gen ni s P hwf un gn.
  Proof.
    move: κ Γ P H un gn. fix FIX 4=> κ Γ P H.
    case: P H=>/=; intros; case H=>/= he; f_equiv=> >; try apply FIX;
    try apply leibniz_equiv, eq_hacc;
    rewrite rew_eq_hwf; move: nsubst'_nheight=>/=; subst;
    have EQ := nsubst_nlarge (P:=P); move: (nsubst (nlarge P)) EQ;
    move=> ?->?; apply FIX.
  Qed.
  (** Simplify [⟦ ⟧] over [nlarge] *)
  Lemma nintp_nlarge {s κ P} : ⟦ nlarge P ⟧(s) ⊣⊢ ⟦ P ⟧{κ}(s).
  Proof. exact nintp_gen_nlarge. Qed.
  (** [⟦ ⟧ˢ] coincides with [⟦ ⟧] over [nlarge] *)
  Lemma nintpS_nintp_nlarge {s P} : ⟦ P ⟧ˢ(s) ⊣⊢ ⟦ nlarge P ⟧(s).
  Proof. by rewrite nintpS_nintp nintp_nlarge. Qed.
End nintp_facts.

(** Utility *)
Notation nninv_wsat s := (ninv_wsat (λ P, ⟦ P ⟧ˢ(s))).
