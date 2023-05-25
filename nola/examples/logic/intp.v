(** * [nintp]: Interpretation of [nProp] as [iProp] *)

From nola.examples.logic Require Export subst.
From nola Require Export sintp.
From iris.base_logic.lib Require Import fancy_updates.
Import EqNotations.

(** ** [nintpG]: Nola resources *)

Class nintpG (Σ : gFunctors) := NintpG {
  nintpG_invG :: invGS_gen HasNoLc Σ;
}.

(** ** For strong interpretation *)

(** [intps] for [nPropL] *)
Definition nintps Σ : intps := Intps nat (λ _, nPropL (;ᵞ)) (iProp Σ).

(** Notation for [nintps] *)
Notation nsintp_ty Σ := (sintp_ty (nintps Σ)).
Notation npsintp_ty Σ := (psintp_ty (nintps Σ)).
Notation "⸨ P ⸩ ( s , i )" := (sunwrap s (Sarg i P%n))
  (format "'[' ⸨  P  ⸩ '/  ' ( s ,  i ) ']'") : nola_scope.

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
Section nintp_gen.
  Context
    (** Iris resources *) `{!nintpG Σ}
    (** Interpretation used contractively *)
    (ni : nsintp_ty Σ → ∀ κ, nProp κ (;ᵞ) → iProp Σ)
    (** Strong interpretation *) (s : nsintp_ty Σ).

  (** [nintpS_gen P] : Evaluate small [P] *)
  Fixpoint nintpS_gen {κ Γ} (P : nProp κ Γ) (H : hAcc (nheight P))
    : κ = nS → Γ.ᵞu = [] → Γ.ᵞg = [] → iProp Σ :=
    match P, H with
    | ⌜φ⌝%n, _ => λ _ _ _, ⌜φ⌝
    | (P ∧ Q)%n, _ => λ κS un gn,
        nintpS_gen P (H ‼ʰ 0₂) κS un gn ∧ nintpS_gen Q (H ‼ʰ 1₂) κS un gn
    | (P ∨ Q)%n, _ => λ κS un gn,
        nintpS_gen P (H ‼ʰ 0₂) κS un gn ∨ nintpS_gen Q (H ‼ʰ 1₂) κS un gn
    | (P → Q)%n, _ => λ κS un gn,
        nintpS_gen P (H ‼ʰ 0₂) κS un gn → nintpS_gen Q (H ‼ʰ 1₂) κS un gn
    | (∀' Φ)%n, _ => λ κS un gn, ∀ a, nintpS_gen (Φ a) (H ‼ʰ a) κS un gn
    | (∃' Φ)%n, _ => λ κS un gn, ∃ a, nintpS_gen (Φ a) (H ‼ʰ a) κS un gn
    | (P ∗ Q)%n, _ => λ κS un gn,
        nintpS_gen P (H ‼ʰ 0₂) κS un gn ∗ nintpS_gen Q (H ‼ʰ 1₂) κS un gn
    | (P -∗ Q)%n, _ => λ κS un gn,
        nintpS_gen P (H ‼ʰ 0₂) κS un gn -∗ nintpS_gen Q (H ‼ʰ 1₂) κS un gn
    | (□ P)%n, _ => λ κS un gn, □ nintpS_gen P (H ‼ʰ ()) κS un gn
    | (■ P)%n, _ => λ κS un gn, ■ nintpS_gen P (H ‼ʰ ()) κS un gn
    | (|==> P)%n, _ => λ κS un gn, |==> nintpS_gen P (H ‼ʰ ()) κS un gn
    | (|={E,E'}=> P)%n, _ => λ κS un gn,
        |={E,E'}=> nintpS_gen P (H ‼ʰ ()) κS un gn
    | (▷ P)%n, _ => λ _ un gn, ▷ ni s _ (rew app_eq_nil_ug_g un gn in P)
    | (○(i) P)%n, _ => λ _ un gn, ⸨ rew app_eq_nil_ug_g un gn in P ⸩(s,i)
    | (∀: V, P)%n, _ => λ κS un gn, ∀ Φ, nintpS_gen
        (nsubst' P un gn Φ) (H ‼ʰ[nsubst'_nheight] ()) κS eq_refl eq_refl
    | (∃: V, P)%n, _ => λ κS un gn, ∃ Φ, nintpS_gen
        (nsubst' P un gn Φ) (H ‼ʰ[nsubst'_nheight] ()) κS eq_refl eq_refl
    | (rec:ˢ' Φ a)%n, _ => λ _ un gn, nintpS_gen
        (nsubst' (Φ a) un gn (rew[λ _,_] ctxeq_ug un gn in rec:ˢ' Φ)%n)
        (H ‼ʰ[nsubst'_nheight] ()) eq_refl eq_refl eq_refl
    | (rec:ˡ' Φ a)%n, _ => λ κS, match κS with end
    | (%ᵍˢ s)%n, _ => λ _ _, seqnil s
    | (%ᵍˡ s)%n, _ => λ κS, match κS with end
    | (%ᵘˢ s)%n, _ => λ κS, match κS with end
    | (!ᵘˢ P)%n, _ => λ κS, match κS with end
    end%I.

  (** [nintp_gen P] : Evaluate [P] *)
  Fixpoint nintp_gen {κ Γ} (P : nProp κ Γ) (H : hAcc (nheight P))
    : Γ.ᵞu = [] → Γ.ᵞg = [] → iProp Σ :=
    match P, H with
    | ⌜φ⌝%n, _ => λ _ _, ⌜φ⌝
    | (P ∧ Q)%n, _ => λ un gn,
        nintp_gen P (H ‼ʰ 0₂) un gn ∧ nintp_gen Q (H ‼ʰ 1₂) un gn
    | (P ∨ Q)%n, _ => λ un gn,
        nintp_gen P (H ‼ʰ 0₂) un gn ∨ nintp_gen Q (H ‼ʰ 1₂) un gn
    | (P → Q)%n, _ => λ un gn,
        nintp_gen P (H ‼ʰ 0₂) un gn → nintp_gen Q (H ‼ʰ 1₂) un gn
    | (∀' Φ)%n, _ => λ un gn, ∀ a, nintp_gen (Φ a) (H ‼ʰ a) un gn
    | (∃' Φ)%n, _ => λ un gn, ∃ a, nintp_gen (Φ a) (H ‼ʰ a) un gn
    | (P ∗ Q)%n, _ => λ un gn,
        nintp_gen P (H ‼ʰ 0₂) un gn ∗ nintp_gen Q (H ‼ʰ 1₂) un gn
    | (P -∗ Q)%n, _ => λ un gn,
        nintp_gen P (H ‼ʰ 0₂) un gn -∗ nintp_gen Q (H ‼ʰ 1₂) un gn
    | (□ P)%n, _ => λ un gn, □ nintp_gen P (H ‼ʰ ()) un gn
    | (■ P)%n, _ => λ un gn, ■ nintp_gen P (H ‼ʰ ()) un gn
    | (|==> P)%n, _ => λ un gn, |==> nintp_gen P (H ‼ʰ ()) un gn
    | (|={E,E'}=> P)%n, _ => λ un gn, |={E,E'}=> nintp_gen P (H ‼ʰ ()) un gn
    | (▷ P)%n, _ => λ un gn, ▷ ni s _ (rew app_eq_nil_ug_g un gn in P)
    | (○(i) P)%n, _ => λ un gn, ⸨ rew app_eq_nil_ug_g un gn in P ⸩(s,i)
    | (∀: V, P)%n, _ => λ un gn, ∀ Φ,
        nintp_gen (nsubst' P un gn Φ) (H ‼ʰ[nsubst'_nheight] ()) eq_refl eq_refl
    | (∃: V, P)%n, _ => λ un gn, ∃ Φ,
        nintp_gen (nsubst' P un gn Φ) (H ‼ʰ[nsubst'_nheight] ()) eq_refl eq_refl
    | (rec:ˢ' Φ a)%n, _ => λ un gn, nintp_gen
        (nsubst' (Φ a) un gn (rew[λ _,_] ctxeq_ug un gn in rec:ˢ' Φ)%n)
        (H ‼ʰ[nsubst'_nheight] ()) eq_refl eq_refl
    | (rec:ˡ' Φ a)%n, _ => λ un gn, nintp_gen
        (nsubst' (Φ a) un gn (rew[λ _,_] ctxeq_ug un gn in rec:ˡ' Φ)%n)
        (H ‼ʰ[nsubst'_nheight] ()) eq_refl eq_refl
    | (%ᵍˢ s)%n, _ => λ _, seqnil s
    | (%ᵍˡ s)%n, _ => λ _, seqnil s
    | (%ᵘˢ s)%n, _ => seqnil s
    | (!ᵘˢ P)%n, _ => λ _ _, nintpS_gen P hwf eq_refl eq_refl eq_refl
    end%I.
End nintp_gen.

Section nintp.
  Context (** Iris resources *) `{!nintpG Σ}.

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
    try (by f_equiv=> >; apply FIX); by f_contractive; apply nid.
  Qed.

  (** [nintp_gen] is contractive *)
  #[export] Instance nintp_gen_contractive : Contractive nintp_gen'.
  Proof.
    unfold nintp_gen'=> i ni ni' nid s + + + + + +. fix FIX 4=> κ Γ P H.
    case: P H=>/=; intros; case H=>//= ?; try (by f_equiv=> >; apply FIX);
    try (by f_contractive; apply nid); by apply nintpS_gen_contractive.
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

(** ** Facts on [⟦ ⟧] etc. *)
Section nintp_facts.
  Context (** Iris resources *) `{!nintpG Σ}.

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
