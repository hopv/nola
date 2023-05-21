(** * [nintp]: Interpretation of [nProp] as [iProp] *)

From nola.examples.logic Require Export subst.
From iris.base_logic.lib Require Import iprop fancy_updates.
Import EqNotations.

(** Type of a derivability predicate *)
Notation nderiv_ty := (nat → nPropL (;ᵞ) * nPropL (;ᵞ) → Prop).
Notation npderiv_ty := (nderiv_ty → nderiv_ty).

(** Nola resources *)
Class nintpG (Σ : gFunctors) := NintpG {
  nintpG_invG :: invGS_gen HasNoLc Σ;
}.

(** Modification of [nsubst] *)
Definition nsubst' {σ Γᵘ Γᵍ V} (P : nProp σ (V :: Γᵘ;ᵞ Γᵍ))
  (un : Γᵘ = []) (gn : Γᵍ = []) : nPred V → nProp σ (;ᵞ) :=
  nsubst (rew ctxeq_ug (f_equal (_ ::.) un) gn in P).
Arguments nsubst' {_ _ _ _} _ _ _ /.

(** [nsubst'] preserves [nheight] *)
Lemma nsubst'_nheight {σ Γᵘ Γᵍ V} {P : nProp σ (V :: Γᵘ;ᵞ Γᵍ)} {un gn Φ} :
  nheight (nsubst' P un gn Φ) = nheight P.
Proof. subst. apply nsubst_nheight. Qed.

(** ** [nintp]: Interpretation of [nProp] as [iProp] *)
Section nintp_gen.
  Context
    (** Iris resources *) `{!nintpG Σ}
    (** Interpretation used contractively *)
    (ni : nderiv_ty → ∀ σ, nProp σ (;ᵞ) → iProp Σ)
    (** Derivability predicate *) (d : nderiv_ty).

  (** [nintpS_gen P] : Evaluate small [P] *)
  Fixpoint nintpS_gen {σ Γ} (P : nProp σ Γ) (H : hAcc (nheight P))
    : σ = nS → Γ.ᵞu = [] → Γ.ᵞg = [] → iProp Σ :=
    match P, H with
    | ⌜φ⌝%n, _ => λ _ _ _, ⌜φ⌝
    | (P ∧ Q)%n, _ => λ σS un gn,
        nintpS_gen P (H ‼ʰ true) σS un gn ∧ nintpS_gen Q (H ‼ʰ false) σS un gn
    | (P ∨ Q)%n, _ => λ σS un gn,
        nintpS_gen P (H ‼ʰ true) σS un gn ∨ nintpS_gen Q (H ‼ʰ false) σS un gn
    | (P → Q)%n, _ => λ σS un gn,
        nintpS_gen P (H ‼ʰ true) σS un gn → nintpS_gen Q (H ‼ʰ false) σS un gn
    | (∀' Φ)%n, _ => λ σS un gn, ∀ a, nintpS_gen (Φ a) (H ‼ʰ a) σS un gn
    | (∃' Φ)%n, _ => λ σS un gn, ∃ a, nintpS_gen (Φ a) (H ‼ʰ a) σS un gn
    | (P ∗ Q)%n, _ => λ σS un gn,
        nintpS_gen P (H ‼ʰ true) σS un gn ∗ nintpS_gen Q (H ‼ʰ false) σS un gn
    | (P -∗ Q)%n, _ => λ σS un gn,
        nintpS_gen P (H ‼ʰ true) σS un gn -∗ nintpS_gen Q (H ‼ʰ false) σS un gn
    | (□ P)%n, _ => λ σS un gn, □ nintpS_gen P (H ‼ʰ ()) σS un gn
    | (■ P)%n, _ => λ σS un gn, ■ nintpS_gen P (H ‼ʰ ()) σS un gn
    | (|==> P)%n, _ => λ σS un gn, |==> nintpS_gen P (H ‼ʰ ()) σS un gn
    | (|={E,E'}=> P)%n, _ => λ σS un gn,
        |={E,E'}=> nintpS_gen P (H ‼ʰ ()) σS un gn
    | (▷ P)%n, _ => λ _ un gn, ▷ ni d _ (rew app_eq_nil_ug_g un gn in P)
    | (P ⊢{i} Q)%n, _ => λ _ un gn,
        ⌜d i ((rew app_eq_nil_ug_g un gn in P), rew app_eq_nil_ug_g un gn in Q)⌝
    | (∀: V, P)%n, _ => λ σS un gn, ∀ Φ, nintpS_gen
        (nsubst' P un gn Φ) (H ‼ʰ[nsubst'_nheight] ()) σS eq_refl eq_refl
    | (∃: V, P)%n, _ => λ σS un gn, ∃ Φ, nintpS_gen
        (nsubst' P un gn Φ) (H ‼ʰ[nsubst'_nheight] ()) σS eq_refl eq_refl
    | (rec:ˢ' Φ a)%n, _ => λ _ un gn, nintpS_gen
        (nsubst' (Φ a) un gn (rew[λ _,_] ctxeq_ug un gn in rec:ˢ' Φ)%n)
        (H ‼ʰ[nsubst'_nheight] ()) eq_refl eq_refl eq_refl
    | (rec:ˡ' Φ a)%n, _ => λ σS, match σS with end
    | (%ᵍˢ s)%n, _ => λ _ _, seqnil s
    | (%ᵍˡ s)%n, _ => λ σS, match σS with end
    | (%ᵘˢ s)%n, _ => λ σS, match σS with end
    | (!ᵘˢ P)%n, _ => λ σS, match σS with end
    end%I.

  (** [nintp_gen P] : Evaluate [P] *)
  Fixpoint nintp_gen {σ Γ} (P : nProp σ Γ) (H : hAcc (nheight P))
    : Γ.ᵞu = [] → Γ.ᵞg = [] → iProp Σ :=
    match P, H with
    | ⌜φ⌝%n, _ => λ _ _, ⌜φ⌝
    | (P ∧ Q)%n, _ => λ un gn,
        nintp_gen P (H ‼ʰ true) un gn ∧ nintp_gen Q (H ‼ʰ false) un gn
    | (P ∨ Q)%n, _ => λ un gn,
        nintp_gen P (H ‼ʰ true) un gn ∨ nintp_gen Q (H ‼ʰ false) un gn
    | (P → Q)%n, _ => λ un gn,
        nintp_gen P (H ‼ʰ true) un gn → nintp_gen Q (H ‼ʰ false) un gn
    | (∀' Φ)%n, _ => λ un gn, ∀ a, nintp_gen (Φ a) (H ‼ʰ a) un gn
    | (∃' Φ)%n, _ => λ un gn, ∃ a, nintp_gen (Φ a) (H ‼ʰ a) un gn
    | (P ∗ Q)%n, _ => λ un gn,
        nintp_gen P (H ‼ʰ true) un gn ∗ nintp_gen Q (H ‼ʰ false) un gn
    | (P -∗ Q)%n, _ => λ un gn,
        nintp_gen P (H ‼ʰ true) un gn -∗ nintp_gen Q (H ‼ʰ false) un gn
    | (□ P)%n, _ => λ un gn, □ nintp_gen P (H ‼ʰ ()) un gn
    | (■ P)%n, _ => λ un gn, ■ nintp_gen P (H ‼ʰ ()) un gn
    | (|==> P)%n, _ => λ un gn, |==> nintp_gen P (H ‼ʰ ()) un gn
    | (|={E,E'}=> P)%n, _ => λ un gn, |={E,E'}=> nintp_gen P (H ‼ʰ ()) un gn
    | (▷ P)%n, _ => λ un gn, ▷ ni d _ (rew app_eq_nil_ug_g un gn in P)
    | (P ⊢{i} Q)%n, _ => λ un gn,
        ⌜d i ((rew app_eq_nil_ug_g un gn in P), rew app_eq_nil_ug_g un gn in Q)⌝
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
    λ ni d σ Γ (P : nProp σ Γ), nintpS_gen ni d P.
  Definition nintp_gen' : (_ -d> _ -d> _ -d> iProp Σ) ->
    _ -d> _ -d> _ -d> _ -d> _ -d> _ -d> _ -d> iProp Σ :=
    λ ni d σ Γ (P : nProp σ Γ), nintp_gen ni d P.

  (** [nintpS_gen] is contractive *)
  #[export] Instance nintpS_gen_contractive : Contractive nintpS_gen'.
  Proof.
    unfold nintpS_gen'=> i ni ni' nid d + + + + + + +. fix FIX 4=> σ Γ P H.
    case: P H=>/=; intros; case H=>//= ?;
    try (by f_equiv=> >; apply FIX); by f_contractive; apply nid.
  Qed.

  (** [nintp_gen] is contractive *)
  #[export] Instance nintp_gen_contractive : Contractive nintp_gen'.
  Proof.
    unfold nintp_gen'=> i ni ni' nid d + + + + + +. fix FIX 4=> σ Γ P H.
    case: P H=>/=; intros; case H=>//= ?; try (by f_equiv=> >; apply FIX);
    try (by f_contractive; apply nid); by apply nintpS_gen_contractive.
  Qed.

  (** [nintp_pre]: Generator of [nintp_fp] *)
  Definition nintp_pre
    : (_ -d> _ -d> _ -d> iProp Σ) -> (_ -d> _ -d> _ -d> iProp Σ)
    := λ ni d σ (P : nProp σ (;ᵞ)), nintp_gen' ni d _ _ P hwf eq_refl eq_refl.
  #[export] Instance nintp_pre_contractive : Contractive nintp_pre.
  Proof. move=> ???????. by apply nintp_gen_contractive. Qed.

  (** [nintp_fp]: Fixpoint interpretation of [nProp σ (;ᵞ)] *)
  Definition nintp_fp : _ → ∀ σ, nProp σ (;ᵞ) → iProp Σ := fixpoint nintp_pre.
End nintp.

(** Notations, which will be printed in (partial) interpretation, yay! *)

Notation "⟦ P ⟧ᶠ ( d )" := (nintp_fp d _ P)
  (format "'[' ⟦  P  ⟧ᶠ '/  ' ( d ) ']'") : nola_scope.
Notation "⟦ P ⟧{ Σ , σ } ( d , H )" :=
  (@nintp_gen Σ _ nintp_fp d σ (;ᵞ) P H eq_refl eq_refl) (only parsing)
  : nola_scope.
Notation "⟦ P ⟧{ Σ , σ } ( d )" := (⟦ P ⟧{Σ, σ}(d, hwf)) (only parsing)
  : nola_scope.
Notation "⟦ P ⟧ ( d , H )" := ⟦ P ⟧{_,_}(d, H)
  (format "'[' ⟦  P  ⟧ '/  ' ( d ,  H ) ']'") : nola_scope.
Notation "⟦ P ⟧ ( d )" := ⟦ P ⟧(d, hwf)
  (format "'[' ⟦  P  ⟧ '/  ' ( d ) ']'") : nola_scope.
Notation "⟦ P ⟧ˢ{ Σ } ( d , H )" :=
  (@nintpS_gen Σ _ nintp_fp d nS (;ᵞ) P H eq_refl eq_refl eq_refl)
  (only parsing).
Notation "⟦ P ⟧ˢ{ Σ } ( d )" := (⟦ P ⟧ˢ{Σ}(d, hwf)) (only parsing)
  : nola_scope.
Notation "⟦ P ⟧ˢ ( d , H )" := ⟦ P ⟧ˢ{_}(d, H)
  (format "'[' ⟦  P  ⟧ˢ '/  ' ( d ,  H ) ']'") : nola_scope.
Notation "⟦ P ⟧ˢ ( d )" := ⟦ P ⟧ˢ(d, hwf)
  (format "'[' ⟦  P  ⟧ˢ '/  ' ( d ) ']'") : nola_scope.

(** ** Facts on [⟦ _ ⟧] etc. *)
Section nintp_facts.
  Context (** Iris resources *) `{!nintpG Σ}.

  (** [⟦ _ ⟧ᶠ] coincides with [⟦ _ ⟧] *)
  Lemma nintp_fp_nintp {d σ P} : ⟦ P ⟧ᶠ(d) ⊣⊢ ⟦ P ⟧{Σ, σ}(d).
  Proof. unfold nintp_fp. apply (fixpoint_unfold nintp_pre). Qed.

  (** [nintpS_gen] coincides with [nintp_gen] *)
  Lemma nintpS_gen_nintp_gen {ni d σ Γ} {P : nProp σ Γ} {H σS un gn} :
    nintpS_gen (Σ:=Σ) ni d P H σS un gn ⊣⊢ nintp_gen ni d P H un gn.
  Proof.
    move: σ Γ P H σS un gn. fix FIX 4=> σ Γ P H.
    case: P H; intros; case H=>//= ?; try f_equiv=> >; apply FIX.
  Qed.
  (** [nintpS] coincides with [nintp] *)
  Lemma nintpS_nintp {d P} : ⟦ P ⟧ˢ(d) ⊣⊢ ⟦ P ⟧(d).
  Proof. exact nintpS_gen_nintp_gen. Qed.

  (** Simplify [nintp_gen] over [nlarge] *)
  Lemma nintp_gen_nlarge {ni d σ Γ} {P : nProp σ Γ} {H un gn} :
    nintp_gen (Σ:=Σ) ni d (nlarge P) H un gn ⊣⊢ nintp_gen ni d P hwf un gn.
  Proof.
    move: σ Γ P H un gn. fix FIX 4=> σ Γ P H.
    case: P H=>/=; intros; case H=>/= he; f_equiv=> >; try apply FIX;
    try apply leibniz_equiv, eq_hacc;
    rewrite rew_eq_hwf; move: nsubst'_nheight=>/=; subst;
    have EQ := nsubst_nlarge (P:=P); move: (nsubst (nlarge P)) EQ;
    move=> ?->?; apply FIX.
  Qed.
  (** Simplify [nintp] over [nlarge] *)
  Lemma nintp_nlarge {d σ P} : ⟦ nlarge P ⟧(d) ⊣⊢ ⟦ P ⟧{Σ, σ}(d).
  Proof. exact nintp_gen_nlarge. Qed.
  (** [nintpS] coincides with [nintp] over [nlarge] *)
  Lemma nintpS_nintp_nlarge {d P} : ⟦ P ⟧ˢ(d) ⊣⊢ ⟦ nlarge P ⟧(d).
  Proof. by rewrite nintpS_nintp nintp_nlarge. Qed.
End nintp_facts.
