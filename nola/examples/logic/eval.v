(** * [neval]: Evaluation of [nProp] as [iProp] *)

From nola.examples.logic Require Export subst.
From iris.base_logic.lib Require Import iprop fancy_updates.
Import EqNotations.

(** Type of a derivability predicate *)
Notation nderiv_ty := (nat → nPropL (;ᵞ) * nPropL (;ᵞ) → Prop).
Notation npderiv_ty := (nderiv_ty → nderiv_ty).

(** Nola resources *)
Class nevalG (Σ : gFunctors) := NevalG {
  nevalG_invG :: invGS_gen HasNoLc Σ;
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

Section neval_gen.
  Context
    (** Iris resources *) `{!nevalG Σ}
    (** Evaluation used contractively *)
    (nev : nderiv_ty → ∀ σ, nProp σ (;ᵞ) → iProp Σ)
    (** Derivability predicate *) (d : nderiv_ty).

  (** ** [nevalS_gen P] : Evaluate small [P] *)
  Fixpoint nevalS_gen {σ Γ} (P : nProp σ Γ) (H : hAcc (nheight P))
    : σ = nS → Γ.ᵞu = [] → Γ.ᵞg = [] → iProp Σ :=
    match P, H with
    | ⌜φ⌝%n, _ => λ _ _ _, ⌜φ⌝
    | (P ∧ Q)%n, _ => λ σS un gn,
        nevalS_gen P (H ‼ʰ true) σS un gn ∧ nevalS_gen Q (H ‼ʰ false) σS un gn
    | (P ∨ Q)%n, _ => λ σS un gn,
        nevalS_gen P (H ‼ʰ true) σS un gn ∨ nevalS_gen Q (H ‼ʰ false) σS un gn
    | (P → Q)%n, _ => λ σS un gn,
        nevalS_gen P (H ‼ʰ true) σS un gn → nevalS_gen Q (H ‼ʰ false) σS un gn
    | (∀' Φ)%n, _ => λ σS un gn, ∀ a, nevalS_gen (Φ a) (H ‼ʰ a) σS un gn
    | (∃' Φ)%n, _ => λ σS un gn, ∃ a, nevalS_gen (Φ a) (H ‼ʰ a) σS un gn
    | (P ∗ Q)%n, _ => λ σS un gn,
        nevalS_gen P (H ‼ʰ true) σS un gn ∗ nevalS_gen Q (H ‼ʰ false) σS un gn
    | (P -∗ Q)%n, _ => λ σS un gn,
        nevalS_gen P (H ‼ʰ true) σS un gn -∗ nevalS_gen Q (H ‼ʰ false) σS un gn
    | (□ P)%n, _ => λ σS un gn, □ nevalS_gen P (H ‼ʰ ()) σS un gn
    | (■ P)%n, _ => λ σS un gn, ■ nevalS_gen P (H ‼ʰ ()) σS un gn
    | (|==> P)%n, _ => λ σS un gn, |==> nevalS_gen P (H ‼ʰ ()) σS un gn
    | (|={E,E'}=> P)%n, _ => λ σS un gn,
        |={E,E'}=> nevalS_gen P (H ‼ʰ ()) σS un gn
    | (▷ P)%n, _ => λ _ un gn, ▷ nev d _ (rew app_eq_nil_ug_g un gn in P)
    | (P ⊢{i} Q)%n, _ => λ _ un gn,
        ⌜d i ((rew app_eq_nil_ug_g un gn in P), rew app_eq_nil_ug_g un gn in Q)⌝
    | (∀: V, P)%n, _ => λ σS un gn, ∀ Φ, nevalS_gen
        (nsubst' P un gn Φ) (H ‼ʰ[nsubst'_nheight] ()) σS eq_refl eq_refl
    | (∃: V, P)%n, _ => λ σS un gn, ∃ Φ, nevalS_gen
        (nsubst' P un gn Φ) (H ‼ʰ[nsubst'_nheight] ()) σS eq_refl eq_refl
    | ((rec:ˢ' Φ) a)%n, _ => λ _ un gn, nevalS_gen
        (nsubst' (Φ a) un gn (rew[λ _,_] ctxeq_ug un gn in rec:ˢ' Φ)%n)
        (H ‼ʰ[nsubst'_nheight] ()) eq_refl eq_refl eq_refl
    | ((rec:ˡ' Φ) a)%n, _ => λ σS, match σS with end
    | (%ᵍˢ s)%n, _ => λ _ _, seqnil s
    | (%ᵍˡ s)%n, _ => λ σS, match σS with end
    | (%ᵘˢ s)%n, _ => λ σS, match σS with end
    | (!ᵘˢ P)%n, _ => λ σS, match σS with end
    end%I.

  (** ** [neval_gen P] : Evaluate [P] *)
  Fixpoint neval_gen {σ Γ} (P : nProp σ Γ) (H : hAcc (nheight P))
    : Γ.ᵞu = [] → Γ.ᵞg = [] → iProp Σ :=
    match P, H with
    | ⌜φ⌝%n, _ => λ _ _, ⌜φ⌝
    | (P ∧ Q)%n, _ => λ un gn,
        neval_gen P (H ‼ʰ true) un gn ∧ neval_gen Q (H ‼ʰ false) un gn
    | (P ∨ Q)%n, _ => λ un gn,
        neval_gen P (H ‼ʰ true) un gn ∨ neval_gen Q (H ‼ʰ false) un gn
    | (P → Q)%n, _ => λ un gn,
        neval_gen P (H ‼ʰ true) un gn → neval_gen Q (H ‼ʰ false) un gn
    | (∀' Φ)%n, _ => λ un gn, ∀ a, neval_gen (Φ a) (H ‼ʰ a) un gn
    | (∃' Φ)%n, _ => λ un gn, ∃ a, neval_gen (Φ a) (H ‼ʰ a) un gn
    | (P ∗ Q)%n, _ => λ un gn,
        neval_gen P (H ‼ʰ true) un gn ∗ neval_gen Q (H ‼ʰ false) un gn
    | (P -∗ Q)%n, _ => λ un gn,
        neval_gen P (H ‼ʰ true) un gn -∗ neval_gen Q (H ‼ʰ false) un gn
    | (□ P)%n, _ => λ un gn, □ neval_gen P (H ‼ʰ ()) un gn
    | (■ P)%n, _ => λ un gn, ■ neval_gen P (H ‼ʰ ()) un gn
    | (|==> P)%n, _ => λ un gn, |==> neval_gen P (H ‼ʰ ()) un gn
    | (|={E,E'}=> P)%n, _ => λ un gn, |={E,E'}=> neval_gen P (H ‼ʰ ()) un gn
    | (▷ P)%n, _ => λ un gn, ▷ nev d _ (rew app_eq_nil_ug_g un gn in P)
    | (P ⊢{i} Q)%n, _ => λ un gn,
        ⌜d i ((rew app_eq_nil_ug_g un gn in P), rew app_eq_nil_ug_g un gn in Q)⌝
    | (∀: V, P)%n, _ => λ un gn, ∀ Φ,
        neval_gen (nsubst' P un gn Φ) (H ‼ʰ[nsubst'_nheight] ()) eq_refl eq_refl
    | (∃: V, P)%n, _ => λ un gn, ∃ Φ,
        neval_gen (nsubst' P un gn Φ) (H ‼ʰ[nsubst'_nheight] ()) eq_refl eq_refl
    | ((rec:ˢ' Φ) a)%n, _ => λ un gn, neval_gen
        (nsubst' (Φ a) un gn (rew[λ _,_] ctxeq_ug un gn in rec:ˢ' Φ)%n)
        (H ‼ʰ[nsubst'_nheight] ()) eq_refl eq_refl
    | ((rec:ˡ' Φ) a)%n, _ => λ un gn, neval_gen
        (nsubst' (Φ a) un gn (rew[λ _,_] ctxeq_ug un gn in rec:ˡ' Φ)%n)
        (H ‼ʰ[nsubst'_nheight] ()) eq_refl eq_refl
    | (%ᵍˢ s)%n, _ => λ _, seqnil s
    | (%ᵍˡ s)%n, _ => λ _, seqnil s
    | (%ᵘˢ s)%n, _ => seqnil s
    | (!ᵘˢ P)%n, _ => λ _ _, nevalS_gen P hwf eq_refl eq_refl eq_refl
    end%I.
End neval_gen.

Section neval.
  Context (** Iris resources *) `{!nevalG Σ}.

  (** [nevalS_gen]/[neval_gen] typed as a discrete function *)
  Definition nevalS_gen' : (_ -d> _ -d> _ -d> iProp Σ) ->
    _ -d> _ -d> _ -d> _ -d> _ -d> _ -d> _ -d> _ -d> iProp Σ :=
    λ nev d σ Γ (P : nProp σ Γ), nevalS_gen nev d P.
  Definition neval_gen' : (_ -d> _ -d> _ -d> iProp Σ) ->
    _ -d> _ -d> _ -d> _ -d> _ -d> _ -d> _ -d> iProp Σ :=
    λ nev d σ Γ (P : nProp σ Γ), neval_gen nev d P.

  (** [nevalS_gen] is contractive *)
  #[export] Instance nevalS_gen_contractive : Contractive nevalS_gen'.
  Proof.
    unfold nevalS_gen'=> i nev nev' nevd d + + + + + + +. fix FIX 4=> σ Γ P H.
    case: P H=>/=; intros; case H=>//= ?;
    try (by f_equiv=> >; apply FIX); by f_contractive; apply nevd.
  Qed.

  (** [neval_gen] is contractive *)
  #[export] Instance neval_gen_contractive : Contractive neval_gen'.
  Proof.
    unfold neval_gen'=> i nev nev' nevd d + + + + + +. fix FIX 4=> σ Γ P H.
    case: P H=>/=; intros; case H=>//= ?; try (by f_equiv=> >; apply FIX);
    try (by f_contractive; apply nevd); by apply nevalS_gen_contractive.
  Qed.

  (** [neval_pre]: Generator of [neval_fp] *)
  Definition neval_pre
    : (_ -d> _ -d> _ -d> iProp Σ) -> (_ -d> _ -d> _ -d> iProp Σ)
    := λ nev d σ (P : nProp σ (;ᵞ)), neval_gen' nev d _ _ P hwf eq_refl eq_refl.
  #[export] Instance neval_pre_contractive : Contractive neval_pre.
  Proof. move=> ???????. by apply neval_gen_contractive. Qed.

  (** [neval_fp]: Fixpoint evaluation of [nProp σ (;ᵞ)] *)
  Definition neval_fp : _ → ∀ σ, nProp σ (;ᵞ) → iProp Σ := fixpoint neval_pre.
End neval.

(** The notations [neval]/[nevalx] (as well as [nevalS]/[nevalSx])
  will be printed in (partial) evaluation, yay! *)

Notation nevalx' Σ d σ P H :=
  (@neval_gen Σ _ neval_fp d σ (;ᵞ) P H eq_refl eq_refl) (only parsing).
Notation neval' Σ d σ P := (nevalx' Σ d σ P hwf).
Notation nevalx d P H := (nevalx' _ d _ P H).
Notation neval d P := (nevalx d P hwf).
Notation nevalSx' Σ d P H :=
  (@nevalS_gen Σ _ neval_fp d nS (;ᵞ) P H eq_refl eq_refl eq_refl)
  (only parsing).
Notation nevalS' Σ d P := (nevalSx' Σ d P hwf).
Notation nevalSx d P H := (nevalSx' _ d P H).
Notation nevalS d P := (nevalSx d P hwf).

Section neval_facts.
  Context (** Iris resources *) `{!nevalG Σ}.

  (** [nevalx] coincides with [neval] *)
  Lemma nevalx_neval {d σ P H} : nevalx' Σ d σ P H ⊣⊢ neval d P.
  Proof. by rewrite (eq_hwf H). Qed.

  (** [neval_fp] coincides with [neval] *)
  Lemma neval_fp_neval {d σ P} : neval_fp d σ P ⊣⊢ neval d P.
  Proof. unfold neval_fp. apply (fixpoint_unfold neval_pre). Qed.

  (** [nevalS_gen] coincides with [neval_gen] *)
  Lemma nevalS_gen_neval_gen {nev d σ Γ} {P : nProp σ Γ} {H σS un gn} :
    nevalS_gen (Σ:=Σ) nev d P H σS un gn ⊣⊢ neval_gen nev d P H un gn.
  Proof.
    move: σ Γ P H σS un gn. fix FIX 4=> σ Γ P H.
    case: P H; intros; case H=>//= ?; try f_equiv=> >; apply FIX.
  Qed.
  (** [nevalS] coincides with [neval] *)
  Lemma nevalS_neval {d P} : nevalS' Σ d P ⊣⊢ neval d P.
  Proof. exact nevalS_gen_neval_gen. Qed.
  (** [nevalSx] coincides with [neval] *)
  Lemma nevalSx_neval {d P H} : nevalSx' Σ d P H ⊣⊢ neval d P.
  Proof. rewrite (eq_hwf H). exact nevalS_neval. Qed.

  (** Simplify [neval_gen] over [nlarge] *)
  Lemma neval_gen_nlarge {nev d σ Γ} {P : nProp σ Γ} {H un gn} :
    neval_gen (Σ:=Σ) nev d (nlarge P) H un gn ⊣⊢ neval_gen nev d P hwf un gn.
  Proof.
    move: σ Γ P H un gn. fix FIX 4=> σ Γ P H.
    case: P H=>/=; intros; case H=>/= he; f_equiv=> >; try apply FIX;
    try apply leibniz_equiv, eq_hacc;
    rewrite (eq_hwf (rew _ in _)); move: nsubst'_nheight=>/=;
    subst; have EQ := (nsubst_nlarge (P:=n)); move: (nsubst (nlarge n)) EQ;
    move=> ?->?; apply FIX.
  Qed.

  (** Simplify [neval] over [nlarge] *)
  Lemma neval_nlarge {d σ P} : neval d (nlarge P) ⊣⊢ neval' Σ d σ P.
  Proof. exact neval_gen_nlarge. Qed.
End neval_facts.
