(** * [neval]: Evaluation of [nProp] as [iProp] *)

From nola.examples.logic Require Export subst.
From iris.base_logic.lib Require Import iprop fancy_updates.
Import EqNotations.

(** Type of a derivability predicate *)
Notation nderiv_ty := (nat → nPropL (;) * nPropL (;) → Prop).
Notation npderiv_ty := (nderiv_ty → nderiv_ty).

(** Nola resources *)
Class nevalG (Σ : gFunctors) := NevalG {
  nevalG_invG :: invGS_gen HasNoLc Σ;
}.

(** Modification of [nsubst] *)
Definition nsubst' {σ Γᵒ Γⁱ V} (P : nProp σ (V :: Γᵒ; Γⁱ))
  (no : Γᵒ = []) (ni : Γⁱ = []) : nPred V → nProp σ (;) :=
  nsubst
    (nProp_rewi (rew[λ Γᵒ, nProp _ (_ :: Γᵒ; _)] no in P) ni).
  Arguments nsubst' {_ _ _ _} _ _ _ /.

(** [nsubst'] preserves [nheight] *)
Lemma nsubst'_nheight {σ Γᵒ Γⁱ V} {P : nProp σ (V :: Γᵒ; Γⁱ)} {no ni Φ} :
  nheight (nsubst' P no ni Φ) = nheight P.
Proof. subst. apply nsubst_nheight. Qed.

Definition nProp_rewina {σ Γᵒ Γⁱ} (P : nProp σ (; Γᵒ ++ Γⁱ))
  (no : Γᵒ = []) (ni : Γⁱ = []) : nProp σ (;) :=
  nProp_rewi P (eq_trans (f_equal (.++ Γⁱ) no) ni).
Arguments nProp_rewina {_ _ _} _ _ _ /.

Definition nPred_rewoin {A σ Γᵒ Γⁱ} (Φ : A → nProp σ (Γᵒ; Γⁱ))
  (no : Γᵒ = []) (ni : Γⁱ = []) : A → nProp σ (;) :=
  rew[λ _, _] ni in rew[λ Γᵒ, A → nProp σ (Γᵒ; _)] no in Φ.
Arguments nPred_rewoin {_ _ _ _} _ _ _ /.

Section neval_gen.
  Context
    (** Iris resources *) `{!nevalG Σ}
    (** Evaluation used contractively *)
    (nev : nderiv_ty → ∀ σ, nProp σ (;) → iProp Σ)
    (** Derivability predicate *) (d : nderiv_ty).

  (** ** [nevalS_gen P] : Evaluate small [P] *)
  Fixpoint nevalS_gen {σ Γ} (P : nProp σ Γ) (H : hAcc (nheight P))
    : σ = nS → Γ.(nctx_o) = [] → Γ.(nctx_i) = [] → iProp Σ :=
    match P, H with
    | ⌜φ⌝%n, _ => λ _ _ _, ⌜φ⌝
    | (P ∧ Q)%n, _ => λ σS no ni,
        nevalS_gen P (H ‼ʰ true) σS no ni ∧ nevalS_gen Q (H ‼ʰ false) σS no ni
    | (P ∨ Q)%n, _ => λ σS no ni,
        nevalS_gen P (H ‼ʰ true) σS no ni ∨ nevalS_gen Q (H ‼ʰ false) σS no ni
    | (P → Q)%n, _ => λ σS no ni,
        nevalS_gen P (H ‼ʰ true) σS no ni → nevalS_gen Q (H ‼ʰ false) σS no ni
    | (∀' Φ)%n, _ => λ σS no ni, ∀ a, nevalS_gen (Φ a) (H ‼ʰ a) σS no ni
    | (∃' Φ)%n, _ => λ σS no ni, ∃ a, nevalS_gen (Φ a) (H ‼ʰ a) σS no ni
    | (P ∗ Q)%n, _ => λ σS no ni,
        nevalS_gen P (H ‼ʰ true) σS no ni ∗ nevalS_gen Q (H ‼ʰ false) σS no ni
    | (P -∗ Q)%n, _ => λ σS no ni,
        nevalS_gen P (H ‼ʰ true) σS no ni -∗ nevalS_gen Q (H ‼ʰ false) σS no ni
    | (□ P)%n, _ => λ σS no ni, □ nevalS_gen P (H ‼ʰ ()) σS no ni
    | (■ P)%n, _ => λ σS no ni, ■ nevalS_gen P (H ‼ʰ ()) σS no ni
    | (|==> P)%n, _ => λ σS no ni, |==> nevalS_gen P (H ‼ʰ ()) σS no ni
    | (|={E,E'}=> P)%n, _ => λ σS no ni,
        |={E,E'}=> nevalS_gen P (H ‼ʰ ()) σS no ni
    | (▷ P)%n, _ => λ _ no ni, ▷ nev d _ (nProp_rewina P no ni)
    | (P ⊢!{i} Q)%n, _ => λ _ no ni,
        ⌜d i (nProp_rewina P no ni, nProp_rewina P no ni)⌝
    | ((rec:ˢ' Φ) a)%n, _ => λ _ no ni, nevalS_gen
        (nsubst' (Φ a) no ni (nPred_rewoin (rec:ˢ' Φ)%n no ni))
        (H ‼ʰ[nsubst'_nheight] ()) eq_refl eq_refl eq_refl
    | ((rec:ˡ' Φ) a)%n, _ => λ σS, match σS with end
    | (∀: V, P)%n, _ => λ σS no ni, ∀ Φ, nevalS_gen
        (nsubst' P no ni Φ) (H ‼ʰ[nsubst'_nheight] ()) σS eq_refl eq_refl
    | (∃: V, P)%n, _ => λ σS no ni, ∃ Φ, nevalS_gen
        (nsubst' P no ni Φ) (H ‼ʰ[nsubst'_nheight] ()) σS eq_refl eq_refl
    | (%ⁱˢ s)%n, _ => λ _ _, seqnil s
    | (%ⁱˡ s)%n, _ => λ σS, match σS with end
    | (%ᵒˢ s)%n, _ => λ σS, match σS with end
    | (!ᵒˢ P)%n, _ => λ σS, match σS with end
    end%I.

  (** ** [neval_gen P] : Evaluate [P] *)
  Fixpoint neval_gen {σ Γ} (P : nProp σ Γ) (H : hAcc (nheight P))
    : Γ.(nctx_o) = [] → Γ.(nctx_i) = [] → iProp Σ :=
    match P, H with
    | ⌜φ⌝%n, _ => λ _ _, ⌜φ⌝
    | (P ∧ Q)%n, _ => λ no ni,
        neval_gen P (H ‼ʰ true) no ni ∧ neval_gen Q (H ‼ʰ false) no ni
    | (P ∨ Q)%n, _ => λ no ni,
        neval_gen P (H ‼ʰ true) no ni ∨ neval_gen Q (H ‼ʰ false) no ni
    | (P → Q)%n, _ => λ no ni,
        neval_gen P (H ‼ʰ true) no ni → neval_gen Q (H ‼ʰ false) no ni
    | (∀' Φ)%n, _ => λ no ni, ∀ a, neval_gen (Φ a) (H ‼ʰ a) no ni
    | (∃' Φ)%n, _ => λ no ni, ∃ a, neval_gen (Φ a) (H ‼ʰ a) no ni
    | (P ∗ Q)%n, _ => λ no ni,
        neval_gen P (H ‼ʰ true) no ni ∗ neval_gen Q (H ‼ʰ false) no ni
    | (P -∗ Q)%n, _ => λ no ni,
        neval_gen P (H ‼ʰ true) no ni -∗ neval_gen Q (H ‼ʰ false) no ni
    | (□ P)%n, _ => λ no ni, □ neval_gen P (H ‼ʰ ()) no ni
    | (■ P)%n, _ => λ no ni, ■ neval_gen P (H ‼ʰ ()) no ni
    | (|==> P)%n, _ => λ no ni, |==> neval_gen P (H ‼ʰ ()) no ni
    | (|={E,E'}=> P)%n, _ => λ no ni, |={E,E'}=> neval_gen P (H ‼ʰ ()) no ni
    | (▷ P)%n, _ => λ no ni, ▷ nev d _ (nProp_rewina P no ni)
    | (P ⊢!{i} Q)%n, _ => λ no ni,
        ⌜d i (nProp_rewina P no ni, nProp_rewina P no ni)⌝
    | ((rec:ˢ' Φ) a)%n, _ => λ no ni, neval_gen
        (nsubst' (Φ a) no ni (nPred_rewoin (rec:ˢ' Φ)%n no ni))
        (H ‼ʰ[nsubst'_nheight] ()) eq_refl eq_refl
    | ((rec:ˡ' Φ) a)%n, _ => λ no ni, neval_gen
        (nsubst' (Φ a) no ni (nPred_rewoin (rec:ˡ' Φ)%n no ni))
        (H ‼ʰ[nsubst'_nheight] ()) eq_refl eq_refl
    | (∀: V, P)%n, _ => λ no ni, ∀ Φ,
        neval_gen (nsubst' P no ni Φ) (H ‼ʰ[nsubst'_nheight] ()) eq_refl eq_refl
    | (∃: V, P)%n, _ => λ no ni, ∃ Φ,
        neval_gen (nsubst' P no ni Φ) (H ‼ʰ[nsubst'_nheight] ()) eq_refl eq_refl
    | (%ⁱˢ s)%n, _ => λ _, seqnil s
    | (%ⁱˡ s)%n, _ => λ _, seqnil s
    | (%ᵒˢ s)%n, _ => seqnil s
    | (!ᵒˢ P)%n, _ => λ _ _, nevalS_gen P hwf eq_refl eq_refl eq_refl
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
    try (by f_equiv=> >; apply FIX); try (by f_contractive; apply nevd).
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
    := λ nev d σ (P : nProp σ (;)), neval_gen' nev d _ _ P hwf eq_refl eq_refl.
  #[export] Instance neval_pre_contractive : Contractive neval_pre.
  Proof. move=> ???????. by apply neval_gen_contractive. Qed.

  (** [neval_fp]: Fixpoint evaluation of [nProp σ (;)] *)
  Definition neval_fp : _ → ∀ σ, nProp σ (;) → iProp Σ := fixpoint neval_pre.
End neval.

(** The notations [neval]/[nevalx] (as well as [nevalS]/[nevalSx])
  will be printed in (partial) evaluation, yay! *)

Notation nevalx' Σ d σ P H :=
  (@neval_gen Σ _ neval_fp d σ (;) P H eq_refl eq_refl) (only parsing).
Notation neval' Σ d σ P := (nevalx' Σ d σ P hwf).
Notation nevalx d P H := (nevalx' _ d _ P H).
Notation neval d P := (nevalx d P hwf).
Notation nevalSx' Σ d P H :=
  (@nevalS_gen Σ _ neval_fp d nS (;) P H eq_refl eq_refl eq_refl)
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
  Lemma nevalS_gen_neval_gen {nev d σ Γ} {P : nProp σ Γ} {H σS no ni} :
    nevalS_gen (Σ:=Σ) nev d P H σS no ni ⊣⊢ neval_gen nev d P H no ni.
  Proof.
    move: σ Γ P H σS no ni. fix FIX 4=> σ Γ P H.
    case: P H; intros; case H=>//= ?; try f_equiv=> >; apply FIX.
  Qed.
  (** [nevalS] coincides with [neval] *)
  Lemma nevalS_neval {d P} : nevalS' Σ d P ⊣⊢ neval d P.
  Proof. exact nevalS_gen_neval_gen. Qed.
  (** [nevalSx] coincides with [neval] *)
  Lemma nevalSx_neval {d P H} : nevalSx' Σ d P H ⊣⊢ neval d P.
  Proof. rewrite (eq_hwf H). exact nevalS_neval. Qed.
End neval_facts.
