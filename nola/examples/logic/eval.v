(** * [neval]: Evaluation of [nProp] as [iProp] *)

From nola.examples.logic Require Export subst.
From iris.base_logic.lib Require Import iprop fancy_updates.

(** Modification of [nsubstsi]/[nsubstso] *)
Definition nsubstsi_an {σ Γᵒ Γⁱ}
  : nProp σ (; Γᵒ ++ Γⁱ) → plist nPred Γᵒ → Γⁱ = [] → nProp σ (;) :=
  match Γⁱ with _ :: _ => λ _ _ eq, match eq with end | [] => λ P Φs _,
    nsubstsi (nProp_rewi P app_nil_def) Φs end.
Definition nsubstso_n {σ Γᵒ Γⁱ}
  : nProp σ (Γᵒ; Γⁱ) → plist nPred Γᵒ → Γⁱ = [] → nProp σ (;) :=
  match Γⁱ with _ :: _ => λ _ _ eq, match eq with end | [] => λ P Φs _,
    nsubstso P Φs end.

(** Type of a derivability predicate *)
Notation nderiv_ty := (nat → nPropL (;) * nPropL (;) → Prop).
Notation npderiv_ty := (nderiv_ty → nderiv_ty).

(** Nola resources *)
Class nevalG (Σ : gFunctors) := NevalG {
  nevalG_invG :: invGS_gen HasNoLc Σ;
}.

Section neval_gen.
  Context
    (** Iris resources *) `{!nevalG Σ}
    (** Evaluation used contractively *)
    (nev : nderiv_ty → ∀ σ, nProp σ (;) → iProp Σ)
    (** Derivability predicate *) (d : nderiv_ty).

  (** ** [nevalS_gen P Φs] : Evaluate small [P] under the environment [Φs] *)
  Fixpoint nevalS_gen {σ Γᵒ Γⁱ} (P : nProp σ (Γᵒ; Γⁱ))
    : σ = nS → plist nPred Γᵒ → Γⁱ = [] → iProp Σ :=
    match P with
    | ⌜φ⌝%n => λ _ _ _, ⌜φ⌝
    | (P ∧ Q)%n => λ σS Φs eq, nevalS_gen P σS Φs eq ∧ nevalS_gen Q σS Φs eq
    | (P ∨ Q)%n => λ σS Φs eq, nevalS_gen P σS Φs eq ∨ nevalS_gen Q σS Φs eq
    | (P → Q)%n => λ σS Φs eq, nevalS_gen P σS Φs eq → nevalS_gen Q σS Φs eq
    | (∀' Φ)%n => λ σS Φs eq, ∀ a, nevalS_gen (Φ a) σS Φs eq
    | (∃' Φ)%n => λ σS Φs eq, ∃ a, nevalS_gen (Φ a) σS Φs eq
    | (P ∗ Q)%n => λ σS Φs eq, nevalS_gen P σS Φs eq ∗ nevalS_gen Q σS Φs eq
    | (P -∗ Q)%n => λ σS Φs eq, nevalS_gen P σS Φs eq -∗ nevalS_gen Q σS Φs eq
    | (□ P)%n => λ σS Φs eq, □ nevalS_gen P σS Φs eq
    | (■ P)%n => λ σS Φs eq, ■ nevalS_gen P σS Φs eq
    | (|==> P)%n => λ σS Φs eq, |==> nevalS_gen P σS Φs eq
    | (|={E,E'}=> P)%n => λ σS Φs eq, |={E,E'}=> nevalS_gen P σS Φs eq
    | (▷ P)%n => λ _ Φs eq, ▷ nev d _ (nsubstsi_an P Φs eq)
    | (P ⊢!{i} Q)%n => λ _ Φs eq,
        ⌜d i (nsubstsi_an P Φs eq, nsubstsi_an P Φs eq)⌝
    | ((rec:ˢ' Φ) a)%n => λ _ Φs eq, nevalS_gen (Φ a)
        eq_refl ((λ a, nsubstso_n ((rec:ˢ' Φ)%n a) Φs eq) -:: Φs) eq
    | ((rec:ˡ' Φ) a)%n => λ σS, match σS with end
    | (∀: V, P)%n => λ σS Φs eq, ∀ Ψ, nevalS_gen P σS (Ψ -:: Φs) eq
    | (∃: V, P)%n => λ σS Φs eq, ∃ Ψ, nevalS_gen P σS (Ψ -:: Φs) eq
    | (%ⁱˢ s)%n => λ _ _, match s with
        #0 _ => λ eq, match eq with end | +/ _ => λ eq, match eq with end end
    | (%ⁱˡ s)%n => λ σS, match σS with end
    | (%ᵒˢ s)%n => λ σS, match σS with end
    | (!ᵒˢ P)%n => λ σS, match σS with end
    end%I.

  (** ** [neval_gen P Φs] : Evaluate [P] under the environment [Φs] *)
  Fixpoint neval_gen {σ Γᵒ Γⁱ} (P : nProp σ (Γᵒ; Γⁱ))
    : plist nPred Γᵒ → Γⁱ = [] → iProp Σ :=
    match P with
    | ⌜φ⌝%n => λ _ _, ⌜φ⌝
    | (P ∧ Q)%n => λ Φs eq, neval_gen P Φs eq ∧ neval_gen Q Φs eq
    | (P ∨ Q)%n => λ Φs eq, neval_gen P Φs eq ∨ neval_gen Q Φs eq
    | (P → Q)%n => λ Φs eq, neval_gen P Φs eq → neval_gen Q Φs eq
    | (∀' Φ)%n => λ Φs eq, ∀ a, neval_gen (Φ a) Φs eq
    | (∃' Φ)%n => λ Φs eq, ∃ a, neval_gen (Φ a) Φs eq
    | (P ∗ Q)%n => λ Φs eq, neval_gen P Φs eq ∗ neval_gen Q Φs eq
    | (P -∗ Q)%n => λ Φs eq, neval_gen P Φs eq -∗ neval_gen Q Φs eq
    | (□ P)%n => λ Φs eq, □ neval_gen P Φs eq
    | (■ P)%n => λ Φs eq, ■ neval_gen P Φs eq
    | (|==> P)%n => λ Φs eq, |==> neval_gen P Φs eq
    | (|={E,E'}=> P)%n => λ Φs eq, |={E,E'}=> neval_gen P Φs eq
    | (▷ P)%n => λ Φs eq, ▷ nev d _ (nsubstsi_an P Φs eq)
    | (P ⊢!{i} Q)%n => λ Φs eq, ⌜d i (nsubstsi_an P Φs eq, nsubstsi_an P Φs eq)⌝
    | ((rec:ˢ' Φ) a)%n => λ Φs eq,
        neval_gen (Φ a) ((λ a, nsubstso_n ((rec:ˢ' Φ)%n a) Φs eq) -:: Φs) eq
    | ((rec:ˡ' Φ) a)%n => λ Φs eq,
        neval_gen (Φ a) ((λ a, nsubstso_n ((rec:ˡ' Φ)%n a) Φs eq) -:: Φs) eq
    | (∀: V, P)%n => λ Φs eq, ∀ Ψ, neval_gen P (Ψ -:: Φs) eq
    | (∃: V, P)%n => λ Φs eq, ∃ Ψ, neval_gen P (Ψ -:: Φs) eq
    | (%ⁱˢ s)%n => λ _, match s with
        #0 _ => λ eq, match eq with end | +/ _ => λ eq, match eq with end end
    | (%ⁱˡ s)%n => λ _, match s with
        #0 _ => λ eq, match eq with end | +/ _ => λ eq, match eq with end end
    | (%ᵒˢ s)%n => λ Φs eq,
        nevalS_gen (spapply (λ _, npargS_apply) s Φs) eq_refl -[] eq_refl
    | (!ᵒˢ P)%n => λ _  _, nevalS_gen P eq_refl -[] eq_refl
    end%I.
End neval_gen.

Section neval_fp.
  Context (** Iris resources *) `{!nevalG Σ}.

  (** [nevalS_gen]/[neval_gen] typed as a discrete function *)
  Definition nevalS_gen' : (_ -d> _ -d> _ -d> iProp Σ) ->
    _ -d> _ -d> _ -d> _ -d> _ -d> _ -d> _ -d> iProp Σ :=
    λ nev d σ Γ (P : nProp σ Γ), nevalS_gen nev d P.
  Definition neval_gen' : (_ -d> _ -d> _ -d> iProp Σ) ->
    _ -d> _ -d> _ -d> _ -d> _ -d> _ -d> iProp Σ :=
    λ nev d σ Γ (P : nProp σ Γ), neval_gen nev d P.

  (** [nevalS_gen] is contractive *)
  #[export] Instance nevalS_gen_contractive : Contractive nevalS_gen'.
  Proof.
    unfold nevalS_gen'=> i nev nev' nevdist + + + +. fix FIX 4=> d σ Γ.
    case=>/= *>; (try by clear FIX);
      (try by f_equiv=> >; apply (FIX _ _ (_; _)%nctx));
      (try by f_contractive; apply nevdist); apply (FIX _ _ (_; _)%nctx).
  Qed.
  (** [neval_gen] is contractive *)
  #[export] Instance neval_gen_contractive : Contractive neval_gen'.
  Proof.
    unfold neval_gen'=> i nev nev' nevdist + + + +. fix FIX 4=> d σ Γ.
    case=>/= *>; (try by clear FIX);
      (try by f_equiv=> >; apply (FIX _ _ (_; _)%nctx));
      (try by f_contractive; apply nevdist);
      (try by apply (FIX _ _ (_; _)%nctx));
      apply (nevalS_gen_contractive i nev nev' nevdist _ _ (_; _)%nctx).
  Qed.

  (** [neval_pre]: Generator of [neval_fp] *)
  Definition neval_pre
    : (_ -d> _ -d> _ -d> iProp Σ) -> (_ -d> _ -d> _ -d> iProp Σ)
    := λ nev d σ (P : nProp σ (;)), neval_gen' nev d _ _ P -[] eq_refl.
  #[export] Instance neval_pre_contractive : Contractive neval_pre.
  Proof. move=> ???????. by apply neval_gen_contractive. Qed.

  (** [neval_fp]: Fixpoint evaluation of [nProp σ (;)] *)
  Definition neval_fp : _ → ∀ σ, nProp σ (;) → iProp Σ := fixpoint neval_pre.
End neval_fp.

(** The notations [neval] and [neval_env] (as well as [nevalS] and [nevalS_env])
  will be printed in (partial) evaluation, yay! *)

Notation neval_env' Σ d σ Γᵒ P Φs :=
  (@neval_gen Σ _ neval_fp d σ Γᵒ [] P Φs eq_refl) (only parsing).
Notation neval_env d P Φs := (neval_env' _ d _ _ P Φs).
Notation neval' Σ d σ P := (neval_env' Σ d σ [] P -[]) (only parsing).
Notation neval d P := (neval' _ d _ P).
Notation nevalS_env' Σ d Γᵒ P Φs :=
  (@nevalS_gen Σ _ neval_fp d nS Γᵒ [] P eq_refl Φs eq_refl) (only parsing).
Notation nevalS_env d P Φs := (nevalS_env' _ d _ P Φs).
Notation nevalS' Σ d P := (nevalS_env' Σ d [] P -[]) (only parsing).
Notation nevalS d P := (nevalS' _ d P).

Section neval_facts.
  Context (** Iris resources *) `{!nevalG Σ}.

  (** [neval_fp] coincides with [neval] *)
  Lemma neval_fp_neval {d σ P} : neval_fp d σ P ⊣⊢ neval d P.
  Proof. unfold neval_fp. apply (fixpoint_unfold neval_pre). Qed.

  (** [nevalS_gen] coincides with [neval_gen] *)
  Lemma nevalS_gen_neval_gen {nev d σ Γ} {P : nProp σ Γ} {σS Φs eq} :
    nevalS_gen (Σ:=Σ) nev d P σS Φs eq ⊣⊢ neval_gen nev d P Φs eq.
  Proof.
    move: σ Γ P σS Φs eq. fix FIX 3=> σ Γ.
    case=>//= *; try f_equiv=> >; apply (FIX _ (_; _)%nctx).
  Qed.
  (** [nevalS_env] coincides with [neval_env] *)
  Lemma nevalS_env_neval_env {d Γᵒ P Φs} :
    nevalS_env' Σ d Γᵒ P Φs ⊣⊢ neval_env d P Φs.
  Proof. apply (nevalS_gen_neval_gen (Γ:=(Γᵒ; ))). Qed.

  (** Simplify [neval_gen] over [nlarge] *)
  Lemma neval_gen_nlarge {nev d σ Γ} {P : nProp σ Γ} {Φs eq} :
    neval_gen (Σ:=Σ) nev d (nlarge P) Φs eq ⊣⊢ neval_gen nev d P Φs eq.
  Proof.
    move: σ Γ P Φs eq. fix FIX 3=> σ Γ.
    case=>//= *; f_equiv=> >; apply (FIX _ (_; _)%nctx).
  Qed.
  (** Simplify [neval_env] over [nlarge] *)
  Lemma neval_env_nlarge {d σ Γᵒ P Φs} :
    neval_env d (nlarge P) Φs ⊣⊢ neval_env' Σ d σ Γᵒ P Φs.
  Proof. apply (neval_gen_nlarge (Γ:=(Γᵒ; ))). Qed.
End neval_facts.
