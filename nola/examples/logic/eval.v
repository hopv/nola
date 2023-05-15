(** * [neval]: Evaluation of [nProp] as [iProp] *)

From nola.examples.logic Require Export subst.
From iris.base_logic.lib Require Import iprop.
Require Import Coq.Program.Equality.

(** Modification of [nsubsti] *)
Definition nsubsti' {σ Γₒ Γᵢ}
  : Γᵢ = [] → nProp σ (; Γₒ ++ Γᵢ) → plist nPred Γₒ → nProp σ (;) :=
  match Γᵢ with _ :: _ => λ σS, match σS with end | [] => λ _ P Φs,
    nsubsti (nProp_rewi P (app_nil_def _)) Φs end.

(** Type of a derivability predicate *)
Notation nderiv_ty := (nat → nPropL (;) * nPropL (;) → Prop).

Section neval_gen.
  Context
    (** Iris resources *) {Σ : gFunctors}
    (** Derivability predicate *) (d : nderiv_ty)
    (** Evaluation used contractively *)
    (nev : nderiv_ty → ∀ σ, nProp σ (;) → iProp Σ).

  (** ** [nevalS_gen P Φs] : Evaluate small [P] under the environment [Φs] *)
  Fixpoint nevalS_gen {σ Γₒ Γᵢ} (P : nProp σ (Γₒ; Γᵢ))
    : σ = nS → plist nPred Γₒ → Γᵢ = [] → iProp Σ :=
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
    | (▷ P)%n => λ _ Φs eq, ▷ nev d _ (nsubsti' eq P Φs)
    | (P ⊢!{i} Q)%n => λ _ Φs eq, ⌜d i (nsubsti' eq P Φs, nsubsti' eq P Φs)⌝
    | ((rec:ₛ' Φ) a)%n => λ _ Φs eq, nevalS_gen (Φ a)
        eq_refl ((λ a, nsubsto ((rec:ₛ' Φ)%n a) Φs eq) -:: Φs) eq
    | ((rec:ₗ' Φ) a)%n => λ σS, match σS with end
    | (∀: V, P)%n => λ σS Φs eq, ∀ Ψ, nevalS_gen P σS (Ψ -:: Φs) eq
    | (∃: V, P)%n => λ σS Φs eq, ∃ Ψ, nevalS_gen P σS (Ψ -:: Φs) eq
    | (%ᵢₛ s)%n => λ _ _, match s with
        #0 _ => λ eq, match eq with end | +/ _ => λ eq, match eq with end end
    | (%ᵢₗ s)%n => λ σS, match σS with end
    | (%ₒₛ s)%n => λ σS, match σS with end
    end%I.

  (** ** [neval_gen P Φs] : Evaluate [P] under the environment [Φs] *)
  Fixpoint neval_gen {σ Γₒ Γᵢ} (P : nProp σ (Γₒ; Γᵢ))
    : plist nPred Γₒ → Γᵢ = [] → iProp Σ :=
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
    | (▷ P)%n => λ Φs eq, ▷ nev d _ (nsubsti' eq P Φs)
    | (P ⊢!{i} Q)%n => λ Φs eq, ⌜d i (nsubsti' eq P Φs, nsubsti' eq P Φs)⌝
    | ((rec:ₛ' Φ) a)%n => λ Φs eq,
        neval_gen (Φ a) ((λ a, nsubsto ((rec:ₛ' Φ)%n a) Φs eq) -:: Φs) eq
    | ((rec:ₗ' Φ) a)%n => λ Φs eq,
        neval_gen (Φ a) ((λ a, nsubsto ((rec:ₗ' Φ)%n a) Φs eq) -:: Φs) eq
    | (∀: V, P)%n => λ Φs eq, ∀ Ψ, neval_gen P (Ψ -:: Φs) eq
    | (∃: V, P)%n => λ Φs eq, ∃ Ψ, neval_gen P (Ψ -:: Φs) eq
    | (%ᵢₛ s)%n => λ _, match s with
        #0 _ => λ eq, match eq with end | +/ _ => λ eq, match eq with end end
    | (%ᵢₗ s)%n => λ _, match s with
        #0 _ => λ eq, match eq with end | +/ _ => λ eq, match eq with end end
    | (%ₒₛ s)%n => λ Φs eq,
        nevalS_gen (cpapply (λ _, npargS_apply) s Φs) eq_refl -[] eq_refl
    end%I.

  (** [nevalS_gen] coincides with [neval_gen] *)
  Lemma nevalS_gen_neval_gen {Γₒ Γᵢ} {P : nPropS (Γₒ; Γᵢ)} {Φs eq} :
    nevalS_gen P eq_refl Φs eq ⊣⊢ neval_gen P Φs eq.
  Proof.
    move: Γₒ Γᵢ P Φs eq. fix FIX 3=> Γₒ Γᵢ P Φs eq.
    dependent destruction P=>//=; f_equiv=> >; apply FIX.
  Qed.
End neval_gen.

Section neval_fp.
  Context
    (** Iris resources *) {Σ : gFunctors}.

  (** [nevalS_gen]/[neval_gen] typed as a discrete function *)
  Definition nevalS_gen' : (_ -d> _ -d> _ -d> iProp Σ) ->
    _ -d> _ -d> _ -d> _ -d> _ -d> _ -d> _ -d> _ -d> iProp Σ :=
    λ nev d σ Γₒ Γᵢ, nevalS_gen d nev (σ:=σ) (Γₒ:=Γₒ) (Γᵢ:=Γᵢ).
  Definition neval_gen' : (_ -d> _ -d> _ -d> iProp Σ) ->
    _ -d> _ -d> _ -d> _ -d> _ -d> _ -d> _ -d> iProp Σ :=
    λ nev d σ Γₒ Γᵢ, neval_gen d nev (σ:=σ) (Γₒ:=Γₒ) (Γᵢ:=Γᵢ).

  (** [nevalS_gen] is contractive *)
  #[export] Instance nevalS_gen_contractive : Contractive nevalS_gen'.
  Proof.
    move=> i nev nev' nevdist + + + + +. fix FIX 5=> d σ Γₒ Γᵢ P σS Φs eq.
    dependent destruction P=>/=; (try by clear FIX);
      (try by f_equiv=> >; apply FIX);
      (try by f_contractive; apply nevdist); apply FIX.
  Qed.
  (** [neval_gen] is contractive *)
  #[export] Instance neval_gen_contractive : Contractive neval_gen'.
  Proof.
    move=> i nev nev' nevdist + + + + +. fix FIX 5=> d σ Γₒ Γᵢ P Φs eq.
    dependent destruction P=>/=; (try by clear FIX);
      (try by f_equiv=> >; apply FIX);
      (try by f_contractive; apply nevdist);
      (try by apply nevalS_gen_contractive); apply FIX.
  Qed.

  (** [neval_pre]: Generator of [neval_fp] *)
  Definition neval_pre
    : (_ -d> _ -d> _ -d> iProp Σ) -> (_ -d> _ -d> _ -d> iProp Σ)
    := λ nev d σ (P : nProp σ (;)), neval_gen d nev P -[] eq_refl.
  #[export] Instance neval_pre_contractive : Contractive neval_pre.
  Proof. move=> ???????. by apply neval_gen_contractive. Qed.

  (** [neval_fp]: Fixpoint evaluation of [nProp σ (;)] *)
  Definition neval_fp : _ → ∀ σ, nProp σ (;) → iProp Σ := fixpoint neval_pre.
End neval_fp.

(** The notations [neval] and [neval_env] will be printed
  in (partial) evaluation, yay! *)

(** [neval d P]: Evaluation of [P : nProp σ (;)] as [iProp Σ]
  under the derivability [d] *)
Notation neval d P := (neval_gen d neval_fp (Γₒ:=[]) P -[] eq_refl).
(** [neval_env d P Φs]: Evaluation of [P : nProp σ (Γₒ; ) as [iProp Σ]
  under the derivability [d] and the environment [Φs : plist nPred Γₒ] *)
Notation neval_env d P Φs := (neval_gen d neval_fp P Φs eq_refl).
(** [neval_def]: Definied [neval] *)
Definition neval_def {Σ σ} d (P : nProp σ (;)) : iProp Σ := neval d P.
Arguments neval_def /.

(** [neval_fp] coincides with [neval] *)
Lemma neval_fp_neval {Σ d σ P} : neval_fp (Σ:=Σ) d σ P ⊣⊢ neval d P.
Proof. unfold neval_fp. apply (fixpoint_unfold neval_pre). Qed.
