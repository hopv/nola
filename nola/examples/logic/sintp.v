(** * Strong interpretation of [nProp] *)

From nola.examples.logic Require Export intp.
From nola.util Require Export wft.
From iris.proofmode Require Export proofmode.

(** ** [nintpsi]: [inpsi] for [nPropL] *)
Definition nintpsi Σ `{!nintpGS Σ} : intpsi :=
  Intpsi (nintps Σ) (λ s '(Sarg i P), ⟦ P ⟧(s)).

(** Notation for [nintpsi] *)
Notation nsintpy Σ := (sintpy (nintpsi Σ)).
Notation nsintp := (sintp (ITI:=nintpsi _)).
Notation nsintpb := (nsintp ⊥ˢ).
Notation nssound := (ssound (ITI:=nintpsi _)).
Notation nsintp_sound := (sintp_sound (ITI:=nintpsi _)).

(** Utility for [nsintp] *)
Notation nninvs := (nninv nsintpb).
Notation na_nninvs := (na_nninv nsintpb).
Notation "⟦ P ⟧{ κ }" := ⟦ P ⟧{κ}(nsintpb) (only parsing) : nola_scope.
Notation "⟦ P ⟧" := ⟦ P ⟧(nsintpb) : nola_scope.
Notation "⟦ P ⟧ˢ" := ⟦ P ⟧ˢ(nsintpb) : nola_scope.
Notation nninv_wsats := (nninv_wsat nsintpb).

Implicit Type P : nPropL (;ᵞ).

(** ** On [nsintpy] *)
Section nsintpy.
  Context `{!nintpGS Σ, !nsintpy Σ σ}.

  (** [σ s] is monotone over the level *)
  Lemma sintpy_mono_lev {i j s P} : i ≤ j → ⸨ P ⸩(σ s, i) -∗ ⸨ P ⸩(σ s, j).
  Proof.
    move/Nat.lt_eq_cases=> [ij|<-]; [|by iIntros]. iIntros "Pi".
    iApply sintpy_map_lev; by [|iIntros|iLeft].
  Qed.
End nsintpy.
