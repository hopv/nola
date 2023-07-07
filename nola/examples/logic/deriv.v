(** * Derivability of [nPropL] *)

From nola.examples.logic Require Export intp.
From iris.proofmode Require Export proofmode.

(** ** [nderivsi]: [derivsi] for [nPropL] *)
Definition nderivsi Σ `{!nintpGS Σ} : derivsi :=
  Intpsi (nderivs Σ) (λ d '(Darg i P), ⟦ P ⟧(d)).

(** Notation for [nderivsi] *)
Notation nderivy Σ := (derivy (nderivsi Σ)).
Notation nderiv := (deriv (ITI:=nderivsi _)).
Notation ndsound := (dsound (ITI:=nderivsi _)).
Notation nderiv_sound := (deriv_sound (ITI:=nderivsi _)).

(** Utility for [nderiv] *)
Notation nninvd := (nninv nderiv).
Notation na_nninvd := (na_nninv nderiv).
Notation "⟦ P ⟧{ κ }" := ⟦ P ⟧{κ}(nderiv) (only parsing) : nola_scope.
Notation "⟦ P ⟧" := ⟦ P ⟧(nderiv) : nola_scope.
Notation "⟦ P ⟧ˢ" := ⟦ P ⟧ˢ(nderiv) : nola_scope.
Notation nninv_wsatd := (nninv_wsat nderiv).

Implicit Type P : nPropL (;ᵞ).

(** ** On [nderivy] *)
Section nderivy.
  Context `{!nintpGS Σ, !nderivy Σ ih d}.

  (** [d] is monotone over the level *)
  Lemma derivy_mono_lev {i j P} : i ≤ j → ⸨ P ⸩(d, i) ⊢ ⸨ P ⸩(d, j).
  Proof.
    move/Nat.lt_eq_cases=> [?|<-//]. iApply derivy_map_lev; by [|iIntros].
  Qed.
End nderivy.
