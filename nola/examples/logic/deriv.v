(** * Derivability of [nPropL] *)

From nola.examples.logic Require Export intp.
From iris.proofmode Require Export proofmode.

(** ** [nderivsi]: [derivsi] for [nPropL] *)
Definition nderivsi Σ `{!nintpGS Σ} : derivsi :=
  Derivsi (nderivs Σ) (λ d '(Darg _ P), ⟦ P ⟧(d)).

(** Notation for [nderivsi] *)
Notation nderivy Σ := (derivy (nderivsi Σ)).
Notation nderiv := (deriv (DI:=nderivsi _)).
Notation ndsound d := (dsound (DI:=nderivsi _) d ()).
Notation nderiv_sound := (deriv_sound (DI:=nderivsi _)).

(** Utility for [nderiv] *)
Notation nninvd := (nninv nderiv).
Notation na_nninvd := (na_nninv nderiv).
Notation "⟦ P ⟧{ κ }" := ⟦ P ⟧{κ}(nderiv) (only parsing) : nola_scope.
Notation "⟦ P ⟧" := ⟦ P ⟧(nderiv) : nola_scope.
Notation "⟦ P ⟧ˢ" := ⟦ P ⟧ˢ(nderiv) : nola_scope.
Notation nninv_wsatd := (nninv_wsat nderiv).

Implicit Type P : nPropL (;ᵞ).
