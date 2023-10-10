(** * Derivability of [nPropL] *)

From nola.examples.logic Require Export intp.
From iris.proofmode Require Export proofmode.

(** ** [nderivsi]: [derivsi] for [nPropL] *)
Canonical nderivsi `{!nintpGS Σ} :=
  Derivsi (nderivs Σ) (λ δ '(Darg _ P), ⟦ P ⟧(δ)).

(** Notation for [nderivsi] *)
Notation nderivy := (derivy nderivsi).
Notation nderiv := (deriv (DI:=nderivsi)).
Notation nderiv_sound := (deriv_sound (DI:=nderivsi)).

(** Utility for [nderiv] *)
Notation ninvd := (ninv nderiv).
Notation na_ninvd := (na_ninv nderiv).
Notation "⟦ P ⟧{ κ }" := ⟦ P ⟧{κ}(nderiv) (only parsing) : nola_scope.
Notation "⟦ P ⟧" := ⟦ P ⟧(nderiv) : nola_scope.
Notation "⟦ P ⟧ˢ" := ⟦ P ⟧ˢ(nderiv) : nola_scope.
Notation inv_wsatd := (inv_wsat' nderiv).
Notation na_inv_wsatd := (na_inv_wsat' nderiv).
Notation borrow_wsatd W E := (borrow_wsat' nderiv W E).

Implicit Type P : nPropL (;ᵞ).
