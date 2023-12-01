(** * Derivability of [nPropL] *)

From nola.examples.logic Require Export intp.
From iris.proofmode Require Export proofmode.

(** ** [nderivsi]: [derivsi] for [nPropL] *)
Canonical nderivsi `{!nintpGS Σ} := Derivsi (nderivs Σ) (λ δ P, ⟦ P ⟧(δ)).

(** Notation for [nderivsi] *)
Notation nDeriv := (Deriv nderivsi).
Notation nderiv := (deriv (DI:=nderivsi)).
Notation nderiv_sound := (deriv_sound (DI:=nderivsi)).

(** Utility for [nderiv] *)
Notation "⟦ P ⟧{ κ }" := ⟦ P ⟧{κ}(nderiv) (only parsing) : nola_scope.
Notation "⟦ P ⟧" := ⟦ P ⟧(nderiv) : nola_scope.
Notation "⟦ P ⟧ˢ" := ⟦ P ⟧ˢ(nderiv) : nola_scope.
Notation "⸨ P ⸩" := ⸨ P ⸩(nderiv) (format "⸨  P  ⸩") : nola_scope.

Notation sinv_wsatd := (sinv_wsat' nderiv).
Notation inv_wsatd := (inv_wsat' nderiv).
Notation na_inv_wsatd := (na_inv_wsat' nderiv).
Notation pborrow_wsatd M := (pborrow_wsat' M nderiv).

Notation sinvd := (sinv nderiv).
Notation ninvd := (ninv nderiv).
Notation na_ninvd := (na_ninv nderiv).

Notation borcd := (borc nderiv).
Notation bord := (bor nderiv).
Notation obord := (obor nderiv).
Notation lendd := (lend nderiv).
Notation fbord := (fbor nderiv).
Notation pborcd := (pborc nderiv).
Notation pbord := (pbor nderiv).
Notation pobord := (pobor nderiv).
Notation plendd := (plend nderiv).
Notation fbor_pointstod α l v := (fbor_pointsto nderiv α l v).
Notation "l ↦[ α ] v" := (fbor_pointstod α l v)
  (at level 20, format "l  ↦[ α ]  v") : bi_scope.
