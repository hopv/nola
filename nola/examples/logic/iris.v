(** * Iris preliminaries *)

From nola.examples.logic Require Export prop.
From nola Require Export sintp iris.inv.

(** ** [nintpGS]: Iris resources *)

Class nintpGS (Σ : gFunctors) := NintpG {
  nintpGS_invG :: invGS_gen HasNoLc Σ;
  ninppGS_ninvGS :: ninvGS (nPropS (;ᵞ)) Σ;
}.

(** ** For strong interpretation *)

(** [intps] for [nPropL] *)
Definition nintps Σ : intps := Intps nat (λ _, nPropL (;ᵞ)) (iProp Σ).

(** Notation for [nintps] *)
Notation nsintp_ty Σ := (sintp_ty (nintps Σ)).
Notation npsintp_ty Σ := (psintp_ty (nintps Σ)).
Notation "⸨ P ⸩ ( s , i )" := (sunwrap s (Sarg i P%n))
  (format "'[' ⸨  P  ⸩ '/  ' ( s ,  i ) ']'") : nola_scope.

Section iris.
  Context (* Iris resources *) `{!nintpGS Σ}.

  (** ** [nsinv]: Invariant with the semantic agreement *)
  Definition nsinv_def (s : nsintp_ty Σ)
    (i : nat) (N : namespace) (P : nPropL (;ᵞ)) : iProp Σ :=
    ∃ Q, □ ⸨ nlarge Q ={∅}=∗ P ∗ (P ={∅}=∗ nlarge Q) ⸩(s, i) ∗ ninv N Q.
  Definition nsinv_aux : seal nsinv_def. Proof. by eexists. Qed.
  Definition nsinv := nsinv_aux.(unseal).
  Lemma nsinv_unseal : nsinv = nsinv_def. Proof. exact nsinv_aux.(seal_eq). Qed.
  #[export] Instance nsinv_persistent {s i N P} : Persistent (nsinv s i N P).
  Proof. rewrite nsinv_unseal. apply _. Qed.
End iris.
