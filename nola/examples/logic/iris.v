(** * Iris preliminaries *)

From nola.examples.logic Require Export prop.
From nola Require Export sintp iris.inv iris.wp.
From nola.examples.heap_lang Require Export primitive_laws.

(** ** [nintpGS]: Iris resources *)

Class nintpGS (Σ : gFunctors) := NintpG {
  nintpGS_heapGS :: heapGS_gen HasNoLc Σ;
  nintpGS_ninvGS :: ninvGS (nPropS (;ᵞ)) Σ;
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

  (** ** [nninv]: [ninv] with a semantic agreement *)
  Definition nninv_def (s : nsintp_ty Σ)
    (i : nat) (N : namespace) (P : nPropL (;ᵞ)) : iProp Σ :=
    ∃ Q, □ ⸨ nlarge Q ={∅}=∗ P ∗ (P ={∅}=∗ nlarge Q) ⸩(s, i) ∗ ninv N Q.
  Definition nninv_aux : seal nninv_def. Proof. by eexists. Qed.
  Definition nninv := nninv_aux.(unseal).
  Lemma nninv_unseal : nninv = nninv_def. Proof. exact nninv_aux.(seal_eq). Qed.
  #[export] Instance nninv_persistent {s i N P} : Persistent (nninv s i N P).
  Proof. rewrite nninv_unseal. apply _. Qed.
End iris.
