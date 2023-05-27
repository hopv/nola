(** * Facts *)

From nola.examples.logic Require Export sintp.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import iprop.

Section facts.
  Context `{!nintpGS Σ}.

  (** ** Behavior of [nintp] for featured connectives *)
  Lemma nintp_later {κ s} {P : _ (;ᵞ)} : ⟦ ▷{nil} P ⟧{κ}(s) ⊣⊢ ▷ ⟦ P ⟧(s).
  Proof. by rewrite/= nintp_fp_nintp. Qed.
  Lemma nintp_indir {κ s i} {P : _ (;ᵞ)} :
    ⟦ ○{nil}(i) P ⟧{κ}(s) ⊣⊢ ⸨ P ⸩(s,i).
  Proof. done. Qed.
  Lemma nintp_wp {s st E e Φ} :
    ⟦ n_wp st E e Φ ⟧(s) ⊣⊢ wpw (nninv_wsat s) st E e (λ v, ⟦ Φ v ⟧(s)).
  Proof. done. Qed.
  Lemma nintp_twp {s st E e Φ} :
    ⟦ n_twp st E e Φ ⟧(s) ⊣⊢ twpw (nninv_wsat s) st E e (λ v, ⟦ Φ v ⟧(s)).
  Proof. done. Qed.
  Lemma nintp_n_forall {κ s V P} :
    ⟦ ∀: V, P ⟧{κ}(s) ⊣⊢ ∀ Φ, ⟦ P /: Φ ⟧(s).
  Proof. simpl. f_equiv=> ?. by rewrite rew_eq_hwf. Qed.
  Lemma nintp_n_exist {κ s V P} :
    ⟦ ∃: V, P ⟧{κ}(s) ⊣⊢ ∃ Φ, ⟦ P /: Φ ⟧(s).
  Proof. simpl. f_equiv=> ?. by rewrite rew_eq_hwf. Qed.
  Lemma nintp_n_recs {κ s A Φ} {a : A} :
    ⟦ rec:ˢ' Φ a ⟧{κ}(s) ⊣⊢ ⟦ nsubst (Φ a) (rec:ˢ' Φ) ⟧(s).
  Proof. by rewrite/= rew_eq_hwf. Qed.
  Lemma nintp_n_recl {s A Φ} {a : A} :
    ⟦ rec:ˡ' Φ a ⟧(s) ⊣⊢ ⟦ nsubst (Φ a) (rec:ˡ' Φ) ⟧(s).
  Proof. by rewrite/= rew_eq_hwf. Qed.
  Lemma nintp_subus {s P} : ⟦ !ᵘˢ P ⟧(s) ⊣⊢ ⟦ ↑ˡ P ⟧(s).
  Proof. by rewrite/= nintpS_nintp_nlarge. Qed.
End facts.
