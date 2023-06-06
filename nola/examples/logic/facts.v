(** * Facts *)

From nola.examples.logic Require Export sintp.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import iprop.

Section facts.
  Context `{!nintpGS Σ}.

  (** ** Behavior of [nintp] *)
  Lemma nintp_pure {κ s φ} : ⟦ ⌜φ⌝ ⟧{κ}(s) ⊣⊢ ⌜φ⌝.
  Proof. done. Qed.
  Lemma nintp_persistently {κ s P} : ⟦ □ P ⟧{κ}(s) ⊣⊢ □ ⟦ P ⟧{κ}(s).
  Proof. done. Qed.
  Lemma nintp_plainly {κ s P} : ⟦ ■ P ⟧{κ}(s) ⊣⊢ ■ ⟦ P ⟧{κ}(s).
  Proof. done. Qed.
  Lemma nintp_bupd {κ s P} : ⟦ |==> P ⟧{κ}(s) ⊣⊢ |==> ⟦ P ⟧{κ}(s).
  Proof. done. Qed.
  Lemma nintp_fupd {κ s P E E'} :
    ⟦ |={E,E'}=> P ⟧{κ}(s) ⊣⊢ |={E,E'}=> ⟦ P ⟧{κ}(s).
  Proof. done. Qed.
  Lemma nintp_and {κ s P Q} : ⟦ P ∧ Q ⟧{κ}(s) ⊣⊢ ⟦ P ⟧{κ}(s) ∧ ⟦ Q ⟧{κ}(s).
  Proof. done. Qed.
  Lemma nintp_or {κ s P Q} : ⟦ P ∨ Q ⟧{κ}(s) ⊣⊢ ⟦ P ⟧{κ}(s) ∨ ⟦ Q ⟧{κ}(s).
  Proof. done. Qed.
  Lemma nintp_impl {κ s P Q} : ⟦ P → Q ⟧{κ}(s) ⊣⊢ (⟦ P ⟧{κ}(s) → ⟦ Q ⟧{κ}(s)).
  Proof. done. Qed.
  Lemma nintp_sep {κ s P Q} : ⟦ P ∗ Q ⟧{κ}(s) ⊣⊢ ⟦ P ⟧{κ}(s) ∗ ⟦ Q ⟧{κ}(s).
  Proof. done. Qed.
  Lemma nintp_wand {κ s P Q} : ⟦ P -∗ Q ⟧{κ}(s) ⊣⊢ (⟦ P ⟧{κ}(s) -∗ ⟦ Q ⟧{κ}(s)).
  Proof. done. Qed.
  Lemma nintp_forall {κ s A Φ} : ⟦ ∀' Φ ⟧{κ}(s) ⊣⊢ ∀ x : A, ⟦ Φ x ⟧{κ}(s).
  Proof. done. Qed.
  Lemma nintp_exist {κ s A Φ} : ⟦ ∃' Φ ⟧{κ}(s) ⊣⊢ ∃ x : A, ⟦ Φ x ⟧{κ}(s).
  Proof. done. Qed.
  Lemma nintp_later {κ s} {P : _ (;ᵞ)} : ⟦ ▷{nil} P ⟧{κ}(s) ⊣⊢ ▷ ⟦ P ⟧(s).
  Proof. by rewrite/= nintp_fp_nintp. Qed.
  Lemma nintp_indir {κ s i} {P : _ (;ᵞ)} : ⟦ ○{nil}(i) P ⟧{κ}(s) ⊣⊢ ⸨ P ⸩(s,i).
  Proof. done. Qed.
  Lemma nintp_wp {s st E e Φ} :
    ⟦ n_wp st E e Φ ⟧(s) ⊣⊢ wpw (nninv_wsat s) st E e (λ v, ⟦ Φ v ⟧(s)).
  Proof. done. Qed.
  Lemma nintp_twp {s st E e Φ} :
    ⟦ n_twp st E e Φ ⟧(s) ⊣⊢ twpw (nninv_wsat s) st E e (λ v, ⟦ Φ v ⟧(s)).
  Proof. done. Qed.
  Lemma nintp_n_forall {κ s V P} : ⟦ ∀: V, P ⟧{κ}(s) ⊣⊢ ∀ Φ, ⟦ P /: Φ ⟧(s).
  Proof. simpl. f_equiv=> ?. by rewrite rew_eq_hwf. Qed.
  Lemma nintp_n_exist {κ s V P} : ⟦ ∃: V, P ⟧{κ}(s) ⊣⊢ ∃ Φ, ⟦ P /: Φ ⟧(s).
  Proof. simpl. f_equiv=> ?. by rewrite rew_eq_hwf. Qed.
  Lemma nintp_n_recs {κ s A Φ} {a : A} :
    ⟦ rec:ˢ' Φ a ⟧{κ}(s) ⊣⊢ ⟦ Φ a /: rec:ˢ' Φ ⟧(s).
  Proof. by rewrite/= rew_eq_hwf. Qed.
  Lemma nintp_n_recl {s A Φ} {a : A} :
    ⟦ rec:ˡ' Φ a ⟧(s) ⊣⊢ ⟦ Φ a /: rec:ˡ' Φ ⟧(s).
  Proof. by rewrite/= rew_eq_hwf. Qed.
  Lemma nintp_subus {s P} : ⟦ !ᵘˢ P ⟧(s) ⊣⊢ ⟦ ↑ˡ P ⟧(s).
  Proof. by rewrite/= nintpS_nintp_nlarge. Qed.

  Context `{!nsintpy Σ σ}.
  Implicit Type (i j : nat) (P Q : nPropL (;ᵞ)).

  (** Make connectives go inside the strong interpretation *)
  Lemma sintpy_and {i s P Q} :
    ⸨ P ⸩(σ s, i) ∧ ⸨ Q ⸩(σ s, i) -∗ ⸨ P ∧ Q ⸩(σ s, i).
  Proof.
    iIntros "PQ". iApply sintpy_byintp. iIntros (? _) "/= #to _ _".
    iSplit; iApply "to"; [iDestruct "PQ" as "[$_]"|iDestruct "PQ" as "[_$]"].
  Qed.
  Lemma sintpy_or {i s P Q} :
    ⸨ P ⸩(σ s, i) ∨ ⸨ Q ⸩(σ s, i) -∗ ⸨ P ∨ Q ⸩(σ s, i).
  Proof.
    iIntros "[?|?]"; iApply sintpy_byintp; iIntros (? _) "/= #to _ _";
      [iLeft|iRight]; by iApply "to".
  Qed.
  Lemma sintpy_forall {i s A} {Φ : A → nPropL (;ᵞ)} :
    (∀ a, ⸨ Φ a ⸩(σ s, i)) -∗ ⸨ ∀' Φ ⸩(σ s, i).
  Proof.
    iIntros "Φ". iApply sintpy_byintp. iIntros (? _) "/= #to _ _". iIntros (a).
    iApply "to". iApply "Φ".
  Qed.
  Lemma sintpy_exist {i s A} {Φ : A → nPropL (;ᵞ)} :
    (∃ a, ⸨ Φ a ⸩(σ s, i)) -∗ ⸨ ∃' Φ ⸩(σ s, i).
  Proof.
    iDestruct 1 as (a) "Φ". iApply sintpy_byintp. iIntros (? _) "/= #to _ _".
    iExists a. iApply "to". iApply "Φ".
  Qed.
  Lemma sintpy_sep {i s P Q} :
    ⸨ P ⸩(σ s, i) ∗ ⸨ Q ⸩(σ s, i) -∗ ⸨ P ∗ Q ⸩(σ s, i).
  Proof.
    iIntros "[P Q]". iApply sintpy_byintp. iIntros (? _) "/= #to _ _".
    iSplitL "P"; by iApply "to".
  Qed.
  Lemma sintpy_persistently {i s P} : □ ⸨ P ⸩(σ s, i) -∗ ⸨ □ P ⸩(σ s, i).
  Proof.
    iIntros "#P". iApply sintpy_byintp. iIntros (? _) "/= #to _ _ !#".
    by iApply "to".
  Qed.
  Lemma sintpy_bupd {i s P} : (|==> ⸨ P ⸩(σ s, i)) -∗ ⸨ |==> P ⸩(σ s, i).
  Proof.
    iIntros "P". iApply sintpy_byintp. iIntros (? _) "/= #to _ _".
    by iApply "to".
  Qed.
  Lemma sintpy_fupd {i s E E' P} :
    (|={E,E'}=> ⸨ P ⸩(σ s, i)) -∗ ⸨ |={E,E'}=> P ⸩(σ s, i).
  Proof.
    iIntros "P". iApply sintpy_byintp. iIntros (? _) "/= #to _ _".
    by iApply "to".
  Qed.
  Lemma sintpy_later {i s P} : ▷ ⸨ P ⸩(σ s, i) -∗ ⸨ ▷{nil} P ⸩(σ s, i).
  Proof.
    iIntros "P". iApply sintpy_byintp. iIntros (? _) "/= #to _ _".
    rewrite nintp_fp_nintp. by iApply "to".
  Qed.
  Lemma sintpy_n_forall {i s V} {P : nPropL ([V];ᵞ )} :
    (∀ Φ, ⸨ P /: Φ ⸩(σ s, i)) -∗ ⸨ ∀: V, P ⸩(σ s, i).
  Proof.
    iIntros "P". iApply sintpy_byintp. iIntros (? _) "/= #to _ _". iIntros (Ψ).
    rewrite rew_eq_hwf. iApply "to". iApply "P".
  Qed.
  Lemma sintpy_n_exist {i s V} {P : nPropL ([V];ᵞ )} :
    (∃ Φ, ⸨ P /: Φ ⸩(σ s, i)) -∗ ⸨ ∃: V, P ⸩(σ s, i).
  Proof.
    iDestruct 1 as (Φ) "P". iApply sintpy_byintp. iIntros (? _) "/= #to _ _".
    iExists Φ. rewrite rew_eq_hwf. iApply "to". iApply "P".
  Qed.

  (** Introduce [○(i)] *)
  Lemma sintpy_indir_intro {i j s P} :
    ⸨ P ⸩(σ $∨ˢ s, i) -∗ ⸨ ○{nil}(i) P ⸩(σ s, j).
  Proof.
    iIntros "P". iApply sintpy_byintp. iIntros (σ' _) "/= _ #toσ' _".
    by iApply "toσ'".
  Qed.
  (** Eliminate [○(i)] under a strong interpration of level [j > i] *)
  Lemma sintpy_indir_elim {i j s P} :
    i < j → ⸨ ○{nil}(i) P ⸩(σ s, j) -∗ ⸨ P ⸩(σ s, j).
  Proof.
    move=> ij. iIntros "○P". iApply sintpy_byintp.
    iIntros (σ' _) "/= #to #toσ' #σ'to". iDestruct ("to" with "○P") as "/= ○P".
    by iApply "σ'to".
  Qed.
End facts.
