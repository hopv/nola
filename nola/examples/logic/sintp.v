(** * Strong interpretation of [nProp] *)

From nola.examples.logic Require Export intp.
From nola Require Export util.wft.
From iris.proofmode Require Import tactics.

(** ** [nintpsi]: [inpsi] for [nPropL] *)
Definition nintpsi Σ `{!nintpGS Σ} : intpsi :=
  Intpsi (nintps Σ) (λ s '(Sarg i P), ⟦ P ⟧(s)).

(** Notation for [nintpsi] *)
Notation nsintpy Σ := (sintpy (nintpsi Σ)).
Notation nsintp Σ := (sintp (nintpsi Σ)).

Implicit Type (i j : nat) (P Q : nPropL (;ᵞ)).

(** ** Lemmas about [nsintpy] *)
Section lemmas.
  Context `{!nintpGS Σ, !nsintpy Σ σ}.

  (** [σ s] is monotone over the index *)
  Lemma sintpy_up {i j s P} : i ≤ j → ⸨ P ⸩(σ s, i) -∗ ⸨ P ⸩(σ s, j).
  Proof.
    move/Nat.lt_eq_cases=> [|<-]; [|by iIntros]=> ij. iIntros "Pi".
    iApply sintpy_byintp. iIntros (? _) "_ #toσ' #σ'to".
    iApply ("σ'to" $! i ij). iApply "toσ'". by iLeft.
  Qed.

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
    (∀ Φ, ⸨ nsubst P Φ ⸩(σ s, i)) -∗ ⸨ ∀: V, P ⸩(σ s, i).
  Proof.
    iIntros "P". iApply sintpy_byintp. iIntros (? _) "/= #to _ _". iIntros (Ψ).
    rewrite rew_eq_hwf. iApply "to". iApply "P".
  Qed.
  Lemma sintpy_n_exist {i s V} {P : nPropL ([V];ᵞ )} :
    (∃ Φ, ⸨ nsubst P Φ ⸩(σ s, i)) -∗ ⸨ ∃: V, P ⸩(σ s, i).
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
End lemmas.
