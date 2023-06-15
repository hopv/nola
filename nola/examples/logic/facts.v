(** * Facts *)

From nola.examples.logic Require Export sintp.

Section facts.
  Context `{!nintpGS Σ}.

  (** ** Behavior of [nintp] *)
  Fact nintp_pure {κ s φ} : ⟦ ⌜φ⌝ ⟧{κ}(s) ⊣⊢ ⌜φ⌝.
  Proof. done. Qed.
  Fact nintp_persistently {κ s P} : ⟦ □ P ⟧{κ}(s) ⊣⊢ □ ⟦ P ⟧{κ}(s).
  Proof. done. Qed.
  Fact nintp_plainly {κ s P} : ⟦ ■ P ⟧{κ}(s) ⊣⊢ ■ ⟦ P ⟧{κ}(s).
  Proof. done. Qed.
  Fact nintp_bupd {κ s P} : ⟦ |==> P ⟧{κ}(s) ⊣⊢ |==> ⟦ P ⟧{κ}(s).
  Proof. done. Qed.
  Fact nintp_fupd {κ s P E E'} :
    ⟦ |={E,E'}=> P ⟧{κ}(s) ⊣⊢ |={E,E'}=> ⟦ P ⟧{κ}(s).
  Proof. done. Qed.
  Fact nintp_and {κ s P Q} : ⟦ P ∧ Q ⟧{κ}(s) ⊣⊢ ⟦ P ⟧{κ}(s) ∧ ⟦ Q ⟧{κ}(s).
  Proof. done. Qed.
  Fact nintp_or {κ s P Q} : ⟦ P ∨ Q ⟧{κ}(s) ⊣⊢ ⟦ P ⟧{κ}(s) ∨ ⟦ Q ⟧{κ}(s).
  Proof. done. Qed.
  Fact nintp_impl {κ s P Q} : ⟦ P → Q ⟧{κ}(s) ⊣⊢ (⟦ P ⟧{κ}(s) → ⟦ Q ⟧{κ}(s)).
  Proof. done. Qed.
  Fact nintp_sep {κ s P Q} : ⟦ P ∗ Q ⟧{κ}(s) ⊣⊢ ⟦ P ⟧{κ}(s) ∗ ⟦ Q ⟧{κ}(s).
  Proof. done. Qed.
  Fact nintp_wand {κ s P Q} : ⟦ P -∗ Q ⟧{κ}(s) ⊣⊢ (⟦ P ⟧{κ}(s) -∗ ⟦ Q ⟧{κ}(s)).
  Proof. done. Qed.
  Fact nintp_forall {κ s A Φ} : ⟦ ∀' Φ ⟧{κ}(s) ⊣⊢ ∀ x : A, ⟦ Φ x ⟧{κ}(s).
  Proof. done. Qed.
  Fact nintp_exist {κ s A Φ} : ⟦ ∃' Φ ⟧{κ}(s) ⊣⊢ ∃ x : A, ⟦ Φ x ⟧{κ}(s).
  Proof. done. Qed.
  Fact nintp_later {κ s} {P : _ (;ᵞ)} : ⟦ ▷{nil} P ⟧{κ}(s) ⊣⊢ ▷ ⟦ P ⟧(s).
  Proof. by rewrite/= nintp_fp_nintp. Qed.
  Fact nintp_indir {κ s i} {P : _ (;ᵞ)} : ⟦ ○{nil}(i) P ⟧{κ}(s) ⊣⊢ ⸨ P ⸩(s,i).
  Proof. done. Qed.
  Fact nintp_wpw {κ W s st E e Φ} :
    ⟦ WP[W] e @ st ; E {{ Φ }} ⟧{κ}(s) ⊣⊢
      WP[⟦ W ⟧(s)] e @ st ; E {{ v, ⟦ Φ v ⟧(s) }}.
  Proof. done. Qed.
  Fact nintp_twpw {κ W s st E e Φ} :
    ⟦ WP[W] e @ st ; E [{ Φ }] ⟧{κ}(s) ⊣⊢
      WP[⟦ W ⟧(s)] e @ st ; E [{ v, ⟦ Φ v ⟧(s) }].
  Proof. done. Qed.
  Fact nintp_n_forall {κ s V P} : ⟦ ∀: V, P ⟧{κ}(s) ⊣⊢ ∀ Φ, ⟦ P /: Φ ⟧(s).
  Proof. simpl. f_equiv=> ?. by rewrite rew_eq_hwf. Qed.
  Fact nintp_n_exist {κ s V P} : ⟦ ∃: V, P ⟧{κ}(s) ⊣⊢ ∃ Φ, ⟦ P /: Φ ⟧(s).
  Proof. simpl. f_equiv=> ?. by rewrite rew_eq_hwf. Qed.
  Fact nintp_n_recs {κ s A Φ} {a : A} :
    ⟦ rec:ˢ' Φ a ⟧{κ}(s) ⊣⊢ ⟦ Φ a /: rec:ˢ' Φ ⟧(s).
  Proof. by rewrite/= rew_eq_hwf. Qed.
  Fact nintp_n_recl {s A Φ} {a : A} :
    ⟦ rec:ˡ' Φ a ⟧(s) ⊣⊢ ⟦ Φ a /: rec:ˡ' Φ ⟧(s).
  Proof. by rewrite/= rew_eq_hwf. Qed.
  Fact nintp_subus {s P} : ⟦ !ᵘˢ P ⟧(s) ⊣⊢ ⟦ ↑ˡ P ⟧(s).
  Proof. by rewrite/= nintpS_nintp_nlarge. Qed.

  Context `{!nsintpy Σ ih s}.
  Implicit Type (i j : nat) (P Q : nPropL (;ᵞ)).

  (** Make connectives go inside the strong interpretation *)
  Fact sintpy_and {i P Q} :
    ⸨ P ⸩(s, i) ∧ ⸨ Q ⸩(s, i) -∗ ⸨ P ∧ Q ⸩(s, i).
  Proof.
    iIntros "PQ". iApply sintpy_byintp. iIntros (?? _) "/= #to _ _".
    iSplit; iApply "to"; [iDestruct "PQ" as "[$_]"|iDestruct "PQ" as "[_$]"].
  Qed.
  Fact sintpy_or {i P Q} :
    ⸨ P ⸩(s, i) ∨ ⸨ Q ⸩(s, i) -∗ ⸨ P ∨ Q ⸩(s, i).
  Proof.
    iIntros "[?|?]"; iApply sintpy_byintp; iIntros (?? _) "/= #to _ _";
      [iLeft|iRight]; by iApply "to".
  Qed.
  Fact sintpy_forall {i A} {Φ : A → nPropL (;ᵞ)} :
    (∀ a, ⸨ Φ a ⸩(s, i)) -∗ ⸨ ∀' Φ ⸩(s, i).
  Proof.
    iIntros "Φ". iApply sintpy_byintp. iIntros (?? _) "/= #to _ _ %".
    iApply "to". iApply "Φ".
  Qed.
  Fact sintpy_exist {i A} {Φ : A → nPropL (;ᵞ)} :
    (∃ a, ⸨ Φ a ⸩(s, i)) -∗ ⸨ ∃' Φ ⸩(s, i).
  Proof.
    iDestruct 1 as (a) "Φ". iApply sintpy_byintp. iIntros (?? _) "/= #to _ _".
    iExists a. iApply "to". iApply "Φ".
  Qed.
  Fact sintpy_sep {i P Q} :
    ⸨ P ⸩(s, i) ∗ ⸨ Q ⸩(s, i) -∗ ⸨ P ∗ Q ⸩(s, i).
  Proof.
    iIntros "[P Q]". iApply sintpy_byintp. iIntros (?? _) "/= #to _ _".
    iSplitL "P"; by iApply "to".
  Qed.
  Fact sintpy_persistently {i P} : □ ⸨ P ⸩(s, i) -∗ ⸨ □ P ⸩(s, i).
  Proof.
    iIntros "#P". iApply sintpy_byintp. iIntros (?? _) "/= #to _ _ !>".
    by iApply "to".
  Qed.
  Fact sintpy_bupd {i P} : (|==> ⸨ P ⸩(s, i)) -∗ ⸨ |==> P ⸩(s, i).
  Proof.
    iIntros "P". iApply sintpy_byintp. iIntros (?? _) "/= #to _ _".
    by iApply "to".
  Qed.
  Fact sintpy_fupd {i E E' P} :
    (|={E,E'}=> ⸨ P ⸩(s, i)) -∗ ⸨ |={E,E'}=> P ⸩(s, i).
  Proof.
    iIntros "P". iApply sintpy_byintp. iIntros (?? _) "/= #to _ _".
    by iApply "to".
  Qed.
  Fact sintpy_later {i P} : ▷ ⸨ P ⸩(s, i) -∗ ⸨ ▷{nil} P ⸩(s, i).
  Proof.
    iIntros "P". iApply sintpy_byintp. iIntros (?? _) "/= #to _ _".
    rewrite nintp_fp_nintp. by iApply "to".
  Qed.
  Fact sintpy_n_forall {i V} {P : nPropL ([V];ᵞ )} :
    (∀ Φ, ⸨ P /: Φ ⸩(s, i)) -∗ ⸨ ∀: V, P ⸩(s, i).
  Proof.
    iIntros "P". iApply sintpy_byintp. iIntros (?? _) "/= #to _ _ %".
    rewrite rew_eq_hwf. iApply "to". iApply "P".
  Qed.
  Fact sintpy_n_exist {i V} {P : nPropL ([V];ᵞ )} :
    (∃ Φ, ⸨ P /: Φ ⸩(s, i)) -∗ ⸨ ∃: V, P ⸩(s, i).
  Proof.
    iDestruct 1 as (Φ) "P". iApply sintpy_byintp. iIntros (?? _) "/= #to _ _".
    iExists Φ. rewrite rew_eq_hwf. iApply "to". iApply "P".
  Qed.

  (** Introduce [○(i)] *)
  Fact sintpy_indir_intro {i j P} :
    ⸨ P ⸩(s, i) -∗ ⸨ ○{nil}(i) P ⸩(s, j).
  Proof.
    iIntros "P". iApply sintpy_byintp. iIntros (s' _ _) "/= _ #tos' _".
    by iApply "tos'".
  Qed.
  (** Eliminate [○(i)] under a strong interpration of level [j > i] *)
  Fact sintpy_indir_elim {i j P} :
    i < j → ⸨ ○{nil}(i) P ⸩(s, j) -∗ ⸨ P ⸩(s, j).
  Proof.
    move=> ij. iIntros "○P". iApply sintpy_byintp.
    iIntros (s' _ _) "/= #to _ #s'to". iDestruct ("to" with "○P") as "/= ○P".
    by iApply "s'to".
  Qed.
End facts.
