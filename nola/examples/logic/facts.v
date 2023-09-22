(** * Facts *)

From nola.examples.logic Require Export deriv.

Section facts.
  Context `{!nintpGS Σ}.

  (** ** Behavior of [nintp] *)
  Fact nintp_pure {κ d φ} : ⟦ ⌜φ⌝ ⟧{κ}(d) ⊣⊢ ⌜φ⌝.
  Proof. done. Qed.
  Fact nintp_persistently {κ d P} : ⟦ □ P ⟧{κ}(d) ⊣⊢ □ ⟦ P ⟧{κ}(d).
  Proof. done. Qed.
  Fact nintp_plainly {κ d P} : ⟦ ■ P ⟧{κ}(d) ⊣⊢ ■ ⟦ P ⟧{κ}(d).
  Proof. done. Qed.
  Fact nintp_bupd {κ d P} : ⟦ |==> P ⟧{κ}(d) ⊣⊢ |==> ⟦ P ⟧{κ}(d).
  Proof. done. Qed.
  Fact nintp_fupd {κ d P E E'} :
    ⟦ |={E,E'}=> P ⟧{κ}(d) ⊣⊢ |={E,E'}=> ⟦ P ⟧{κ}(d).
  Proof. done. Qed.
  Fact nintp_and {κ d P Q} : ⟦ P ∧ Q ⟧{κ}(d) ⊣⊢ ⟦ P ⟧{κ}(d) ∧ ⟦ Q ⟧{κ}(d).
  Proof. done. Qed.
  Fact nintp_or {κ d P Q} : ⟦ P ∨ Q ⟧{κ}(d) ⊣⊢ ⟦ P ⟧{κ}(d) ∨ ⟦ Q ⟧{κ}(d).
  Proof. done. Qed.
  Fact nintp_impl {κ d P Q} : ⟦ P → Q ⟧{κ}(d) ⊣⊢ (⟦ P ⟧{κ}(d) → ⟦ Q ⟧{κ}(d)).
  Proof. done. Qed.
  Fact nintp_sep {κ d P Q} : ⟦ P ∗ Q ⟧{κ}(d) ⊣⊢ ⟦ P ⟧{κ}(d) ∗ ⟦ Q ⟧{κ}(d).
  Proof. done. Qed.
  Fact nintp_wand {κ d P Q} : ⟦ P -∗ Q ⟧{κ}(d) ⊣⊢ (⟦ P ⟧{κ}(d) -∗ ⟦ Q ⟧{κ}(d)).
  Proof. done. Qed.
  Fact nintp_forall {κ d A Φ} : ⟦ ∀' Φ ⟧{κ}(d) ⊣⊢ ∀ x : A, ⟦ Φ x ⟧{κ}(d).
  Proof. done. Qed.
  Fact nintp_exist {κ d A Φ} : ⟦ ∃' Φ ⟧{κ}(d) ⊣⊢ ∃ x : A, ⟦ Φ x ⟧{κ}(d).
  Proof. done. Qed.
  Fact nintp_later {κ d} {P : _ (;ᵞ)} : ⟦ ▷{nil} P ⟧{κ}(d) ⊣⊢ ▷ ⟦ P ⟧(d).
  Proof. by rewrite/= nintp_fp_nintp. Qed.
  Fact nintp_indir {κ d} {P : _ (;ᵞ)} : ⟦ ○{nil} P ⟧{κ}(d) ⊣⊢ ⸨ P ⸩(d).
  Proof. done. Qed.
  Fact nintp_ag {κ d γ} {P : _ (;ᵞ)} : ⟦ n_ag γ P ⟧{κ}(d) ⊣⊢ nag γ P.
  Proof. done. Qed.
  Fact nintp_inv {κ d N} {P : _ (;ᵞ)} : ⟦ n_inv N P ⟧{κ}(d) ⊣⊢ nninv d N P.
  Proof. done. Qed.
  Fact nintp_na_inv {κ d p N} {P : _ (;ᵞ)} :
    ⟦ n_na_inv p N P ⟧{κ}(d) ⊣⊢ na_nninv d p N P.
  Proof. done. Qed.
  Fact nintp_wpw {κ d W s E e Φ} :
    ⟦ WP[W] e @ s ; E {{ Φ }} ⟧{κ}(d) ⊣⊢
      WP[⟦ W ⟧(d)] e @ s ; E {{ v, ⟦ Φ v ⟧(d) }}.
  Proof. done. Qed.
  Fact nintp_twpw {κ d W s E e Φ} :
    ⟦ WP[W] e @ s ; E [{ Φ }] ⟧{κ}(d) ⊣⊢
      WP[⟦ W ⟧(d)] e @ s ; E [{ v, ⟦ Φ v ⟧(d) }].
  Proof. done. Qed.
  Fact nintp_n_forall {κ d V P} : ⟦ ∀: V, P ⟧{κ}(d) ⊣⊢ ∀ Φ, ⟦ P /: Φ ⟧(d).
  Proof. simpl. f_equiv=> ?. by rewrite rew_eq_hwf. Qed.
  Fact nintp_n_exist {κ d V P} : ⟦ ∃: V, P ⟧{κ}(d) ⊣⊢ ∃ Φ, ⟦ P /: Φ ⟧(d).
  Proof. simpl. f_equiv=> ?. by rewrite rew_eq_hwf. Qed.
  Fact nintp_n_recs {κ d A Φ} {a : A} :
    ⟦ rec:ˢ' Φ a ⟧{κ}(d) ⊣⊢ ⟦ Φ a /: rec:ˢ' Φ ⟧(d).
  Proof. by rewrite/= rew_eq_hwf. Qed.
  Fact nintp_n_recl {d A Φ} {a : A} :
    ⟦ rec:ˡ' Φ a ⟧(d) ⊣⊢ ⟦ Φ a /: rec:ˡ' Φ ⟧(d).
  Proof. by rewrite/= rew_eq_hwf. Qed.
  Fact nintp_subus {d P} : ⟦ !ᵘˢ P ⟧(d) ⊣⊢ ⟦ ↑ˡ P ⟧(d).
  Proof. by rewrite/= nintpS_nintp_nlarge. Qed.

  (** On [nag] *)
  Lemma nag_agree {γ} {P Q : _ (;ᵞ)} : nag γ P -∗ nag γ Q -∗ ⌜P = Q⌝.
  Proof.
    iIntros "P Q". iCombine "P Q" as "o".
    iDestruct (own_valid with "o") as %v. by apply to_agree_op_valid_L in v.
  Qed.

  Context `{!nderivy Σ ih d}.
  Implicit Type P Q : nPropL (;ᵞ).

  (** Make connectives go inside the derivability *)
  Fact derivy_and {P Q} :
    ⸨ P ⸩(d) ∧ ⸨ Q ⸩(d) -∗ ⸨ P ∧ Q ⸩(d).
  Proof.
    iIntros "PQ". iApply derivy_byintp. iIntros (?? _) "/= #to _ _".
    iSplit; iApply "to"; [iDestruct "PQ" as "[$_]"|iDestruct "PQ" as "[_$]"].
  Qed.
  Fact derivy_or {P Q} :
    ⸨ P ⸩(d) ∨ ⸨ Q ⸩(d) -∗ ⸨ P ∨ Q ⸩(d).
  Proof.
    iIntros "[?|?]"; iApply derivy_byintp; iIntros (?? _) "/= #to _ _";
      [iLeft|iRight]; by iApply "to".
  Qed.
  Fact derivy_forall {A} {Φ : A → nPropL (;ᵞ)} :
    (∀ a, ⸨ Φ a ⸩(d)) -∗ ⸨ ∀' Φ ⸩(d).
  Proof.
    iIntros "Φ". iApply derivy_byintp. iIntros (?? _) "/= #to _ _ %".
    iApply "to". iApply "Φ".
  Qed.
  Fact derivy_exist {A} {Φ : A → nPropL (;ᵞ)} :
    (∃ a, ⸨ Φ a ⸩(d)) -∗ ⸨ ∃' Φ ⸩(d).
  Proof.
    iDestruct 1 as (a) "Φ". iApply derivy_byintp. iIntros (?? _) "/= #to _ _".
    iExists a. iApply "to". iApply "Φ".
  Qed.
  Fact derivy_sep {P Q} :
    ⸨ P ⸩(d) ∗ ⸨ Q ⸩(d) -∗ ⸨ P ∗ Q ⸩(d).
  Proof.
    iIntros "[P Q]". iApply derivy_byintp. iIntros (?? _) "/= #to _ _".
    iSplitL "P"; by iApply "to".
  Qed.
  Fact derivy_persistently {P} : □ ⸨ P ⸩(d) -∗ ⸨ □ P ⸩(d).
  Proof.
    iIntros "#P". iApply derivy_byintp. iIntros (?? _) "/= #to _ _ !>".
    by iApply "to".
  Qed.
  Fact derivy_bupd {P} : (|==> ⸨ P ⸩(d)) -∗ ⸨ |==> P ⸩(d).
  Proof.
    iIntros "P". iApply derivy_byintp. iIntros (?? _) "/= #to _ _".
    by iApply "to".
  Qed.
  Fact derivy_fupd {E E' P} :
    (|={E,E'}=> ⸨ P ⸩(d)) -∗ ⸨ |={E,E'}=> P ⸩(d).
  Proof.
    iIntros "P". iApply derivy_byintp. iIntros (?? _) "/= #to _ _".
    by iApply "to".
  Qed.
  Fact derivy_later {P} : ▷ ⸨ P ⸩(d) -∗ ⸨ ▷{nil} P ⸩(d).
  Proof.
    iIntros "P". iApply derivy_byintp. iIntros (?? _) "/= #to _ _".
    rewrite nintp_fp_nintp. by iApply "to".
  Qed.
  Fact derivy_n_forall {V} {P : nPropL ([V];ᵞ )} :
    (∀ Φ, ⸨ P /: Φ ⸩(d)) -∗ ⸨ ∀: V, P ⸩(d).
  Proof.
    iIntros "P". iApply derivy_byintp. iIntros (?? _) "/= #to _ _ %".
    rewrite rew_eq_hwf. iApply "to". iApply "P".
  Qed.
  Fact derivy_n_exist {V} {P : nPropL ([V];ᵞ )} :
    (∃ Φ, ⸨ P /: Φ ⸩(d)) -∗ ⸨ ∃: V, P ⸩(d).
  Proof.
    iDestruct 1 as (Φ) "P". iApply derivy_byintp. iIntros (?? _) "/= #to _ _".
    iExists Φ. rewrite rew_eq_hwf. iApply "to". iApply "P".
  Qed.

  (** Introduce [○] *)
  Fact derivy_indir_intro {P} : ⸨ P ⸩(d) -∗ ⸨ ○{nil} P ⸩(d).
  Proof.
    iIntros "P". iApply derivy_byintp. iIntros (d' _ _) "/= _ #tod' _".
    by iApply "tod'".
  Qed.
End facts.
