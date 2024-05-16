(** * Utility on Iris *)
From nola Require Import upd.
From iris.proofmode Require Import proofmode.

Section util.
  Context `{!BiBUpd PROP}.

  (** ** Accessor getting [P] from [Q] via the modality [M] *)
  Definition acsr M P Q : PROP := Q -∗ M (P ∗ (P -∗ M Q))%I.

  (** [acsr] is proper *)
  #[export] Instance acsr_ne `{!GenUpd M} : NonExpansive2 (acsr M).
  Proof. solve_proper. Qed.

  (** [acsr] is reflexive and transitive *)
  Lemma acsr_refl `{!GenUpd M} {P} : ⊢ acsr M P P.
  Proof. by iIntros "$ !> $". Qed.
  Lemma acsr_trans `{!GenUpd M} {P Q R} :
    acsr M P Q -∗ acsr M Q R -∗ acsr M P R.
  Proof.
    iIntros "QPQ RQR R". iMod ("RQR" with "R") as "[Q QR]".
    iMod ("QPQ" with "Q") as "[$ PQ]". iIntros "!> P".
    iMod ("PQ" with "P") as "Q". by iApply "QR".
  Qed.

  (** [acsr] over [∗] *)
  Lemma acsr_sep_l `{!GenUpd M} {P Q} : ⊢ acsr M P (P ∗ Q).
  Proof. by iIntros "[$$] !> $". Qed.
  Lemma acsr_sep_r `{!GenUpd M} {P Q} : ⊢ acsr M Q (P ∗ Q).
  Proof. by iIntros "[$$] !> $". Qed.
End util.
