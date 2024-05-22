(** * Order theory *)

From nola.util Require Export order.
From iris.bi Require Import bi.
From iris.proofmode Require Import proofmode.

Implicit Type PROP : bi.

(** ** Pre-order for [PROP] *)
Program Canonical biPro PROP := Proty PROP (⊢) (⊣⊢) _ _.
Next Obligation.
  move=> >. split; by [move/bi.equiv_entails|move=> ?; apply bi.equiv_entails].
Qed.

(** ** [biPro] has the top, bottom, meet and join *)
#[export] Program Instance otop_bi {PROP} : Otop PROP := OTOP True%I _.
Next Obligation. by iIntros. Qed.
#[export] Program Instance obot_bi {PROP} : Obot PROP := OBOT False%I _.
Next Obligation. by iIntros. Qed.
#[export] Program Instance bin_meet_bi {PROP} : BinMeet PROP :=
  BIN_MEET (∧)%I _ _ _.
Next Obligation. move=> *. by iIntros "[? _]". Qed.
Next Obligation. move=> *. by iIntros "[_ ?]". Qed.
Next Obligation.
  move=> > le le'. iIntros "?". iSplit; by [iApply le|iApply le'].
Qed.
#[export] Program Instance bin_join_bi {PROP} : BinJoin PROP :=
  BIN_JOIN (∨)%I _ _ _.
Next Obligation. move=> *. iIntros "?". by iLeft. Qed.
Next Obligation. move=> *. iIntros "?". by iRight. Qed.
Next Obligation.
  move=> > le le'. iIntros "[?|?]"; by [iApply le|iApply le'].
Qed.
#[export] Program Instance big_meet_bi {PROP} : BigMeet PROP :=
  BIG_MEET (λ _ S Φ, ∀ a, ⌜S a⌝ → Φ a)%I _ _.
Next Obligation. move=> *. iIntros "to". by iApply "to". Qed.
Next Obligation. move=> > to. iIntros "?" (??). iStopProof. by apply to. Qed.
#[export] Program Instance big_join_bi {PROP} : BigJoin PROP :=
  BIG_JOIN (λ _ S Φ, ∃ a, ⌜S a⌝ ∧ Φ a)%I _ _.
Next Obligation. move=> *. iIntros "?". iExists _. by iSplit. Qed.
Next Obligation. move=> > to. iIntros "[%[% ?]]". iStopProof. by apply to. Qed.
