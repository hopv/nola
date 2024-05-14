(** * Order theory *)

From nola Require Export prelude.

(** ** [proty]: Pre-ordered type *)
Structure proty := Proty {
  proty_car :> Type;
  #[canonical=no] ole :: SqSubsetEq proty_car;
  #[canonical=no] ole_preorder :: PreOrder ole;
}.
Implicit Type (OT : proty) (A : Type).

(** ** [oeqv]: Equivalence w.r.t. the order *)
Definition oeqv {OT} (o o' : OT) : Prop := o ⊑ o' ∧ o' ⊑ o.

Module OeqvNotation.
  Infix "≃" := oeqv (at level 70).
  Notation "(≃)" := oeqv (only parsing).
  Infix "( o ≃.)" := (oeqv o) (at level 70, only parsing).
  Infix "(.≃ o )" := (λ o', o' ≃ o) (at level 70, only parsing).
  Infix "≃@{ OT }" := (@oeqv OT) (at level 70, only parsing).
  Notation "(≃@{ OT } )" := (@oeqv OT) (only parsing).
End OeqvNotation.
Import OeqvNotation.

(** [≃] is an equivalence relation *)
#[export] Instance oeqv_equivalence {OT} : Equivalence (≃@{OT}).
Proof.
  constructor; [done|..]. { by move=> ??[??]. }
  move=> ???[??][??]. by split; etrans.
Qed.

(** [⊑] is proper w.r.t. [≃] *)
Local Lemma ole_proper' {OT} : Proper ((≃) ==> (≃) ==> (→)) (⊑@{OT}).
Proof. move=> ??[??]??[??]?; etrans; by [|etrans]. Qed.
#[export] Instance ole_proper {OT} : Proper ((≃) ==> (≃) ==> (↔)) (⊑@{OT}).
Proof. move=> *?*. split; by apply ole_proper'. Qed.

(** ** Canonical structures *)

(** Natural number *)
Canonical Structure natPro : proty := Proty nat (≤) _.
Lemma nat_ole {n m} : n ⊑ m ↔ n ≤ m.
Proof. done. Qed.

(** Proposition *)
Program Canonical Structure PropPro : proty := Proty Prop (→) _.
Next Obligation. constructor; auto. Qed.
Lemma Prop_ole {P Q : Prop} : P ⊑ Q ↔ (P → Q).
Proof. done. Qed.

(** Unit *)
Canonical Structure unitPro : proty := Proty unit (λ _ _, True) _.
Lemma unit_ole {u u' : ()} : u ⊑ u' ↔ True.
Proof. done. Qed.

(** Function *)
Program Canonical Structure funPro {A} (OTF : A → proty) : proty :=
  Proty (∀ a, OTF a) (λ f g, ∀ a, f a ⊑ g a) _.
Next Obligation. constructor; [auto|]=> ??????. etrans; auto. Qed.

(** Dual *)
#[projections(primitive)]
Record dual A := Dual { undual : A }.
Arguments Dual {_} _. Arguments undual {_} _.
Program Canonical Structure dualPro OT : proty :=
  Proty (dual OT) (λ o o', undual o' ⊑ undual o) _.
Next Obligation. move=> ?. constructor; [auto|]=> ?????. by etrans. Qed.

Lemma dual_ole {OT} {o o' : dual OT} : o ⊑ o' ↔ undual o' ⊑ undual o.
Proof. done. Qed.

(** ** Monotonicity *)

Class Mono {OT OT'} (f : OT → OT') := mono :: Proper ((⊑) ==> (⊑)) f.
Arguments mono {_ _} _ {_ _ _}.

Class Anti {OT OT'} (f : OT → OT') := anti :: Proper ((⊑) --> (⊑)) f.
Arguments anti {_ _} _ {_ _ _}.

Class Mono2 {OT OT' OT''} (f : OT → OT' → OT'') :=
  mono2 :: Proper ((⊑) ==> (⊑) ==> (⊑)) f.
Arguments mono2 {_ _ _} _ {_ _ _}.

Class AntiMono {OT OT' OT''} (f : OT → OT' → OT'') :=
  antimono :: Proper ((⊑) --> (⊑) ==> (⊑)) f.
Arguments antimono {_ _ _} _ {_ _ _}.

(** Partial application *)
#[export] Instance mono2_mono `{!@Mono2 OT OT' OT'' f} {o} : Mono (f o).
Proof. move=> ???. by apply mono2. Qed.
#[export] Instance antimono_mono `{!@AntiMono OT OT' OT'' f} {o} : Mono (f o).
Proof. move=> ???. by apply antimono. Qed.

(** Monotonicity implies properness *)
#[export] Instance mono_proper `{!@Mono OT OT' f} : Proper ((≃) ==> (≃)) f.
Proof. move=> >[??]; split; by apply mono. Qed.
#[export] Instance anti_proper `{!@Anti OT OT' f} : Proper ((≃) ==> (≃)) f.
Proof. move=> >[??]; split; by apply anti. Qed.
#[export] Instance mono2_proper `{!@Mono2 OT OT' OT'' f} :
  Proper ((≃) ==> (≃) ==> (≃)) f.
Proof. move=> >[??]??[??]. split; by apply mono2. Qed.
#[export] Instance antimono_proper `{!@AntiMono OT OT' OT'' f} :
  Proper ((≃) ==> (≃) ==> (≃)) f.
Proof. move=> >[??]??[??]. split; by apply antimono. Qed.

(** ** Top and bottom *)

Class OTop OT := O_TOP {
  otop :: Top OT;
  otop_intro {o : OT} : o ⊑ ⊤;
}.
Arguments O_TOP {_} _ _.

Class OBot OT := O_BOT {
  obot :: Bottom OT;
  obot_elim {o : OT} : ⊥ ⊑ o;
}.
Arguments O_BOT {_} _ _.

(** [nat] has the bottom *)
#[export] Program Instance obot_nat : OBot nat := O_BOT 0 _.
Next Obligation. move=> ?. rewrite nat_ole /bottom. lia. Qed.

(** [Prop] has the top and bottom *)
#[export] Program Instance otop_Prop : OTop Prop := O_TOP True _.
Next Obligation. done. Qed.
#[export] Program Instance obot_Prop : OBot Prop := O_BOT False _.
Next Obligation. move=> ?[]. Qed.

(** [()] has the top and bottom *)
#[export] Program Instance otop_unit : OTop unit := O_TOP () _.
Next Obligation. done. Qed.
#[export] Program Instance obot_unit : OBot unit := O_BOT () _.
Next Obligation. done. Qed.

(** The top and bottom for a function *)
#[export] Program Instance otop_fun `{!∀ a : A, OTop (OTF a)} :
  OTop (∀ a, OTF a) := O_TOP (λ _, ⊤) _.
Next Obligation. move=> *?. exact otop_intro. Qed.
#[export] Program Instance obot_fun `{!∀ a : A, OBot (OTF a)} :
  OBot (∀ a, OTF a) := O_BOT (λ _, ⊥) _.
Next Obligation. move=> *?. exact obot_elim. Qed.

(** [dual] flips the top and bottom *)
#[export] Program Instance otop_dual `{!OBot OT} : OTop (dual OT) :=
  O_TOP (Dual ⊥) _.
Next Obligation. move=> ???. exact obot_elim. Qed.
#[export] Program Instance obot_dual `{!OTop OT} : OBot (dual OT) :=
  O_BOT (Dual ⊤) _.
Next Obligation. move=> ???. exact otop_intro. Qed.

(** ** Binary meet and join *)

Class BinMeet OT := BIN_MEET {
  bin_meet :: Meet OT;
  bin_meet_elim_1 {o o' : OT} : o ⊓ o' ⊑ o;
  bin_meet_elim_2 {o o' : OT} : o ⊓ o' ⊑ o';
  bin_meet_intro {o o' o'' : OT} : o'' ⊑ o → o'' ⊑ o' → o'' ⊑ o ⊓ o';
}.
Arguments BIN_MEET {_} _ _ _ _.

Class BinJoin OT := BIN_JOIN {
  bin_join :: Join OT;
  bin_join_intro_1 {o o' : OT} : o ⊑ o ⊔ o';
  bin_join_intro_2 {o o' : OT} : o' ⊑ o ⊔ o';
  bin_join_elim {o o' o'' : OT} : o ⊑ o'' → o' ⊑ o'' → o ⊔ o' ⊑ o'';
}.
Arguments BIN_JOIN {_} _ _ _ _.

(** The binary meet/join is monotone *)
#[export] Instance bin_meet_mono `{!BinMeet OT} : Mono2 (meet (A:=OT)) | 20.
Proof.
  move=> *?*. apply bin_meet_intro; (etrans; [|done]);
    [exact bin_meet_elim_1|exact bin_meet_elim_2].
Qed.
#[export] Instance bin_join_mono `{!BinJoin OT} : Mono2 (join (A:=OT)) | 20.
Proof.
  move=> *?*. apply bin_join_elim; (etrans; [done|]);
    [exact bin_join_intro_1|exact bin_join_intro_2].
Qed.

(** The binary meet/join is commutative *)
#[export] Instance bin_meet_comm `{!BinMeet OT} : Comm (≃) (meet (A:=OT)) | 20.
Proof.
  move=> >. split; apply bin_meet_intro;
    by [apply bin_meet_elim_2|apply bin_meet_elim_1].
Qed.
#[export] Instance bin_join_comm `{!BinJoin OT} : Comm (≃) (join (A:=OT)) | 20.
Proof.
  move=> >. split; apply bin_join_elim;
    by [apply bin_join_intro_2|apply bin_join_intro_1].
Qed.

(** The binary meet/join is associative *)
#[export] Instance bin_meet_assoc `{!BinMeet OT} :
  Assoc (≃) (meet (A:=OT)) | 20.
Proof.
  move=> >. split; repeat apply bin_meet_intro;
    try exact bin_meet_elim_1; try exact bin_meet_elim_2;
    try (etrans; [exact bin_meet_elim_2|
      try exact bin_meet_elim_1; exact bin_meet_elim_2]);
    (etrans; [exact bin_meet_elim_1|
      try exact bin_meet_elim_1; exact bin_meet_elim_2]).
Qed.
#[export] Instance bin_join_assoc `{!BinJoin OT} :
  Assoc (≃) (join (A:=OT)) | 20.
Proof.
  move=> >. split; repeat apply bin_join_elim;
    try exact bin_join_intro_1; try exact bin_join_intro_2;
    try (etrans; last first; [exact bin_join_intro_1|
      try exact bin_join_intro_1; exact bin_join_intro_2]);
    (etrans; last first; [exact bin_join_intro_2|
      try exact bin_join_intro_1; exact bin_join_intro_2]).
Qed.

(** The binary meet/join is unitary with [⊤]/[⊥] *)
#[export] Instance bin_meet_top_l `{!BinMeet OT, !OTop OT} :
  LeftId (≃) ⊤ (meet (A:=OT)) | 20.
Proof.
  move=> ?. split; [exact bin_meet_elim_2|].
  apply bin_meet_intro; by [exact otop_intro|].
Qed.
#[export] Instance bin_meet_top_r `{!BinMeet OT, !OTop OT} :
  RightId (≃) ⊤ (meet (A:=OT)) | 20.
Proof. move=> ?. by rewrite comm left_id. Qed.
#[export] Instance bin_join_bot_l `{!BinJoin OT, !OBot OT} :
  LeftId (≃) ⊥ (join (A:=OT)) | 20.
Proof.
  move=> ?. split; [|exact bin_join_intro_2].
  apply bin_join_elim; by [exact obot_elim|].
Qed.
#[export] Instance bin_join_bot_r `{!BinJoin OT, !OBot OT} :
  RightId (≃) ⊥ (join (A:=OT)) | 20.
Proof. move=> ?. by rewrite comm left_id. Qed.

(** [nat] has the binary meet and join *)

#[export] Program Instance bin_meet_nat : BinMeet nat := BIN_MEET min _ _ _.
Next Obligation. move=> >. rewrite nat_ole /meet. lia. Qed.
Next Obligation. move=> >. rewrite nat_ole /meet. lia. Qed.
Next Obligation. move=> >. rewrite !nat_ole /meet. lia. Qed.

#[export] Program Instance bin_join_nat : BinJoin nat := BIN_JOIN max _ _ _.
Next Obligation. move=> >. rewrite nat_ole /join. lia. Qed.
Next Obligation. move=> >. rewrite nat_ole /join. lia. Qed.
Next Obligation. move=> >. rewrite !nat_ole /join. lia. Qed.

(** [Prop] has the binary meet and join *)

#[export] Program Instance bin_meet_Prop : BinMeet Prop := BIN_MEET and _ _ _.
Next Obligation. by move=> ??[??]. Qed.
Next Obligation. by move=> ??[??]. Qed.
Next Obligation. move=> ??????. split; auto. Qed.

#[export] Program Instance bin_join_Prop : BinJoin Prop := BIN_JOIN or _ _ _.
Next Obligation. move=> >. by left. Qed.
Next Obligation. move=> >. by right. Qed.
Next Obligation. move=> > ??[?|?]; auto. Qed.

(** [()] has the binary meet and join *)

#[export] Program Instance bin_meet_unit : BinMeet unit :=
  BIN_MEET (λ _ _, ()) _ _ _.
Solve All Obligations with done.

#[export] Program Instance bin_join_unit : BinJoin unit :=
  BIN_JOIN (λ _ _, ()) _ _ _.
Solve All Obligations with done.

(** The binary meet and join over functions *)

#[export] Program Instance bin_meet_fun `{!∀ a : A, BinMeet (OTF a)} :
  BinMeet (∀ a, OTF a) := BIN_MEET (λ f g a, f a ⊓ g a) _ _ _.
Next Obligation. move=> *?. by apply bin_meet_elim_1. Qed.
Next Obligation. move=> *?. by apply bin_meet_elim_2. Qed.
Next Obligation. move=> *?. by apply bin_meet_intro. Qed.

#[export] Program Instance bin_join_fun `{!∀ a : A, BinJoin (OTF a)} :
  BinJoin (∀ a, OTF a) := BIN_JOIN (λ f g a, f a ⊔ g a) _ _ _.
Next Obligation. move=> *?. by apply bin_join_intro_1. Qed.
Next Obligation. move=> *?. by apply bin_join_intro_2. Qed.
Next Obligation. move=> *?. by apply bin_join_elim. Qed.

(** The binary meet and join flipped with [dual] *)

#[export] Program Instance bin_meet_dual `{!BinJoin OT} : BinMeet (dual OT) :=
  BIN_MEET (λ o o', Dual (undual o ⊔ undual o')) _ _ _.
Next Obligation. move=> *. exact bin_join_intro_1. Qed.
Next Obligation. move=> *. exact bin_join_intro_2. Qed.
Next Obligation. move=> *. exact: bin_join_elim. Qed.

#[export] Program Instance bin_join_dual `{!BinMeet OT} : BinJoin (dual OT) :=
  BIN_JOIN (λ o o', Dual (undual o ⊓ undual o')) _ _ _.
Next Obligation. move=> *. exact bin_meet_elim_1. Qed.
Next Obligation. move=> *. exact bin_meet_elim_2. Qed.
Next Obligation. move=> *. exact: bin_meet_intro. Qed.

(** ** Big meet and join *)

Class BigMeet OT := BIG_MEET {
  big_meet {A : Type} : (A → Prop) → (A → OT) → OT;
  big_meet_elim {A} {S : A → Prop} f {a} : S a → big_meet S f ⊑ f a;
  big_meet_intro {A} {S : A → Prop} f {o} :
    (∀ a, S a → o ⊑ f a) → o ⊑ big_meet S f;
}.
Arguments BIG_MEET {_} _ _ _.

Class BigJoin OT := BIG_JOIN {
  big_join {A : Type} : (A → Prop) → (A → OT) → OT;
  big_join_intro {A} {S : A → Prop} f {a} : S a → f a ⊑ big_join S f;
  big_join_elim {A} {S : A → Prop} f {o} :
    (∀ a, S a → f a ⊑ o) → big_join S f ⊑ o;
}.
Arguments BIG_JOIN {_} _ _ _.

Module BigMJNotation.
  Notation "[⊓] a :: φ , o" := (big_meet (λ a, φ) (λ a, o))
    (at level 200, a at level 1, φ at level 10, right associativity,
      format "[⊓]  a  ::  φ ,  o").
  Notation "[⊔] a :: φ , o" := (big_join (λ a, φ) (λ a, o))
    (at level 200, a at level 1, φ at level 10, right associativity,
      format "[⊔]  a  ::  φ ,  o").
End BigMJNotation.
Import BigMJNotation.

(** The big meet/join is monotone *)
#[export] Instance big_meet_mono `{!BigMeet OT} {A} :
  AntiMono (big_meet (OT:=OT) (A:=A)) | 20.
Proof.
  move=>/= ?? TS ???. apply big_meet_intro=> ? /TS ?.
  etrans; by [apply big_meet_elim|].
Qed.
#[export] Instance big_join_mono `{!BigJoin OT} {A} :
  Mono2 (big_join (OT:=OT) (A:=A)) | 20.
Proof.
  move=>/= ?? ST ???. apply big_join_elim=> ? /ST ?.
  by etrans; [|by apply big_join_intro].
Qed.

(** Inducing a binary meet/join from the big meet/join *)

Program Definition bin_meet_big_meet `{!BigMeet OT} : BinMeet OT :=
  BIN_MEET (λ o o', [⊓] o'' :: o'' = o ∨ o'' = o', o'') _ _ _.
Next Obligation. move=> *. apply (big_meet_elim id). auto. Qed.
Next Obligation. move=> *. apply (big_meet_elim id). auto. Qed.
Next Obligation. move=> *. by apply big_meet_intro=> ?[->|->]. Qed.

Program Definition bin_join_big_join `{!BigJoin OT} : BinJoin OT :=
  BIN_JOIN (λ o o', [⊔] o'' :: o'' = o ∨ o'' = o', o'') _ _ _.
Next Obligation. move=> *. apply (big_join_intro id). auto. Qed.
Next Obligation. move=> *. apply (big_join_intro id). auto. Qed.
Next Obligation. move=> *. by apply big_join_elim=> ?[->|->]. Qed.

(** [Prop] has the big meet and join *)

#[export] Program Instance big_meet_Prop : BigMeet Prop :=
  BIG_MEET (λ _ S φ, ∀ o, S o → φ o) _ _.
Next Obligation. move=>/= ??????. auto. Qed.
Next Obligation. move=>/= ???? all ???. exact: all. Qed.

#[export] Program Instance big_join_Prop : BigJoin Prop :=
  BIG_JOIN (λ _ S φ, ∃ o, S o ∧ φ o) _ _.
Next Obligation. move=>/= ??????. eauto. Qed.
Next Obligation. move=>/= ???? all [?[??]]. exact: all. Qed.

(** The big meet and join over functions *)

#[export] Program Instance big_meet_fun `{!∀ a : A, BigMeet (OTF a)} :
  BigMeet (∀ a, OTF a) := BIG_MEET (λ _ S F a, [⊓] b :: S b, F b a) _ _.
Next Obligation. move=> *?. exact: big_meet_elim. Qed.
Next Obligation.
  move=> ??????? all ?. apply big_meet_intro=> ??. by apply all.
Qed.

#[export] Program Instance big_join_fun `{!∀ a : A, BigJoin (OTF a)} :
  BigJoin (∀ a, OTF a) := BIG_JOIN (λ _ S F a, [⊔] b :: S b, F b a) _ _.
Next Obligation. move=> *?. by exact: big_join_intro. Qed.
Next Obligation.
  move=> ??????? all ?. apply big_join_elim=> ??. by apply all.
Qed.

(** The big meet and join flipped with [dual] *)

#[export] Program Instance big_meet_dual `{!BigJoin OT} : BigMeet (dual OT) :=
  BIG_MEET (λ _ S f, Dual ([⊔] o :: S o, undual (f o))) _ _.
Next Obligation. move=> */=. by exact: (big_join_intro (undual ∘ _)). Qed.
Next Obligation. move=> */=. by exact: (big_join_elim (undual ∘ _)). Qed.

#[export] Program Instance big_join_dual `{!BigMeet OT} : BigJoin (dual OT) :=
  BIG_JOIN (λ _ S f, Dual ([⊓] o :: S o, undual (f o))) _ _.
Next Obligation. move=> */=. by exact: (big_meet_elim (undual ∘ _)). Qed.
Next Obligation. move=> */=. by exact: (big_meet_intro (undual ∘ _)). Qed.

(** ** [lfp]: Knaster-Tarski least fixed point *)

Section lfp.
  Context `{!BigMeet OT}.
  Implicit Type f : OT → OT.

  Local Definition lfp_def (f : OT → OT) : OT :=
    [⊓] o :: f o ⊑ o, o.
  Local Lemma lfp_aux : seal lfp_def. Proof. by eexists. Qed.
  Definition lfp := lfp_aux.(unseal).
  Local Lemma lfp_unseal : lfp = lfp_def. Proof. exact: seal_eq. Qed.

  (** Unfold [lfp] *)
  Lemma lfp_unfold_2 `{!Mono f} : f (lfp f) ⊑ lfp f.
  Proof.
    rewrite lfp_unseal. apply big_meet_intro=> ??. etrans; [|done].
    by apply (mono f), (big_meet_elim id).
  Qed.
  Lemma lfp_unfold_1 `{!Mono f} : lfp f ⊑ f (lfp f).
  Proof.
    rewrite {1}lfp_unseal. apply (big_meet_elim id), (mono f), lfp_unfold_2.
  Qed.
  Lemma lfp_unfold `{!Mono f} : lfp f ≃ f (lfp f).
  Proof. split; [apply lfp_unfold_1|apply lfp_unfold_2]. Qed.

  (** Basic induction principle *)
  Lemma lfp_ind `{!Mono f} {o} : f o ⊑ o → lfp f ⊑ o.
  Proof. rewrite lfp_unseal=> ?. by apply (big_meet_elim id). Qed.

  (** [lfp] is monotone *)
  Lemma lfp_mono `{!Mono f, !Mono g} : f ⊑ g → lfp f ⊑ lfp g.
  Proof. move=> fg. apply lfp_ind. etrans; [apply fg|apply lfp_unfold]. Qed.
  Lemma lfp_cong `{!Mono f, !Mono g} : f ≃ g → lfp f ≃ lfp g.
  Proof. move=> [??]. split; by apply lfp_mono. Qed.

  (** Augmenting a function with a meet *)
  Definition aug_meet `{!BinMeet OT} (f : OT → OT) o o' := f (o' ⊓ o).
  #[export] Instance aug_meet_mono `{!BinMeet OT, !Mono f} : Mono2 (aug_meet f).
  Proof. move=> *?*. apply (mono f), mono2; by [apply _| |]. Qed.
  Lemma aug_meet_nest `{!BinMeet OT, !Mono f} {o o'} :
    aug_meet (aug_meet f o) o' ≃ aug_meet f (o ⊓ o').
  Proof. split=> ?; rewrite comm; apply (mono f); by rewrite assoc. Qed.
  Lemma aug_meet_top `{!BinMeet OT, !Mono f, !OTop OT} : aug_meet f ⊤ ≃ f.
  Proof. split=> ?; apply (mono f); by rewrite right_id. Qed.

  (** Parameterized induction principle *)
  Lemma lfp_para_ind `{!BinMeet OT, !BigMeet OT, !Mono f} {o} :
    lfp (aug_meet f o) ⊑ o → lfp f ⊑ o.
  Proof.
    move=> to. etrans; [|apply to]. apply lfp_ind.
    etrans; [|by apply lfp_unfold]. apply (mono f). by apply bin_meet_intro.
  Qed.
End lfp.

(** ** [gfp]: Knaster-Tarski greatest fixed point *)

Section gfp.
  Context `{!BigJoin OT}.
  Implicit Type f : OT → OT.

  Local Definition gfp_def (f : OT → OT) : OT :=
    [⊔] o :: o ⊑ f o, o.
  Local Lemma gfp_aux : seal gfp_def. Proof. by eexists. Qed.
  Definition gfp := gfp_aux.(unseal).
  Local Lemma gfp_unseal : gfp = gfp_def. Proof. exact: seal_eq. Qed.

  (** Unfold [gfp] *)
  Lemma gfp_unfold_1 `{!Mono f} : gfp f ⊑ f (gfp f).
  Proof.
    rewrite gfp_unseal. apply big_join_elim=> ??. etrans; [done|].
    by apply (mono f), (big_join_intro id).
  Qed.
  Lemma gfp_unfold_2 `{!Mono f} : f (gfp f) ⊑ gfp f.
  Proof.
    rewrite {2}gfp_unseal. apply (big_join_intro id), (mono f), gfp_unfold_1.
  Qed.
  Lemma gfp_unfold `{!Mono f} : gfp f ≃ f (gfp f).
  Proof. split; [apply gfp_unfold_1|apply gfp_unfold_2]. Qed.

  (** Basic coinduction principle *)
  Lemma gfp_coind `{!Mono f} {o} : o ⊑ f o → o ⊑ gfp f.
  Proof. rewrite gfp_unseal=> ?. by apply (big_join_intro id). Qed.

  (** [gfp] is monotone *)
  Lemma gfp_mono `{!BigJoin OT, !Mono f, !Mono g} : f ⊑ g → gfp f ⊑ gfp g.
  Proof. move=> fg. apply gfp_coind. etrans; [apply gfp_unfold|apply fg]. Qed.
  Lemma gfp_cong `{!BigJoin OT, !Mono f, !Mono g} : f ≃ g → gfp f ≃ gfp g.
  Proof. move=> [??]. split; by apply gfp_mono. Qed.

  (** Augmenting a function with a join *)
  Definition aug_join `{!BinJoin OT} f o o' := f (o' ⊔ o).
  #[export] Instance aug_join_mono `{!BinJoin OT, !Mono f} : Mono2 (aug_join f).
  Proof. move=> *?*. apply (mono f), mono2; by [apply _| |]. Qed.
  Lemma aug_join_nest `{!BinJoin OT, !Mono f} {o o'} :
    aug_join (aug_join f o) o' ≃ aug_join f (o ⊔ o').
  Proof. split=> ?; rewrite comm; apply (mono f); by rewrite assoc. Qed.
  Lemma aug_join_bot `{!BinJoin OT, !Mono f, !OBot OT} : aug_join f ⊥ ≃ f.
  Proof. split=> ?; apply (mono f); by rewrite right_id. Qed.

  (** Parameterized coinduction principle *)
  Lemma gfp_para_coind `{!BinJoin OT, !BigJoin OT, !Mono f} {o} :
    o ⊑ gfp (aug_join f o) → o ⊑ gfp f.
  Proof.
    move=> to. etrans; [apply to|]. apply gfp_coind.
    etrans; [by apply gfp_unfold|]. apply (mono f). by apply bin_join_elim.
  Qed.
End gfp.

Module OrderNotation.
  Export OeqvNotation.
  Export BigMJNotation.
End OrderNotation.
