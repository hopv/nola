(** * Order theory *)

From nola Require Export prelude.
From iris.algebra Require Export ofe.

(** ** [poty]: Partially ordered type *)
#[projections(primitive)]
Structure poty := Poty {
  poty_car :> ofe;
  #[canonical=no] ole :: SqSubsetEq poty_car;
  #[canonical=no] ole_preorder :: PreOrder ole;
  #[canonical=no] equiv_ole {o o' : poty_car} :
    o ≡ o' ↔ o ⊑ o' ∧ o' ⊑ o;
}.
Add Printing Constructor poty.
Arguments poty_car {OT} : rename.
Arguments ole {OT} : rename. Arguments ole_preorder {OT} : rename.
Arguments equiv_ole {OT _ _} : rename.
#[export] Typeclasses Transparent ole.

Implicit Type (OT : poty) (A : Type).

(** [⊑] is a subrelation of [≡] *)
#[export] Instance equiv_ole_1 {OT} : subrelation (≡@{OT}) (⊑@{OT}).
Proof. move=> >. apply equiv_ole. Qed.
#[export] Instance equiv_ole_2 {OT} : subrelation (≡@{OT}) (flip (⊑@{OT})).
Proof. move=> >. apply equiv_ole. Qed.

(** [⊑] is proper *)
#[export] Instance ole_proper_ole {OT} : Proper ((⊑) --> (⊑) ==> (→)) (⊑@{OT}).
Proof. move=>/= ???????. etrans; by [|etrans]. Qed.
#[export] Instance ole_proper_ole_flip {OT} :
  Proper ((⊑) ==> (⊑) --> flip (→)) (⊑@{OT}).
Proof. move=> ???????. by apply: ole_proper_ole. Qed.
#[export] Instance ole_proper {OT} : Proper ((≡) ==> (≡) ==> (↔)) (⊑@{OT}).
Proof.
  move=> ?? eqv ?? eqv'. by split=> ?; [rewrite -eqv -eqv'|rewrite eqv eqv'].
Qed.

(** ** Canonical structures of [poty] *)

(** Natural number *)
Program Canonical natP : poty := Poty natO (≤) _ _.
Next Obligation.
  move=> >. split; [by move=> ->|]. case=> *. by apply Nat.le_antisymm.
Qed.
Lemma nat_ole {n m} : n ⊑ m ↔ n ≤ m.
Proof. done. Qed.

(** Proposition *)
Program Canonical PropP : poty := Poty PropO (→) _ _.
Next Obligation. constructor; auto. Qed.
Next Obligation. done. Qed.
Lemma Prop_ole {P Q : Prop} : P ⊑ Q ↔ (P → Q).
Proof. done. Qed.

(** Unit *)
Program Canonical unitP : poty := Poty unitO (λ _ _, True) _ _.
Next Obligation. done. Qed.
Lemma unit_ole {u u' : ()} : u ⊑ u' ↔ True.
Proof. done. Qed.

(** Function *)
Program Canonical funP {A} (OTF : A → poty) : poty :=
  Poty (discrete_funO OTF) (λ f g, ∀ a, f a ⊑ g a) _ _.
Next Obligation. constructor; [auto|]=> ??????. etrans; auto. Qed.
Next Obligation.
  move=> ????. split.
  - move=> ?. split=> ?; by apply equiv_ole.
  - move=> [??]?. by apply equiv_ole.
Qed.
Module FunPNotation.
  Notation "A -p> OT" := (@funP A (λ _, OT))
    (at level 99, OT at level 200, right associativity).
End FunPNotation.
Import FunPNotation.

(** Non-expansive map *)
Program Canonical funNP (A : ofe) OT :=
  Poty (A -n> OT) (λ f g, ∀ a, f a ⊑ g a) _ _.
Next Obligation.
  move=> ??. split; [by move|]. move=> [??][??][??]/= le le' ?.
  etrans; [apply le|apply le'].
Qed.
Next Obligation.
  move=> ??[??][??]/=. split.
  - move=> ?. split=>/= ?; by apply equiv_ole.
  - move=> [??]?. by apply equiv_ole.
Qed.
Module FunNPNotation.
  Notation "A -np> PT" := (@funNP A PT)
    (at level 99, PT at level 200, right associativity).
End FunNPNotation.
Import FunNPNotation.

(** Dual *)
#[projections(primitive)]
Record dual A := Dual { undual : A }.
Add Printing Constructor dual.
Arguments Dual {_} _. Arguments undual {_} _.
(** [ofe] structure for [dual] *)
Definition dual_equiv_def {A : ofe} : relation (dual A) :=
  λ '(Dual a) '(Dual a'), a ≡ a'.
Definition dual_dist_def {A : ofe} n : relation (dual A) :=
  λ '(Dual a) '(Dual a'), a ≡{n}≡ a'.
Program Canonical dualO (A : ofe) :=
  @Ofe (dual A) dual_equiv_def dual_dist_def _.
Next Obligation.
  split=> >; [by apply equiv_dist| |by apply dist_lt].
  unfold dist, dual_dist_def. split; [by move..|]=> ???. apply transitivity.
Qed.
Lemma dual_equiv {A : ofe} {a a' : dualO A} :
  (a ≡ a') = (a.(undual) ≡ a'.(undual)).
Proof. done. Qed.
Lemma dual_dist {A : ofe} {a a' : dualO A} {n} :
  (a ≡{n}≡ a') = (a.(undual) ≡{n}≡ a'.(undual)).
Proof. done. Qed.
(** [Dual] is non-expansive *)
#[export] Instance dual_ne {A : ofe} : NonExpansive (@Dual A).
Proof. solve_proper. Qed.
#[export] Instance dual_proper {A : ofe} : Proper ((≡) ==> (≡)) (@Dual A).
Proof. solve_proper. Qed.
(** [poty] structure for [dual] *)
Program Canonical dualP OT : poty :=
  Poty (dualO OT) (λ o o', o'.(undual) ⊑ o.(undual)) _ _.
Next Obligation. move=> ?. constructor; [auto|]=> ?????. by etrans. Qed.
Next Obligation.
  move=> ???. split; by [move/equiv_ole|move=> ?; apply equiv_ole].
Qed.
Lemma dual_ole {OT} {o o' : dual OT} : o ⊑ o' ↔ o'.(undual) ⊑ o.(undual).
Proof. done. Qed.

(** ** Monotonicity *)

Class Mono {OT OT'} (f : OT -p> OT') := mono :: Proper ((⊑) ==> (⊑)) f.
Hint Mode Mono - - ! : typeclass_instances.
Class Anti {OT OT'} (f : OT -p> OT') := anti :: Proper ((⊑) --> (⊑)) f.
Hint Mode Anti - - ! : typeclass_instances.
Class Mono2 {OT OT' OT''} (f : OT -p> OT' -p> OT'') :=
  mono2 :: Proper ((⊑) ==> (⊑) ==> (⊑)) f.
Hint Mode Mono2 - - - ! : typeclass_instances.
Class AntiMono {OT OT' OT''} (f : OT -p> OT' -p> OT'') :=
  antimono :: Proper ((⊑) --> (⊑) ==> (⊑)) f.
Hint Mode AntiMono - - - ! : typeclass_instances.

(** Partial application *)
#[export] Instance mono2_mono_1 `{!@Mono2 OT OT' OT'' f} : Mono f.
Proof. unfold Mono. solve_proper. Qed.
#[export] Instance mono2_mono_2 `{!@Mono2 OT OT' OT'' f} {o} : Mono (f o).
Proof. unfold Mono. solve_proper. Qed.
#[export] Instance antimono_mono_1 `{!@AntiMono OT OT' OT'' f} : Anti f.
Proof. unfold Anti. solve_proper. Qed.
#[export] Instance antimono_mono_2 `{!@AntiMono OT OT' OT'' f} {o} : Mono (f o).
Proof. unfold Mono. solve_proper. Qed.

(** Flip order *)
#[export] Instance mono_flip `{!@Mono OT OT' f} : Proper ((⊑) --> flip (⊑)) f.
Proof. solve_proper. Qed.
#[export] Instance anti_flip `{!@Anti OT OT' f} : Proper ((⊑) ==> flip (⊑)) f.
Proof. solve_proper. Qed.
#[export] Instance mono2_flip `{!@Mono2 OT OT' OT'' f} :
  Proper ((⊑) --> (⊑) --> flip (⊑)) f.
Proof. solve_proper. Qed.
#[export] Instance antimono_flip `{!@AntiMono OT OT' OT'' f} :
  Proper ((⊑) ==> (⊑) --> flip (⊑)) f.
Proof. solve_proper. Qed.

(** Monotonicity implies properness *)
#[export] Instance mono_proper `{!@Mono OT OT' f} : Proper ((≡) ==> (≡)) f.
Proof. move=> > /equiv_ole[??]. apply equiv_ole. split; by apply mono. Qed.
#[export] Instance anti_proper `{!@Anti OT OT' f} : Proper ((≡) ==> (≡)) f.
Proof. move=> > /equiv_ole[??]. apply equiv_ole. split; by apply anti. Qed.
#[export] Instance mono2_proper `{!@Mono2 OT OT' OT'' f} :
  Proper ((≡) ==> (≡) ==> (≡)) f.
Proof.
  move=> > /equiv_ole[??] ?? /equiv_ole[??]. apply equiv_ole.
  split; by apply mono2.
Qed.
#[export] Instance antimono_proper `{!@AntiMono OT OT' OT'' f} :
  Proper ((≡) ==> (≡) ==> (≡)) f.
Proof.
  move=> > /equiv_ole[??] ?? /equiv_ole[??]. apply equiv_ole.
  split; by apply antimono.
Qed.

(** [⊑] is monotone *)
#[export] Instance ole_mono {OT} : AntiMono (⊑@{OT}).
Proof. move=> *?*?. etrans; by [|etrans]. Qed.

(** ** Top and bottom *)

Class Otop OT := OTOP {
  otop :: Top OT;
  otop_intro {o : OT} : o ⊑ ⊤;
}.
Hint Mode Otop ! : typeclass_instances.
Arguments OTOP {_} _ _.

Class Obot OT := OBOT {
  obot :: Bottom OT;
  obot_elim {o : OT} : ⊥ ⊑ o;
}.
Hint Mode Obot ! : typeclass_instances.
Arguments OBOT {_} _ _.

(** [nat] has the bottom *)
#[export] Program Instance obot_nat : Obot nat := OBOT 0 _.
Next Obligation. move=> ?. rewrite nat_ole /bottom. lia. Qed.

(** [Prop] has the top and bottom *)
#[export] Program Instance otop_Prop : Otop Prop := OTOP True _.
Next Obligation. done. Qed.
#[export] Program Instance obot_Prop : Obot Prop := OBOT False _.
Next Obligation. move=> ?[]. Qed.

(** [()] has the top and bottom *)
#[export] Program Instance otop_unit : Otop unit := OTOP () _.
Next Obligation. done. Qed.
#[export] Program Instance obot_unit : Obot unit := OBOT () _.
Next Obligation. done. Qed.

(** The top and bottom for a function *)
#[export] Program Instance otop_fun `{!∀ a : A, Otop (OTF a)} :
  Otop (funP OTF) := OTOP (λ _, ⊤) _.
Next Obligation. move=> *?. exact otop_intro. Qed.
#[export] Program Instance obot_fun `{!∀ a : A, Obot (OTF a)} :
  Obot (funP OTF) := OBOT (λ _, ⊥) _.
Next Obligation. move=> *?. exact obot_elim. Qed.
#[export] Program Instance otop_funN `{!Otop OT} {A : ofe} :
  Otop (A -np> OT) := OTOP (OfeMor (λ _, ⊤)) _.
Next Obligation. move=> *?. exact otop_intro. Qed.
#[export] Program Instance obot_funN `{!Obot OT} {A : ofe} :
  Obot (A -np> OT) := OBOT (OfeMor (λ _, ⊥)) _.
Next Obligation. move=> *?. exact obot_elim. Qed.

(** [dual] flips the top and bottom *)
#[export] Program Instance otop_dual `{!Obot OT} : Otop (dual OT) :=
  OTOP (Dual ⊥) _.
Next Obligation. move=> ???. exact obot_elim. Qed.
#[export] Program Instance obot_dual `{!Otop OT} : Obot (dual OT) :=
  OBOT (Dual ⊤) _.
Next Obligation. move=> ???. exact otop_intro. Qed.

(** ** Binary meet and join *)

Class BinMeet OT := BIN_MEET {
  bin_meet :: Meet OT;
  bin_meet_ne :: NonExpansive2 bin_meet;
  bin_meet_elim_1 {o o' : OT} : o ⊓ o' ⊑ o;
  bin_meet_elim_2 {o o' : OT} : o ⊓ o' ⊑ o';
  bin_meet_intro {o o' o'' : OT} : o'' ⊑ o → o'' ⊑ o' → o'' ⊑ o ⊓ o';
}.
Hint Mode BinMeet ! : typeclass_instances.
Arguments BIN_MEET {_} _ _ _ _.

Class BinJoin OT := BIN_JOIN {
  bin_join :: Join OT;
  bin_join_ne :: NonExpansive2 bin_join;
  bin_join_intro_1 {o o' : OT} : o ⊑ o ⊔ o';
  bin_join_intro_2 {o o' : OT} : o' ⊑ o ⊔ o';
  bin_join_elim {o o' o'' : OT} : o ⊑ o'' → o' ⊑ o'' → o ⊔ o' ⊑ o'';
}.
Hint Mode BinJoin ! : typeclass_instances.
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
#[export] Instance bin_meet_comm `{!BinMeet OT} : Comm (≡) (meet (A:=OT)) | 20.
Proof.
  move=> >. apply equiv_ole. split; apply bin_meet_intro;
    by [apply bin_meet_elim_2|apply bin_meet_elim_1].
Qed.
#[export] Instance bin_join_comm `{!BinJoin OT} : Comm (≡) (join (A:=OT)) | 20.
Proof.
  move=> >. apply equiv_ole. split; apply bin_join_elim;
    by [apply bin_join_intro_2|apply bin_join_intro_1].
Qed.

(** The binary meet/join is associative *)
#[export] Instance bin_meet_assoc `{!BinMeet OT} :
  Assoc (≡) (meet (A:=OT)) | 20.
Proof.
  move=> >. apply equiv_ole. split; repeat apply bin_meet_intro;
    try exact bin_meet_elim_1; try exact bin_meet_elim_2;
    try (etrans; [exact bin_meet_elim_2|
      try exact bin_meet_elim_1; exact bin_meet_elim_2]);
    (etrans; [exact bin_meet_elim_1|
      try exact bin_meet_elim_1; exact bin_meet_elim_2]).
Qed.
#[export] Instance bin_join_assoc `{!BinJoin OT} :
  Assoc (≡) (join (A:=OT)) | 20.
Proof.
  move=> >. apply equiv_ole. split; repeat apply bin_join_elim;
    try exact bin_join_intro_1; try exact bin_join_intro_2;
    try (etrans; last first; [exact bin_join_intro_1|
      try exact bin_join_intro_1; exact bin_join_intro_2]);
    (etrans; last first; [exact bin_join_intro_2|
      try exact bin_join_intro_1; exact bin_join_intro_2]).
Qed.

(** The binary meet/join is unitary with [⊤]/[⊥] *)
#[export] Instance bin_meet_top_l `{!BinMeet OT, !Otop OT} :
  LeftId (≡) ⊤ (meet (A:=OT)) | 20.
Proof.
  move=> ?. apply equiv_ole. split; [exact bin_meet_elim_2|].
  apply bin_meet_intro; by [exact otop_intro|].
Qed.
#[export] Instance bin_meet_top_r `{!BinMeet OT, !Otop OT} :
  RightId (≡) ⊤ (meet (A:=OT)) | 20.
Proof. move=> ?. by rewrite comm left_id. Qed.
#[export] Instance bin_join_bot_l `{!BinJoin OT, !Obot OT} :
  LeftId (≡) ⊥ (join (A:=OT)) | 20.
Proof.
  move=> ?. apply equiv_ole. split; [|exact bin_join_intro_2].
  apply bin_join_elim; by [exact obot_elim|].
Qed.
#[export] Instance bin_join_bot_r `{!BinJoin OT, !Obot OT} :
  RightId (≡) ⊥ (join (A:=OT)) | 20.
Proof. move=> ?. by rewrite comm left_id. Qed.

(** [nat] has the binary meet and join *)

#[export] Program Instance bin_meet_nat : BinMeet nat := BIN_MEET min _ _ _ _.
Next Obligation. move=> >. rewrite nat_ole /meet. lia. Qed.
Next Obligation. move=> >. rewrite nat_ole /meet. lia. Qed.
Next Obligation. move=> >. rewrite !nat_ole /meet. lia. Qed.

#[export] Program Instance bin_join_nat : BinJoin nat := BIN_JOIN max _ _ _ _.
Next Obligation. move=> >. rewrite nat_ole /join. lia. Qed.
Next Obligation. move=> >. rewrite nat_ole /join. lia. Qed.
Next Obligation. move=> >. rewrite !nat_ole /join. lia. Qed.

(** [Prop] has the binary meet and join *)

#[export] Program Instance bin_meet_Prop : BinMeet Prop := BIN_MEET and _ _ _ _.
Next Obligation. by move=> ??[??]. Qed.
Next Obligation. by move=> ??[??]. Qed.
Next Obligation. move=> ??????. split; auto. Qed.

#[export] Program Instance bin_join_Prop : BinJoin Prop := BIN_JOIN or _ _ _ _.
Next Obligation. move=> >. by left. Qed.
Next Obligation. move=> >. by right. Qed.
Next Obligation. move=> > ??[?|?]; auto. Qed.

(** [()] has the binary meet and join *)

#[export] Program Instance bin_meet_unit : BinMeet unit :=
  BIN_MEET (λ _ _, ()) _ _ _ _.
Solve All Obligations with done.

#[export] Program Instance bin_join_unit : BinJoin unit :=
  BIN_JOIN (λ _ _, ()) _ _ _ _.
Solve All Obligations with done.

(** The binary meet and join over functions *)

#[export] Program Instance bin_meet_fun `{!∀ a : A, BinMeet (OTF a)} :
  BinMeet (funP OTF) := BIN_MEET (λ f g a, f a ⊓ g a) _ _ _ _.
Next Obligation. move=> *?*?*?. by f_equiv. Qed.
Next Obligation. move=> *?. by apply bin_meet_elim_1. Qed.
Next Obligation. move=> *?. by apply bin_meet_elim_2. Qed.
Next Obligation. move=> *?. by apply bin_meet_intro. Qed.
#[export] Program Instance bin_join_fun `{!∀ a : A, BinJoin (OTF a)} :
  BinJoin (funP OTF) := BIN_JOIN (λ f g a, f a ⊔ g a) _ _ _ _.
Next Obligation. move=> *?*?*?. by f_equiv. Qed.
Next Obligation. move=> *?. by apply bin_join_intro_1. Qed.
Next Obligation. move=> *?. by apply bin_join_intro_2. Qed.
Next Obligation. move=> *?. by apply bin_join_elim. Qed.

#[export] Program Instance bin_meet_funN `{!BinMeet OT} {A : ofe} :
  BinMeet (A -np> OT) :=
  BIN_MEET (λ f g, OfeMor (λ a, f a ⊓ g a) (ofe_mor_ne:=_)) _ _ _ _.
Next Obligation. solve_proper. Qed.
Next Obligation. solve_proper. Qed.
Next Obligation. move=> *?. by apply bin_meet_elim_1. Qed.
Next Obligation. move=> *?. by apply bin_meet_elim_2. Qed.
Next Obligation. move=> *?. by apply bin_meet_intro. Qed.
#[export] Program Instance bin_join_funN `{!BinJoin OT} {A : ofe} :
  BinJoin (A -np> OT) :=
  BIN_JOIN (λ f g, OfeMor (λ a, f a ⊔ g a) (ofe_mor_ne:=_)) _ _ _ _.
Next Obligation. solve_proper. Qed.
Next Obligation. solve_proper. Qed.
Next Obligation. move=> *?. by apply bin_join_intro_1. Qed.
Next Obligation. move=> *?. by apply bin_join_intro_2. Qed.
Next Obligation. move=> *?. by apply bin_join_elim. Qed.

(** The binary meet and join flipped with [dual] *)

#[export] Program Instance bin_meet_dual `{!BinJoin OT} : BinMeet (dual OT) :=
  BIN_MEET (λ o o', Dual (undual o ⊔ undual o')) _ _ _ _.
Next Obligation. solve_proper. Qed.
Next Obligation. move=> *. exact bin_join_intro_1. Qed.
Next Obligation. move=> *. exact bin_join_intro_2. Qed.
Next Obligation. move=> *. exact: bin_join_elim. Qed.
#[export] Program Instance bin_join_dual `{!BinMeet OT} : BinJoin (dual OT) :=
  BIN_JOIN (λ o o', Dual (undual o ⊓ undual o')) _ _ _ _.
Next Obligation. solve_proper. Qed.
Next Obligation. move=> *. exact bin_meet_elim_1. Qed.
Next Obligation. move=> *. exact bin_meet_elim_2. Qed.
Next Obligation. move=> *. exact: bin_meet_intro. Qed.

(** ** Big meet and join *)

Class BigMeet OT := BIG_MEET {
  big_meet {A : Type} : (A -p> Prop) → (A -p> OT) → OT;
  big_meet_ne {A S} : NonExpansive (@big_meet A S);
  big_meet_elim {A S} f {a} : S a → @big_meet A S f ⊑ f a;
  big_meet_intro {A S} f {o} :
    (∀ a, S a → o ⊑ f a) → o ⊑ @big_meet A S f;
}.
Hint Mode BigMeet ! : typeclass_instances.
Arguments BIG_MEET {_} _ _ _.

Class BigJoin OT := BIG_JOIN {
  big_join {A : Type} : (A -p> Prop) → (A -p> OT) → OT;
  big_join_ne {A S} : NonExpansive (@big_join A S);
  big_join_intro {A S} f {a} : S a → f a ⊑ @big_join A S f;
  big_join_elim {A S} f {o} :
    (∀ a, S a → f a ⊑ o) → @big_join A S f ⊑ o;
}.
Hint Mode BigJoin ! : typeclass_instances.
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

(** [Prop] has the big meet and join *)

#[export] Program Instance big_meet_Prop : BigMeet Prop :=
  BIG_MEET (λ _ S φ, ∀ o, S o → φ o) _ _ _.
Next Obligation. move=>/= ??????. auto. Qed.
Next Obligation. move=>/= ???? all ???. exact: all. Qed.

#[export] Program Instance big_join_Prop : BigJoin Prop :=
  BIG_JOIN (λ _ S φ, ∃ o, S o ∧ φ o) _ _ _.
Next Obligation. move=> ????? eqv. do 3 f_equiv. apply (eqv _). Qed.
Next Obligation. move=>/= ??????. eauto. Qed.
Next Obligation. move=>/= ???? all [?[??]]. exact: all. Qed.

(** The big meet and join over functions *)

#[export] Program Instance big_meet_fun `{!∀ a : A, BigMeet (OTF a)} :
  BigMeet (funP OTF) := BIG_MEET (λ _ S F a, [⊓] b :: S b, F b a) _ _ _.
Next Obligation.
  move=> ???????? eqv ?. apply big_meet_ne=> ?. apply (eqv _ _).
Qed.
Next Obligation. move=> *?. exact: big_meet_elim. Qed.
Next Obligation.
  move=> ??????? all o. apply big_meet_intro=> *. move: o. by apply all.
Qed.
#[export] Program Instance big_join_fun `{!∀ a : A, BigJoin (OTF a)} :
  BigJoin (funP OTF) := BIG_JOIN (λ _ S F a, [⊔] b :: S b, F b a) _ _ _.
Next Obligation.
  move=> ???????? eqv ?. apply big_join_ne=> ?. apply (eqv _ _).
Qed.
Next Obligation. move=> *?. by exact: big_join_intro. Qed.
Next Obligation.
  move=> ??????? all o. apply big_join_elim=> *. move: o. by apply all.
Qed.

#[export] Program Instance big_meet_funN `{!BigMeet OT} {A : ofe} :
  BigMeet (A -np> OT) :=
  BIG_MEET (λ _ S F, OfeMor (λ a, [⊓] b :: S b, F b a) (ofe_mor_ne:=_)) _ _ _.
Next Obligation. move=> *?*. apply big_meet_ne=> ?; solve_proper. Qed.
Next Obligation.
  move=> *?? eqv ?. apply big_meet_ne=>// ?. apply (eqv _ _).
Qed.
Next Obligation. move=> *?. exact: big_meet_elim. Qed.
Next Obligation.
  move=> ??????? all o. apply big_meet_intro=> *. move: o. by apply all.
Qed.
#[export] Program Instance big_join_funN `{!∀ a : A, BigJoin (OTF a)} :
  BigJoin (funP OTF) := BIG_JOIN (λ _ S F a, [⊔] b :: S b, F b a) _ _ _.
Next Obligation.
  move=> *?? eqv ?. apply big_join_ne=>// ?. apply (eqv _ _).
Qed.
Next Obligation. move=> *?. by exact: big_join_intro. Qed.
Next Obligation.
  move=> ??????? all o. apply big_join_elim=> *. move: o. by apply all.
Qed.

(** The big meet and join flipped with [dual] *)

#[export] Program Instance big_meet_dual `{!BigJoin OT} : BigMeet (dual OT) :=
  BIG_MEET (λ _ S f, Dual ([⊔] o :: S o, undual (f o))) _ _ _.
Next Obligation. move=> *?*. by apply big_join_ne. Qed.
Next Obligation. move=> */=. by exact: (big_join_intro (undual ∘ _)). Qed.
Next Obligation. move=> */=. by exact: (big_join_elim (undual ∘ _)). Qed.

#[export] Program Instance big_join_dual `{!BigMeet OT} : BigJoin (dual OT) :=
  BIG_JOIN (λ _ S f, Dual ([⊓] o :: S o, undual (f o))) _ _ _.
Next Obligation. move=> *?*. by apply big_meet_ne. Qed.
Next Obligation. move=> */=. by exact: (big_meet_elim (undual ∘ _)). Qed.
Next Obligation. move=> */=. by exact: (big_meet_intro (undual ∘ _)). Qed.

(** ** [lfp]: Knaster-Tarski least fixed point *)

Section lfp.
  Context `{!BigMeet OT}.
  Implicit Type f : OT -p> OT.

  Local Definition lfp_def (f : OT -p> OT) : OT :=
    [⊓] o :: f o ⊑ o, o.
  Local Lemma lfp_aux : seal lfp_def. Proof. by eexists. Qed.
  Definition lfp := lfp_aux.(unseal).
  Local Lemma lfp_unseal : lfp = lfp_def. Proof. exact: seal_eq. Qed.

  (** [lfp] is monotone *)
  #[export] Instance lfp_mono : Mono lfp.
  Proof.
    rewrite lfp_unseal=> ???. by apply big_meet_mono; [|done]=>/= ? {2}<-.
  Qed.
  #[export] Instance lfp_proper : Proper ((≡) ==> (≡)) lfp.
  Proof. apply mono_proper. Qed.

  (** Unfold [lfp] *)
  Lemma lfp_unfold_2 `{!Mono f} : f (lfp f) ⊑ lfp f.
  Proof.
    rewrite lfp_unseal. apply big_meet_intro=> ??. etrans; [|done].
    by apply mono, (big_meet_elim id).
  Qed.
  Lemma lfp_unfold_1 `{!Mono f} : lfp f ⊑ f (lfp f).
  Proof.
    rewrite {1}lfp_unseal. apply (big_meet_elim id), mono, lfp_unfold_2.
  Qed.
  Lemma lfp_unfold `{!Mono f} : lfp f ≡ f (lfp f).
  Proof. apply equiv_ole. split; [apply lfp_unfold_1|apply lfp_unfold_2]. Qed.

  (** Basic induction principle *)
  Lemma lfp_ind `{!Mono f} {o} : f o ⊑ o → lfp f ⊑ o.
  Proof. rewrite lfp_unseal=> ?. by apply (big_meet_elim id). Qed.

  (** Augmenting a function with a meet *)
  Definition aug_meet `{!BinMeet OT} (f : OT -p> OT) o : _ -p> _ :=
    λ o', f (o' ⊓ o).
  #[export] Instance aug_meet_mono `{!BinMeet OT, !Mono f} : Mono2 (aug_meet f).
  Proof. move=> *?*. by apply (mono (f:=f)), mono2. Qed.
  Lemma aug_meet_nest `{!BinMeet OT, !Proper ((≡) ==> (≡)) f} {o o'} :
    aug_meet (aug_meet f o') o ≡ aug_meet f (o ⊓ o').
  Proof. unfold aug_meet=> ?. by rewrite assoc. Qed.
  Lemma aug_meet_top `{!BinMeet OT, !Otop OT, !Proper ((≡) ==> (≡)) f} :
    aug_meet f ⊤ ≡ f.
  Proof. unfold aug_meet=> ?. by rewrite right_id. Qed.

  (** Parameterized induction principle *)
  Lemma lfp_para_ind `{!BinMeet OT, !BigMeet OT, !Mono f} {o} :
    lfp (aug_meet f o) ⊑ o → lfp f ⊑ o.
  Proof.
    move=> to. rewrite -to. apply lfp_ind. etrans; [|exact lfp_unfold_2].
    apply (mono (f:=f)). by apply bin_meet_intro.
  Qed.
  Lemma lfp_para_ind' `{!BinMeet OT, !BigMeet OT, !Mono f} {o o'} :
    lfp (aug_meet f (o ⊓ o')) ⊑ o → lfp (aug_meet f o') ⊑ o.
  Proof. rewrite -aug_meet_nest. exact lfp_para_ind. Qed.
End lfp.

(** ** [gfp]: Knaster-Tarski greatest fixed point *)

Section gfp.
  Context `{!BigJoin OT}.
  Implicit Type f : OT -p> OT.

  Local Definition gfp_def (f : OT -p> OT) : OT :=
    [⊔] o :: o ⊑ f o, o.
  Local Lemma gfp_aux : seal gfp_def. Proof. by eexists. Qed.
  Definition gfp := gfp_aux.(unseal).
  Local Lemma gfp_unseal : gfp = gfp_def. Proof. exact: seal_eq. Qed.

  (** [gfp] is monotone *)
  #[export] Instance gfp_mono : Mono gfp.
  Proof.
    rewrite gfp_unseal=> ???. by apply big_join_mono; [|done]=>/= ? {1}->.
  Qed.

  (** Unfold [gfp] *)
  Lemma gfp_unfold_1 `{!Mono f} : gfp f ⊑ f (gfp f).
  Proof.
    rewrite gfp_unseal. apply big_join_elim=> ??. etrans; [done|].
    by apply mono, (big_join_intro id).
  Qed.
  Lemma gfp_unfold_2 `{!Mono f} : f (gfp f) ⊑ gfp f.
  Proof.
    rewrite {3}gfp_unseal. apply (big_join_intro id), mono, gfp_unfold_1.
  Qed.
  Lemma gfp_unfold `{!Mono f} : gfp f ≡ f (gfp f).
  Proof. apply equiv_ole. split; [apply gfp_unfold_1|apply gfp_unfold_2]. Qed.

  (** Basic coinduction principle *)
  Lemma gfp_coind `{!Mono f} {o} : o ⊑ f o → o ⊑ gfp f.
  Proof. rewrite gfp_unseal=> ?. by apply (big_join_intro id). Qed.

  (** Augmenting a function with a join *)
  Definition aug_join `{!BinJoin OT} f o : _ -p> _ := λ o', f (o' ⊔ o).
  #[export] Instance aug_join_mono `{!BinJoin OT, !Mono f} : Mono2 (aug_join f).
  Proof. move=> *?*. apply (mono (f:=f)), mono2; by [apply _| |]. Qed.
  Lemma aug_join_nest `{!BinJoin OT, !Proper ((≡) ==> (≡)) f} {o o'} :
    aug_join (aug_join f o') o ≡ aug_join f (o ⊔ o').
  Proof. unfold aug_join=> ?. by rewrite assoc. Qed.
  Lemma aug_join_bot `{!BinJoin OT, !Proper ((≡) ==> (≡)) f, !Obot OT} :
    aug_join f ⊥ ≡ f.
  Proof. unfold aug_join=> ?. by rewrite right_id. Qed.

  (** Parameterized coinduction principle *)
  Lemma gfp_para_coind `{!BinJoin OT, !BigJoin OT, !Mono f} {o} :
    o ⊑ gfp (aug_join f o) → o ⊑ gfp f.
  Proof.
    move=> to. rewrite to. apply gfp_coind. etrans; [exact gfp_unfold_1|].
    apply (mono (f:=f)). by apply bin_join_elim.
  Qed.
  Lemma gfp_para_coind' `{!BinJoin OT, !BigJoin OT, !Mono f} {o o'} :
    o ⊑ gfp (aug_join f (o ⊔ o')) → o ⊑ gfp (aug_join f o').
  Proof. rewrite -aug_join_nest. exact gfp_para_coind. Qed.
End gfp.
