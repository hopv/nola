(** * On productivity *)

From nola Require Export prelude.
From iris.algebra Require Export ofe.

(** ** [prost]: Productivity structure *)
Structure prost := Prost {
  (** Underlying OFE] *) prost_car :> ofe;
  (** Equivalences up to a level *)
    #[canonical=no] proeq : nat → relation prost_car;
  (** [proeq] is an equivalence relation *)
    #[canonical=no] proeq_equivalence {k} :: Equivalence (proeq k);
  (** [proeq] is antitone *)
    #[canonical=no] proeq_anti {k k' a a'} :
      k ≥ k' → proeq k a a' → proeq k' a a';
  (** [≡] is equivalent to universal [proeq] *)
    #[canonical=no] equiv_proeq {a a'} : a ≡ a' ↔ (∀ k, proeq k a a');
}.
Add Printing Constructor prost.
Arguments proeq {PR} : rename, simpl never.
Arguments proeq_equivalence {PR _} : rename.
Arguments proeq_anti {PR _ _ _ _} : rename.
Arguments equiv_proeq {PR _ _} : rename.
Implicit Type PR : prost.

(** [proeq] is proper *)
Local Lemma proeq_proper' {PR k} : Proper ((≡) ==> (≡) ==> impl) (@proeq PR k).
Proof.
  move=> ?? /equiv_proeq eq ?? /equiv_proeq eq' ?.
  etrans; [symmetry; by apply eq|]. by etrans.
Qed.
#[export] Instance proeq_proper {PR k} :
  Proper ((≡) ==> (≡) ==> (↔)) (@proeq PR k).
Proof. move=> ??????. by split; apply proeq_proper'. Qed.

(** [proeq_later]: [proeq] with the level deferred by 1 *)
Definition proeq_later {PR} k : relation PR :=
  match k with 0 => λ _ _, True | S k' => proeq k' end.
#[export] Instance proeq_later_equivalence {PR k} :
  Equivalence (@proeq_later PR k).
Proof. case: k=>//=. exact _. Qed.
(** [proeq] to [proeq_later] *)
Lemma proeq_to_later {PR k a a'} : proeq k a a' → @proeq_later PR k a a'.
Proof. case: k=>//= ?. apply proeq_anti. lia. Qed.
(** [proeq_later] is antinone *)
Lemma proeq_later_anti {PR k k' a a'} :
  k ≥ k' → @proeq_later PR k a a' → proeq_later k' a a'.
Proof. case: k'=>//= ?. case: k; [lia|]=>/= ??. apply proeq_anti. lia. Qed.

(** ** Productivity structures *)

(** Discrete structure *)
Definition discrete_proeq {A : ofe} : nat → relation A := λ _, (≡).
Program Definition discretePR (A : ofe) : prost := Prost A discrete_proeq _ _ _.
Next Obligation. done. Qed.
Next Obligation. move=> ???. split=>// eq. apply eq, 0. Qed.

(** Function *)
Program Canonical funPR {A} (PRF : A → prost) : prost :=
  Prost (discrete_funO PRF) (λ k f g, ∀ a, proeq k (f a) (g a)) _ _ _.
Next Obligation.
  move=> ???. split. { by move=> ??. } { move=> ????. by symmetry. }
  { move=> ??? e ??. etrans; by [apply e|]. }
Qed.
Next Obligation. move=> ?????????. by eapply proeq_anti. Qed.
Next Obligation.
  move=> ????. split. { move=> ???. by apply equiv_proeq. }
  { move=> eq ?. apply equiv_proeq=> ?. apply eq. }
Qed.
(** Unfold [proeq] over [funPR] *)
Lemma fun_proeq {A PRF} :
  @proeq (@funPR A PRF) = λ k f g, ∀ a, proeq k (f a) (g a).
Proof. done. Qed.
(** Unfold [proeq_later] over [funPR] *)
Lemma fun_proeq_later {A PRF k f g} :
  @proeq_later (@funPR A PRF) k f g ↔ ∀ a, proeq_later k (f a) (g a).
Proof. by case: k. Qed.

Module FunPRNotation.
  Notation "A -pr> PR" := (@funPR A (λ _, PR))
    (at level 99, PR at level 200, right associativity).
End FunPRNotation.

(** ** Productivity *)

(** [Productive]: Productive map *)
Notation Productive f := (∀ k, Proper (proeq_later k ==> proeq k) f).
Notation Productive' PR PR' f :=
  (∀ k, Proper (@proeq_later PR k ==> @proeq PR' k) f) (only parsing).
(** [Preserv]: Size-preserving map *)
Notation Preserv f := (∀ k, Proper (proeq k ==> proeq k) f).
Notation Preserv' PR PR' f := (∀ k, Proper (@proeq PR k ==> @proeq PR' k) f)
  (only parsing).

(** [Productive] entails [Preserv] *)
Lemma productive_preserv `{!Productive' PR PR' f} : Preserv f.
Proof. move=> ????. f_equiv. by apply proeq_to_later. Qed.

(** ** Completeness *)

(** [prochain]: Chain / Cauchy sequence over [prost] *)
Record prochain PR := Prochain {
  prochain_seq :> nat → PR;
  prochain_eq {k k'} : k ≤ k' → proeq k (prochain_seq k) (prochain_seq k');
}.
Add Printing Constructor prochain.
Arguments Prochain {_}. Arguments prochain_seq {_}.
Arguments prochain_eq {_ c _ _} : rename.

(** [Cprost]: Complete [prost] *)
Class Cprost PR := CPROST {
  (** Limit *)
  prolimit : prochain PR → PR;
  (** For any level [k], [prolimit c] equals [c k] up to [k] *)
  prolimit_eq {c k} : proeq k (prolimit c) (c k);
  (** [prolimit] is non-expansive *)
  prolimit_ne {n} :: Proper
    ((pointwise_relation _ (≡{n}≡) : relation (prochain _)) ==> (≡{n}≡))
    prolimit;
}.
Arguments CPROST {_}.

(** [prolimit] is proper *)
#[export] Instance prolimit_proper `{!Cprost PR} :
  Proper ((pointwise_relation _ (≡) : relation (prochain _)) ==> (≡))
    (@prolimit PR _).
Proof.
  move=> ???. apply equiv_dist=> ?. apply prolimit_ne=> ?. by apply equiv_dist.
Qed.

(** Turn [prochain] over [funPR] *)
Program Definition prochain_app {A PRF}
  (c : prochain (@funPR A PRF)) (a : A) : prochain (PRF a) :=
  Prochain (λ k, c k a) _.
Next Obligation. move=> ?? c ????/=. by apply c.(prochain_eq). Qed.
(** [Cprost] over [funPR] *)
#[export] Program Instance fun_cprost {A PRF} `{!∀ a, Cprost (PRF a)} :
  Cprost (@funPR A PRF) := CPROST (λ c a, prolimit (prochain_app c a)) _ _.
Next Obligation. move=> ??????. by etrans; [exact prolimit_eq|]. Qed.
Next Obligation.
  move=> ?????? eq a. apply prolimit_ne=> k. by apply (eq k a).
Qed.

(** ** Fixed point *)

Section profix.
  Context `{!Inhabited PR, !Cprost PR}.
  Implicit Type f : PR → PR.

  (** Chain for [profix] *)
  Program Definition profix_chain
    (f : PR → PR) `{!Productive f} : prochain PR :=
    Prochain (λ k, f (Nat.iter k f inhabitant)) _.
  Next Obligation.
    move=>/= ??. elim=>/=. { move=> *. by f_equiv. }
    move=> ? IH. case; [lia|]=> ??. f_equiv=>/=. apply IH. lia.
  Qed.
  (** [profix]: Fixed point over a complete [prost] *)
  Definition profix_def (f : PR → PR) `{!Productive f} : PR :=
    prolimit (profix_chain f).
  Lemma profix_aux : seal (@profix_def). Proof. by eexists _. Qed.
  Definition profix (f : PR → PR) `{!Productive f} : PR :=
    profix_aux.(unseal) f _.
  Lemma profix_unseal : @profix = @profix_def. Proof. exact: seal_eq. Qed.

  (** Unfold [profix] *)
  Lemma profix_unfold `{!Productive f} : profix f ≡ f (profix f).
  Proof.
    rewrite profix_unseal. apply equiv_proeq=> k.
    etrans; [exact prolimit_eq|]=>/=. f_equiv. case: k; [done|]=>/= k. symmetry.
    by etrans; [apply prolimit_eq|].
  Qed.

  (** Any fixed point of [f] equals [profix f] *)
  Lemma profix_unique `{!Productive f} {a} : a ≡ f a → a ≡ profix f.
  Proof.
    move=>/= eq. apply equiv_proeq. elim.
    { rewrite profix_unfold eq. by f_equiv. }
    move=> ??. rewrite profix_unfold eq. by f_equiv.
  Qed.

  (** [profix] is size-preserving *)
  Lemma profix_preserv `{!Productive f, !Productive g} {k} :
    proeq (PR:=funPR _) k f g → proeq k (profix f) (profix g).
  Proof.
    move=> eq. rewrite profix_unseal. etrans; [exact prolimit_eq|].
    etrans; [|symmetry; exact prolimit_eq]=>/=. move: {2 3}k.
    elim=>/=; [by apply eq|]=>/= ? IH. etrans; [by apply eq|]. f_equiv.
    move: IH. apply proeq_to_later.
  Qed.
  Lemma map_profix_preserv {PR'} {f : PR' → PR → PR}
    `{!∀ b, Productive (f b), Pres : !∀ a, Preserv (λ b, f b a)} :
    Preserv (λ b, profix (f b)).
  Proof. move=> ????. apply profix_preserv=> ?. by apply Pres. Qed.
  Lemma map_profix_productive {PR'} {f : PR' → PR → PR}
    `{!∀ b, Productive (f b), Prod : !∀ a, Productive (λ b, f b a)} :
    Productive (λ b, profix (f b)).
  Proof. move=> ????. apply profix_preserv=> ?. by apply Prod. Qed.

  (** [profix] is proper *)
  Lemma profix_proper `{!Equivalence R}
    `{!Proper ((pointwise_relation _ R : relation (prochain _)) ==> R) prolimit}
    `{!Productive f, !Productive g} :
    (∀ a a', R a a' → R (f a) (g a')) → R (profix f) (profix g).
  Proof.
    move=> eq. rewrite profix_unseal /profix_def. f_equiv=>/= +.
    elim=>/= *; by apply eq.
  Qed.
  Lemma profix_equiv `{!Productive f, !Productive g} :
    (∀ a a', a ≡ a' → f a ≡ g a') → profix f ≡ profix g.
  Proof. apply profix_proper. Qed.
  Lemma profix_ne `{!Productive f, !Productive g} {n} :
    (∀ a a', a ≡{n}≡ a' → f a ≡{n}≡ g a') → profix f ≡{n}≡ profix g.
  Proof. apply profix_proper. Qed.
End profix.
