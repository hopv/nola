(** * On productivity *)

From nola Require Export prelude.
From iris.algebra Require Export ofe.

(** ** [prost]: Productivity structure *)
Structure prost := Prost {
  (** Underlying OFE] *) prost_car :> ofe;
  (** Equivalences up to a level *)
    #[canonical=no] proeqv : nat → relation prost_car;
  (** [proeqv] is an equivalence relation *)
    #[canonical=no] proeqv_equivalence {k} :: Equivalence (proeqv k);
  (** [proeqv] is antitone *)
    #[canonical=no] proeqv_anti {k k' a a'} :
      k ≥ k' → proeqv k a a' → proeqv k' a a';
  (** [≡] is equivalent to universal [proeqv] *)
    #[canonical=no] equiv_proeqv {a a'} : a ≡ a' ↔ (∀ k, proeqv k a a');
}.
Add Printing Constructor prost.
Arguments proeqv {PR} : rename, simpl never.
Arguments proeqv_equivalence {PR _} : rename.
Arguments proeqv_anti {PR _ _ _ _} : rename.
Arguments equiv_proeqv {PR _ _} : rename.
Implicit Type PR : prost.

(** [proeqv_later]: [proeqv] with the level deferred by 1 *)
Definition proeqv_later {PR} k : relation PR :=
  match k with 0 => λ _ _, True | S k' => proeqv k' end.

Module ProeqvNotation.
  Notation "a ≡[ k ]≡ a'" := (proeqv k a a')
    (at level 70, k at next level, format "a  ≡[ k ]≡  a'").
  Notation "a ≡[ k ]@{ PR }≡ a'" := (proeqv (PR:=PR) k a a')
    (at level 70, k at next level, only parsing).
  Notation "(≡[ k ]≡)" := (proeqv k) (only parsing).
  Notation "(≡[ k ]@{ PR }≡)" := (proeqv (PR:=PR) k) (only parsing).
  Notation "a ≡[< k ]≡ a'" := (proeqv_later k a a')
    (at level 70, k at next level, format "a  ≡[< k ]≡  a'").
  Notation "a ≡[< k ]@{ PR }≡ a'" := (proeqv_later (PR:=PR) k a a')
    (at level 70, k at next level, only parsing).
  Notation "(≡[< k ]≡)" := (proeqv_later k) (only parsing).
  Notation "(≡[< k ]@{ PR }≡)" := (proeqv_later (PR:=PR) k) (only parsing).
End ProeqvNotation.
Import ProeqvNotation.

(** [proeqv] is proper *)
#[export] Instance proeqv_proper {PR k} :
  Proper ((≡) ==> (≡) ==> (↔)) (≡[k]@{PR}≡).
Proof.
  have pro : Proper ((≡) ==> (≡) ==> impl) (≡[k]@{PR}≡); last first.
  { move=> ?*?*. by split; apply pro. }
  move=> ?? /equiv_proeqv eq ?? /equiv_proeqv eq' ?.
  etrans; [symmetry; by apply eq|]. by etrans.
Qed.

(** [proeqv_later] is an equivalence relation *)
#[export] Instance proeqv_later_equivalence {PR k} :
  Equivalence (≡[<k]@{PR}≡).
Proof. case: k=>//=. exact _. Qed.
(** [proeqv_later] is proper *)
#[export] Instance proeqv_later_proper {PR k} :
  Proper ((≡) ==> (≡) ==> (↔)) (≡[<k]@{PR}≡).
Proof. case: k; solve_proper. Qed.
(** [proeqv] to [proeqv_later] *)
Lemma proeqv_to_later {PR k a a'} : a ≡[k]@{PR}≡ a' → a ≡[<k]≡ a'.
Proof. case: k=>//= ?. apply proeqv_anti. lia. Qed.
(** [proeqv_later] is antinone *)
Lemma proeqv_later_anti {PR k k' a a'} :
  k ≥ k' → a ≡[<k]@{PR}≡ a' → a ≡[<k']≡ a'.
Proof. case: k'=>//= ?. case: k; [lia|]=>/= ??. apply proeqv_anti. lia. Qed.

(** ** Productivity structures *)

(** Discrete structure *)
Program Definition discretePR (A : ofe) : prost := Prost A (λ _, (≡)) _ _ _.
Next Obligation. done. Qed.
Next Obligation. move=> ???. split=>// eq. apply eq, 0. Qed.
(** Unfold [proeqv] over [discretePR] *)
Lemma discrete_proeqv {A} : @proeqv (discretePR A) = λ _, (≡).
Proof. done. Qed.
(** Unfold [proeqv_later] over [discretePR] *)
Lemma discrete_proeqv_later {A k a a'} :
  a ≡[<k]@{discretePR A}≡ a' ↔ k = 0 ∨ a ≡ a'.
Proof. case: k=>/= >; [split; by [left|]|split; by [right|case]]. Qed.

(** Product *)
Program Canonical prodPR (A B : prost) : prost :=
  Prost (prodO A B) (λ k, prod_relation (≡[k]≡) (≡[k]≡)) _ _ _.
Next Obligation. move=> > ?[??]. split; by eapply proeqv_anti. Qed.
Next Obligation.
  move=> >. split. { move=> [??]?. split; by apply equiv_proeqv. }
  { move=> eq. split; apply equiv_proeqv; apply eq. }
Qed.

(** Function *)
Program Canonical funPR {A} (PRF : A → prost) : prost :=
  Prost (discrete_funO PRF) (λ k f g, ∀ a, proeqv k (f a) (g a)) _ _ _.
Next Obligation.
  move=> ???. split. { by move=> ??. } { move=> ????. by symmetry. }
  { move=> ??? e ??. etrans; by [apply e|]. }
Qed.
Next Obligation. move=> *?. by eapply proeqv_anti. Qed.
Next Obligation.
  move=> >. split. { move=> *. by apply equiv_proeqv. }
  { move=> eq ?. apply equiv_proeqv=> ?. apply eq. }
Qed.
(** Unfold [proeqv] over [funPR] *)
Lemma fun_proeqv {A PRF} : @proeqv (@funPR A PRF) = λ k f g, ∀ a, f a ≡[k]≡ g a.
Proof. done. Qed.
(** Unfold [proeqv_later] over [funPR] *)
Lemma fun_proeqv_later {A PRF k f g} :
  @proeqv_later (@funPR A PRF) k f g ↔ ∀ a, proeqv_later k (f a) (g a).
Proof. by case: k. Qed.

Module FunPRNotation.
  Notation "A -pr> PR" := (@funPR A (λ _, PR))
    (at level 99, PR at level 200, right associativity).
End FunPRNotation.

(** ** Productivity *)

(** [Productive]: Productive map *)
Notation Productive f := (∀ k, Proper ((≡[<k]≡) ==> (≡[k]≡)) f).
Notation Productive' PR PR' f :=
  (∀ k, Proper ((≡[<k]@{PR}≡) ==> (≡[k]@{PR'}≡)) f) (only parsing).
(** [Preserv]: Size-preserving map *)
Notation Preserv f := (∀ k, Proper ((≡[k]≡) ==> (≡[k]≡)) f).
Notation Preserv' PR PR' f := (∀ k, Proper ((≡[k]@{PR}≡) ==> (≡[k]@{PR'}≡)) f)
  (only parsing).

(** [Productive] entails [Preserv] *)
Lemma productive_preserv `(!Productive' PR PR' f) : Preserv f.
Proof. move=> ????. f_equiv. by apply proeqv_to_later. Qed.

(** [Preserv] entails [Proper] *)
Lemma preserv_proper `(!Preserv' PR PR' f) : Proper ((≡) ==> (≡)) f.
Proof. move=> ???. apply equiv_proeqv=> ?. f_equiv. by apply equiv_proeqv. Qed.
Lemma productive_proper `(!Productive' PR PR' f) : Proper ((≡) ==> (≡)) f.
Proof. apply preserv_proper, productive_preserv, _. Qed.

(** [pair] is size-preserving *)
#[export] Instance pair_preserv {A B : prost} {k} :
  Proper ((≡[k]≡) ==> (≡[k]≡) ==> (≡[k]≡)) (@pair A B).
Proof. exact _. Qed.

(** ** Completeness *)

(** [prochain]: Chain / Cauchy sequence over [prost] *)
Record prochain PR : Type := Prochain {
  prochain_seq :> nat → PR;
  prochain_eqv {k k'} : k ≤ k' → prochain_seq k ≡[k]≡ prochain_seq k';
}.
Add Printing Constructor prochain.
Arguments Prochain {_}. Arguments prochain_seq {_}.
Arguments prochain_eqv {_ c _ _} : rename.

(** [Cprost]: Complete [prost] *)
Class Cprost PR : Type := CPROST {
  (** Limit *)
  prolimit : prochain PR → PR;
  (** For any level [k], [prolimit c] is equivalent [c k] up to [k] *)
  prolimit_eqv {c k} : prolimit c ≡[k]≡ c k;
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

(** [Cprost] over [discretePR] *)
#[export] Program Instance discrete_cprost {A : ofe} :
  Cprost (discretePR A) := CPROST (λ c, c 0) _ _.
Next Obligation. move=> ???. apply: prochain_eqv. lia. Qed.
Next Obligation. move=> ???? eq. apply eq. Qed.

(** Project [prochain] over [prodPR] *)
Program Definition prochain_proj1 {A B} (c : prochain (prodPR A B))
  : prochain A :=
  Prochain (λ k, (c k).1) _.
Next Obligation. move=> ?? c ???/=. by apply c.(prochain_eqv). Qed.
Program Definition prochain_proj2 {A B} (c : prochain (prodPR A B))
  : prochain B :=
  Prochain (λ k, (c k).2) _.
Next Obligation. move=> ?? c ???/=. by apply c.(prochain_eqv). Qed.
(** [Cprost] over [prodPR] *)
#[export] Program Instance prod_cprost {A B} `{!Cprost A, !Cprost B} :
  Cprost (prodPR A B) :=
  CPROST (λ c, (prolimit (prochain_proj1 c), prolimit (prochain_proj2 c))) _ _.
Next Obligation. move=> *. split; exact prolimit_eqv. Qed.
Next Obligation. move=> ?*?? eq. split; apply prolimit_ne=> ?; apply eq. Qed.

(** Turn [prochain] over [funPR] *)
Program Definition prochain_app {A PRF}
  (c : prochain (@funPR A PRF)) (a : A) : prochain (PRF a) :=
  Prochain (λ k, c k a) _.
Next Obligation. move=> ?? c ????/=. by apply c.(prochain_eqv). Qed.
(** [Cprost] over [funPR] *)
#[export] Program Instance fun_cprost {A PRF} `{!∀ a, Cprost (PRF a)} :
  Cprost (@funPR A PRF) := CPROST (λ c a, prolimit (prochain_app c a)) _ _.
Next Obligation. move=> *>. by etrans; [exact prolimit_eqv|]. Qed.
Next Obligation.
  move=> > ?? eq a. apply prolimit_ne=> k. by apply (eq k a).
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

  (** Approximate [profix] by an iteration *)
  Lemma profix_iter `{!Productive f} {k} :
    profix f ≡[k]≡ f (Nat.iter k f inhabitant).
  Proof. rewrite profix_unseal. exact prolimit_eqv. Qed.

  (** Unfold [profix] *)
  Lemma profix_unfold `{!Productive f} : profix f ≡ f (profix f).
  Proof.
    apply equiv_proeqv=> k. etrans; [exact profix_iter|]=>/=. f_equiv.
    case: k; [done|]=>/= k. symmetry. by etrans; [apply profix_iter|].
  Qed.

  (** Any fixed point of [f] equals [profix f] *)
  Lemma profix_unique `{!Productive f} {a} : a ≡ f a → a ≡ profix f.
  Proof.
    move=>/= eq. apply equiv_proeqv. elim.
    { rewrite profix_unfold eq. by f_equiv. }
    move=> ??. rewrite profix_unfold eq. by f_equiv.
  Qed.

  (** [profix] is size-preserving *)
  Lemma profix_preserv `{!Productive f, !Productive g} {k} :
    (∀ a, f a ≡[k]≡ g a) → profix f ≡[k]≡ profix g.
  Proof.
    move=> eq. etrans; [exact profix_iter|].
    etrans; [|symmetry; exact profix_iter]=>/=. move: {2 3}k.
    elim=>/=; [by apply eq|]=>/= ? IH. etrans; [by apply eq|]. f_equiv.
    move: IH. apply proeqv_to_later.
  Qed.
  Lemma profix_proper `{!Productive f, !Productive g} :
    (∀ a, f a ≡ g a) → profix f ≡ profix g.
  Proof.
    move=> ?. apply equiv_proeqv=> ?. apply profix_preserv=> ?.
    by apply equiv_proeqv.
  Qed.
  Lemma profix_map_preserv {PR'} {f : PR' → PR → PR}
    `{!∀ b, Productive (f b), Pres : !∀ a, Preserv (λ b, f b a)} :
    Preserv (λ b, profix (f b)).
  Proof. move=> ????. apply profix_preserv=> ?. by apply Pres. Qed.
  Lemma profix_map_productive {PR'} {f : PR' → PR → PR}
    `{!∀ b, Productive (f b), Prod : !∀ a, Productive (λ b, f b a)} :
    Productive (λ b, profix (f b)).
  Proof. move=> ????. apply profix_preserv=> ?. by apply Prod. Qed.

  (** Relation between [profix]s *)
  Lemma profix_rel `{!Equivalence R}
    `(!Proper ((pointwise_relation _ R : relation (prochain _)) ==> R) prolimit)
    `{!Productive f, !Productive g} :
    (∀ a a', R a a' → R (f a) (g a')) → R (profix f) (profix g).
  Proof.
    move=> eq. rewrite profix_unseal /profix_def. f_equiv=>/= +.
    elim=>/= *; by apply eq.
  Qed.
  Lemma profix_ne `{!Productive f, !Productive g} {n} :
    (∀ a a', a ≡{n}≡ a' → f a ≡{n}≡ g a') → profix f ≡{n}≡ profix g.
  Proof. apply profix_rel, _. Qed.
End profix.
