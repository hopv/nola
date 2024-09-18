(** * On productivity *)

From nola Require Export prelude.

(** ** [prost]: Productivity structure *)
Structure prost := Prost {
  (** Underlying set *) prost_car :> Type;
  (** Equivalences up to a level *)
    proeq : nat → relation prost_car;
  (** [proeq] is an equivalence relation *)
    #[canonical=no] proeq_equivalence :: ∀ {n}, Equivalence (proeq n);
  (** [proeq] is antitone *)
    #[canonical=no] proeq_anti :
      ∀ {m n a a'}, m ≥ n → proeq m a a' → proeq n a a';
}.
Add Printing Constructor prost.
Arguments proeq {PR} : rename. Arguments proeq_equivalence {PR _} : rename.
Arguments proeq_anti {PR _ _ _ _} : rename.
Implicit Type PR : prost.

(** [proeq_later]: [proeq] with the level deferred by 1 *)
Definition proeq_later {PR} n : relation PR :=
  match n with 0 => λ _ _, True | S n' => proeq n' end.
#[export] Instance proeq_later_equivalence {PR n} :
 Equivalence (@proeq_later PR n).
Proof. case: n=>//=. exact _. Qed.
(** [proeq] to [proeq_later] *)
Lemma proeq_to_later {PR n a a'} : proeq n a a' → @proeq_later PR n a a'.
Proof. case: n=>//= ?. apply proeq_anti. lia. Qed.
(** [proeq_later] is antinone *)
Lemma proeq_later_anti {PR m n a a'} :
  m ≥ n → @proeq_later PR m a a' → proeq_later n a a'.
Proof. case: n=>//= ?. case: m; [lia|]=>/= ??. apply proeq_anti. lia. Qed.

(** [proeqa]: [proeq] over all levels *)
Definition proeqa {PR} (a a' : PR) : Prop := ∀ n, proeq n a a'.
#[export] Instance proeqa_equivalence {PR} : Equivalence (@proeqa PR).
Proof.
  split. { by move=> ??. } { move=> ????. by symmetry. }
  { move=> ??? E E' n. move: (E n) (E' n)=> ??. by etrans. }
Qed.

(** ** Productivity structures *)

(** Discrete structure *)
Definition discrete_eq {A} : nat → relation A := λ _, (=).
Arguments discrete_eq /.
Program Definition discretePR (A : Type) : prost := Prost A discrete_eq _ _.
Next Obligation. done. Qed.

(** Function *)
Definition fun_proeq {A} {PRF : A → prost} : nat → relation (∀ a, PRF a) :=
  λ n f g, ∀ a, proeq n (f a) (g a).
Arguments fun_proeq /.
Program Canonical funPR {A} (PRF : A → prost) : prost :=
  Prost (∀ a, PRF a) fun_proeq _ _.
Next Obligation.
  move=> ???. split. { by move=> ??. } { move=> ????. by symmetry. }
  { move=> ??? e ??. etrans; by [apply e|]. }
Qed.
Next Obligation. move=> ?????????. by eapply proeq_anti. Qed.
(** Turn from [proeq] etc. over a function *)
Lemma proeq_fun {A PRF} {n f g a} :
  @proeq (@funPR A PRF) n f g → proeq n (f a) (g a).
Proof. done. Qed.
Lemma proeq_later_fun {A PRF} {n f g a} :
  @proeq_later (@funPR A PRF) n f g → proeq_later n (f a) (g a).
Proof. case: n=>//=. Qed.
Lemma proeqa_fun {A PRF} {f g a} :
  @proeqa (@funPR A PRF) f g → proeqa (f a) (g a).
Proof. move=> E ?. apply E. Qed.

(** ** Productivity *)

(** [Productive]: Productive map *)
Notation Productive f := (∀ n, Proper (proeq_later n ==> proeq n) f).
Notation Productive' PR PR' f :=
  (∀ n, Proper (@proeq_later PR n ==> @proeq PR' n) f) (only parsing).
(** [Preserv]: Size-preserving map *)
Notation Preserv f := (∀ n, Proper (proeq n ==> proeq n) f).
Notation Preserv' PR PR' f := (∀ n, Proper (@proeq PR n ==> @proeq PR' n) f)
  (only parsing).

(** [Productive] entails [Preserv] *)
Lemma productive_preserv `{!Productive' PR PR' f} : Preserv f.
Proof. move=> ????. f_equiv. by apply proeq_to_later. Qed.

(** ** Completeness *)

(** [prochain]: Chain / Cauchy sequence over [prost] *)
Record prochain PR := Prochain {
  prochain_seq :> nat → PR;
  prochain_eq : ∀{m n}, m ≤ n → proeq m (prochain_seq m) (prochain_seq n);
}.
Add Printing Constructor prochain.
Arguments Prochain {_}. Arguments prochain_seq {_}. Arguments prochain_eq {_}.

(** [Cprost]: Complete [prost] *)
Class Cprost PR := CPROST {
  prolimit : prochain PR → PR;
  prolimit_eq : ∀{c n}, proeq n (prolimit c) (c n);
}.
Arguments CPROST {_}.

(** Turn [prochain] over [funP] *)
Program Definition prochain_app {A} {PRF : A → prost}
  (c : prochain (∀ a, PRF a)) (a : A) : prochain (PRF a) :=
  Prochain (λ n, c n a) _.
Next Obligation. move=> ?? c ????/=. by apply c.(prochain_eq). Qed.
(** [Cprost] over [funP] *)
#[export] Program Instance fun_cprost {A} {PRF : A → prost}
  `{!∀ a, Cprost (PRF a)} :
  Cprost (∀ a, PRF a) := CPROST (λ c a, prolimit (prochain_app c a)) _.
Next Obligation. move=> ??????. by etrans; [exact prolimit_eq|]. Qed.

(** ** Fixed point *)

Section profix.
  Context `{!Inhabited PR, !Cprost PR}.
  Implicit Type f : PR → PR.

  (** Chain for [profix] *)
  Program Definition profix_chain
    (f : PR → PR) `{!Productive f} : prochain PR :=
    Prochain (λ n, f (Nat.iter n f inhabitant)) _.
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
  Lemma profix_unfold `{!Productive f} : proeqa (profix f) (f (profix f)).
  Proof.
    rewrite profix_unseal=> n. etrans; [exact prolimit_eq|]=>/=. f_equiv.
    case: n; [done|]=>/= n. symmetry. by etrans; [apply prolimit_eq|].
  Qed.
  Lemma profix_unfold' `{!Productive f} {n} : proeq n (profix f) (f (profix f)).
  Proof. apply profix_unfold. Qed.

  (** [profix] is size-preserving *)
  Lemma profix_preserv `{!Productive f, !Productive g} {n} :
    proeq n f g → proeq n (profix f) (profix g).
  Proof.
    move=> eq. rewrite profix_unseal. etrans; [exact prolimit_eq|].
    etrans; [|symmetry; exact prolimit_eq]=>/=. move: {2 3}n.
    elim=>/=; [by apply eq|]=>/= ? IH. etrans; [by apply eq|]. f_equiv.
    move: IH. apply proeq_to_later.
  Qed.
End profix.
