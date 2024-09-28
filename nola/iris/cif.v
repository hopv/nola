(** * [cif]: Coinductive-inductive set of formulas *)

From nola.util Require Export uip (** Assume UIP over any type *).
From nola.util Require Export nary cit.
From nola.bi Require Export deriv.
From nola.iris Require Export iprop.
Import EqNotations FunNPNotation iPropAppNotation FunPRNotation DsemNotation.

Implicit Type Σ : gFunctors.

(** ** [cifcon]: Custom constructor structure for [cif] *)
#[projections(primitive)]
Record cifcon := Cifcon {
  (** Identifier *) cifc_id : Type;
  (** Selector of custom constructors *) cifc_sel :> Type;
  (** Domain for inductive parts *) cifc_idom : cifc_sel → Type;
  (** Domain for coinductive parts *) cifc_cdom : cifc_sel → Type;
  (** Data [oFunctor] *) cifc_data : cifc_sel → oFunctor;
  (** [cifc_data] is contractive *)
    cifc_data_contractive {s} :: oFunctorContractive (cifc_data s);
}.
Add Printing Constructor cifcon.
Arguments cifc_id CON : rename. Arguments cifc_sel CON : rename.
Arguments cifc_idom CON : rename. Arguments cifc_cdom CON : rename.
Arguments cifc_data CON : rename.
Arguments cifc_data_contractive CON {_} : rename.
Implicit Type CON : cifcon.

(** Big sum of [cifcon]s *)
Variant sigTCC_id {A} (CONF : A → cifcon) := .
Canonical sigTCC {A} (CONF : A → cifcon) := Cifcon (sigTCC_id CONF) (sigT CONF)
  (λ ss, (CONF _).(cifc_idom) (projT2 ss))
  (λ ss, (CONF _).(cifc_cdom) (projT2 ss))
  (λ ss, (CONF _).(cifc_data) (projT2 ss)) _.

(** ** Data types for [cif] *)

(** [cif_binsel]: Binary operator selector *)
Variant cif_binsel :=
| (** Conjunction *) cifs_and
| (** Disjunction *) cifs_or
| (** Implication *) cifs_imp
| (** Separating conjunction *) cifs_sep
| (** Magic wand *) cifs_wand.

(** [cif_unsel]: Unary operator selector *)
Variant cif_unsel :=
| (** Plainly *) cifs_plain
| (** Persistently *) cifs_pers
| (** Basic update *) cifs_bupd
| (** Except-0 *) cifs_except0.

(** [cif_sel]: Selector *)
Variant cif_sel CON :=
| (** Universal quantifier *) cifs_all (A : Type)
| (** Existential quantifier *) cifs_ex (A : Type)
| (** Binary operator *) cifs_bin (s : cif_binsel)
| (** Unary operator *) cifs_un (s : cif_unsel)
| (** Pure proposition *) cifs_pure
| (** Later *) cifs_later
| (** Custom selector *) cifs_custom (s : CON).
Arguments cifs_all {_}. Arguments cifs_ex {_}.
Arguments cifs_bin {_}.  Arguments cifs_un {_}.
Arguments cifs_pure {_}. Arguments cifs_later {_}. Arguments cifs_custom {_}.

(** [cif_idom]: Domain for inductive parts *)
Definition cif_idom CON (s : cif_sel CON) : Type :=
  match s with
  | cifs_all A | cifs_ex A => A | cifs_bin _ => bool | cifs_un _ => unit
  | cifs_pure | cifs_later => Empty_set | cifs_custom s => CON.(cifc_idom) s
  end.

(** [cif_cdom]: Domain for coinductive parts *)
Definition cif_cdom CON (s : cif_sel CON) : Type :=
  match s with
  | cifs_all _ | cifs_ex _ | cifs_bin _ | cifs_un _ | cifs_pure | cifs_later =>
      Empty_set
  | cifs_custom s => CON.(cifc_cdom) s
  end.

(** [cif_data]: Data [oFunctor] *)
Definition cif_data CON (s : cif_sel CON) : oFunctor :=
  match s with
  | cifs_all _ | cifs_ex _ | cifs_bin _ | cifs_un _ => unitO
  | cifs_pure => PropO | cifs_later => laterOF ∙
  | cifs_custom s => CON.(cifc_data) s
  end.

(** [cif_data] is contractive *)
#[export] Instance cif_data_contractive {CON s} :
  oFunctorContractive (cif_data CON s).
Proof. case s=>/=; exact _. Qed.

(** ** [cif]: Coinductive-inductive set of formulas *)
Definition cifOF CON : oFunctor :=
  citOF (cif_idom CON) (cif_cdom CON) (cif_data CON).
Definition cifPR CON Σ : prost :=
  citPR (cif_idom CON) (cif_cdom CON) (λ s, cif_data CON s $oi Σ).
Definition cifO CON Σ : ofe := cifPR CON Σ.
Definition cif CON Σ : Type := cifPR CON Σ.
Definition cifaPR CON Σ : prost :=
  citaPR (cif_idom CON) (cif_cdom CON) (λ s, cif_data CON s $oi Σ).
Definition cifaO CON Σ : ofe := cifaPR CON Σ.
Definition cifa CON Σ : Type := cifaPR CON Σ.

(** [cifOF] is contractive *)
#[export] Instance cifOF_contractive {CON} : oFunctorContractive (cifOF CON).
Proof. exact _. Qed.

(** ** Construct [cif] *)
Section cif.
  Context {CON Σ}.

  (** Basic connectives *)

  Definition cif_all {A} (Φx : A -pr> cif CON Σ) : cif CON Σ :=
    Citg (cifs_all A) Φx nullary ().
  Definition cif_ex {A} (Φx : A -pr> cif CON Σ) : cif CON Σ :=
    Citg (cifs_ex A) Φx nullary ().

  Definition cif_bin (s : cif_binsel) (Px Qx : cif CON Σ) : cif CON Σ :=
    Citg (cifs_bin s) (binary Px Qx) nullary ().
  Definition cif_and := cif_bin cifs_and.
  Definition cif_or := cif_bin cifs_or.
  Definition cif_imp := cif_bin cifs_imp.
  Definition cif_sep := cif_bin cifs_sep.
  Definition cif_wand := cif_bin cifs_wand.

  Definition cif_un (s : cif_unsel) (Px : cif CON Σ) : cif CON Σ :=
    Citg (cifs_un s) (unary Px) nullary ().
  Definition cif_plain := cif_un cifs_plain.
  Definition cif_pers := cif_un cifs_pers.
  Definition cif_bupd := cif_un cifs_bupd.
  Definition cif_except0 := cif_un cifs_except0.

  Definition cif_pure (φ : Prop) : cif CON Σ :=
    Citg cifs_pure nullary nullary φ.
  Definition cif_later (P : iProp Σ) : cif CON Σ :=
    Citg cifs_later nullary nullary (Next P%I).

  (** Custom connective *)
  Definition cif_custom (s : CON) (Φx : CON.(cifc_idom) s -pr> cif CON Σ)
    (Ψx : CON.(cifc_cdom) s -pr> cif CON Σ) (d : CON.(cifc_data) s $oi Σ)
    : cif CON Σ :=
    Citg (cifs_custom s) Φx (λ c, of_cit (Ψx c)) d.

  (** [cif] is inhabited *)
  #[export] Instance cif_inhabited : Inhabited (cif CON Σ) :=
    populate (cif_pure True).

  (** Basic connectives are size-preserving *)
  #[export] Instance cif_all_preserv {A} : Preserv (@cif_all A).
  Proof. move=> ????. by apply Citg_preserv_productive. Qed.
  #[export] Instance cif_ex_preserv {A} : Preserv (@cif_ex A).
  Proof. move=> ????. by apply Citg_preserv_productive. Qed.
  #[export] Instance cif_bin_preserv {s k} :
    Proper (proeq k ==> proeq k ==> proeq k) (cif_bin s).
  Proof. move=> ??????. apply Citg_preserv_productive=>//. by f_equiv. Qed.
  #[export] Instance cif_un_preserv {s} : Preserv (cif_un s).
  Proof. move=> ????. apply Citg_preserv_productive=>//. by f_equiv. Qed.

  (** Custom connectives are size-preserving over the inductive arguments
    and productive over the coinductive arguments *)
  #[export] Instance cif_custom_preserv_productive {s k} :
    Proper (proeq k ==> proeq_later k ==> (≡) ==> proeq k) (cif_custom s).
  Proof.
    move=> ?????????. apply Citg_preserv_productive=>//. by destruct k as [|k].
  Qed.

  (** Non-expansiveness *)
  #[export] Instance cif_all_ne {A} : NonExpansive (@cif_all A).
  Proof. solve_proper. Qed.
  #[export] Instance cif_all_proper {A} : Proper ((≡) ==> (≡)) (@cif_all A).
  Proof. apply ne_proper, _. Qed.
  #[export] Instance cif_ex_ne {A} : NonExpansive (@cif_ex A).
  Proof. solve_proper. Qed.
  #[export] Instance cif_ex_proper {A} : Proper ((≡) ==> (≡)) (@cif_ex A).
  Proof. apply ne_proper, _. Qed.
  #[export] Instance cif_bin_ne {s} : NonExpansive2 (cif_bin s).
  Proof. move=> ???????. apply Citg_ne; solve_proper. Qed.
  #[export] Instance cif_bin_proper {s} :
    Proper ((≡) ==> (≡) ==> (≡)) (cif_bin s).
  Proof. apply ne_proper_2, _. Qed.
  #[export] Instance cif_un_ne {s} : NonExpansive (cif_un s).
  Proof. solve_proper. Qed.
  #[export] Instance cif_un_proper {s} : Proper ((≡) ==> (≡)) (cif_un s).
  Proof. apply ne_proper, _. Qed.
  #[export] Instance cif_pure_ne : NonExpansive cif_pure.
  Proof. move=> ????. by apply Citg_ne. Qed.
  #[export] Instance cif_pure_proper : Proper ((≡) ==> (≡)) cif_pure.
  Proof. apply ne_proper, _. Qed.
  #[export] Instance cif_later_contractive : Contractive cif_later.
  Proof. move=> ????. by apply Citg_ne. Qed.
  #[export] Instance cif_later_proper : Proper ((≡) ==> (≡)) cif_later.
  Proof. apply ne_proper, _. Qed.
  #[export] Instance cif_custom_ne {s} : NonExpansive3 (cif_custom s).
  Proof. move=> ??????????. apply Citg_ne=>// ?. by f_equiv. Qed.
  #[export] Instance cif_custom_proper {s} :
    Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) (cif_custom s).
  Proof. move=> ??????????. apply cif_custom_ne; by apply equiv_dist. Qed.

  (** Discreteness *)
  #[export] Instance cif_all_discrete {A} `{!∀ a : A, Discrete (Φx a)} :
    Discrete (cif_all Φx).
  Proof. exact _. Qed.
  #[export] Instance cif_ex_discrete {A} `{!∀ a : A, Discrete (Φx a)} :
    Discrete (cif_ex Φx).
  Proof. exact _. Qed.
  #[export] Instance cif_bin_discrete {s} `{!Discrete Px, !Discrete Qx} :
    Discrete (cif_bin s Px Qx).
  Proof. exact _. Qed.
  #[export] Instance cif_un_discrete {s} `{!Discrete Px} :
    Discrete (cif_un s Px).
  Proof. exact _. Qed.
  #[export] Instance cif_pure_discrete {φ} : Discrete (cif_pure φ).
  Proof. exact _. Qed.
  #[export] Instance cif_custom_discrete {s}
    `{!∀ i, Discrete (Φx i), !∀ c, Discrete (Ψx c), !Discrete d} :
    Discrete (cif_custom s Φx Ψx d).
  Proof. exact _. Qed.
End cif.

Declare Scope cif_scope.
Delimit Scope cif_scope with cif.
Bind Scope cif_scope with cif.
Notation "∀ x .. y , Px" :=
  (cif_all (λ x, .. (cif_all (λ y, Px%cif)) ..)) : cif_scope.
Notation "∃ x .. y , Px" :=
  (cif_ex (λ x, .. (cif_ex (λ y, Px%cif)) ..)) : cif_scope.
Infix "∧" := cif_and : cif_scope. Infix "∨" := cif_or : cif_scope.
Infix "→" := cif_imp : cif_scope.
Infix "∗" := cif_sep : cif_scope. Infix "-∗" := cif_wand : cif_scope.
Notation "■ Px" := (cif_plain Px) : cif_scope.
Notation "□ Px" := (cif_pers Px) : cif_scope.
Notation "|==> Px" := (cif_bupd Px) : cif_scope.
Notation "◇ Px" := (cif_except0 Px) : cif_scope.
Notation "⌜ φ ⌝" := (cif_pure φ) : cif_scope.
Notation "'True'" := (cif_pure True) : cif_scope.
Notation "'False'" := (cif_pure False) : cif_scope.
Notation "▷ P" := (cif_later P) : cif_scope.

Implicit Type JUDG : ofe.

(** ** Semantics for [cifcon] *)
#[projections(primitive)]
Record SemCifcon (JUDG : ofe) CON Σ := SEM_CIFCON {
  (** Semantics *)
  sem_cifc :> ((JUDG -n> iProp Σ) -d> cif CON Σ -d> iProp Σ) →
    (JUDG -n> iProp Σ) → ∀ s, (CON.(cifc_idom) s -d> iProp Σ) →
    (CON.(cifc_cdom) s -d> cif CON Σ) → CON.(cifc_data) s $oi Σ → iProp Σ;
  (** [sem_cifc] is non-expansive over usual arguments
    and contractive over the self-reference *)
  sem_cifc_ne {n} :: Proper
    (dist_later n ==> pointwise_relation _ (forall_relation (λ _,
      (≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡)))) sem_cifc;
}.
Existing Class SemCifcon.
Add Printing Constructor SemCifcon.
Arguments SEM_CIFCON {_ _ _} _ _. Arguments sem_cifc {_ _ _ semc} : rename.
Arguments sem_cifc_ne {_ _ _ semc _} : rename.
Hint Mode SemCifcon - ! - : typeclass_instances.

(** ** [cif_sem]: Semantics of [cif] *)
Section iris.
  Context `{!SemCifcon JUDG CON Σ}.
  Implicit Type sm : (JUDG -n> iProp Σ) -d> cif CON Σ -d> iProp Σ.

  (** [cif_bsem]: Base semantics for [cif] *)
  Definition cif_bsem sm δ s :
    (cif_idom CON s -d> iProp Σ) → (cif_cdom CON s -d> cif CON Σ) →
        cif_data CON s $oi Σ → iProp Σ :=
    match s with
    | cifs_all _ => λ Φ _ _, ∀ a, Φ a | cifs_ex _ => λ Φ _ _, ∃ a, Φ a
    | cifs_bin s => λ Φ _ _, let P := Φ true in let Q := Φ false in
        match s with
        | cifs_and => P ∧ Q | cifs_or => P ∨ Q | cifs_imp => P → Q
        | cifs_sep => P ∗ Q | cifs_wand => P -∗ Q
        end
    | cifs_un s => λ Φ _ _, let P := Φ () in
        match s with
        | cifs_plain => ■ P | cifs_pers => □ P | cifs_bupd => |==> P
        | cifs_except0 => ◇ P
        end
    | cifs_pure => λ _ _ φ, ⌜φ⌝ | cifs_later => λ _ _ lP, ▷ later_car lP
    | cifs_custom s => sem_cifc sm δ s
    end%I.

  (** [cif_bsem] is non-expansive over usual arguments
    and contractive over the self-reference *)
  #[export] Instance cif_bsem_ne {n} : Proper
    (dist_later n ==> pointwise_relation _ (forall_relation (λ _,
      (≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡)))) cif_bsem.
  Proof.
    move=> ????. case=>/=; try solve_proper.
    { move=> ????????. by apply later_contractive. } { by apply sem_cifc_ne. }
  Qed.

  (** [cif_sem_gen]: Generator of [cif_sem] *)
  Definition cif_sem_gen sm : (JUDG -n> iProp Σ) -d> cif CON Σ -d> iProp Σ :=
    λ δ, cit_fold (cif_bsem sm δ).
  #[export] Instance cif_sem_gen_contractive : Contractive cif_sem_gen.
  Proof.
    move=> ??????. apply cit_fold_ne_gen=>// ??????????. by apply cif_bsem_ne.
  Qed.

  (** [cif_sem]: Semantics of [cif] *)
  Definition cif_sem' : (JUDG -n> iProp Σ) -d> cif CON Σ -d> iProp Σ :=
    fixpoint cif_sem_gen.
  Definition cif_sem : (JUDG -n> iProp Σ) -d> cif CON Σ -d> iProp Σ :=
    cif_sem_gen cif_sem'.
  (** Unfold [cif_sem'] *)
  Lemma cif_sem'_unfold : cif_sem' ≡ cif_sem.
  Proof. apply fixpoint_unfold. Qed.
  Lemma cif_sem'_app_unfold {δ Px} : cif_sem' δ Px ≡ cif_sem δ Px.
  Proof. apply cif_sem'_unfold. Qed.

  (** [cif_sem] is non-expansive *)
  #[export] Instance cif_sem_ne {δ} : NonExpansive (cif_sem δ).
  Proof.
    move=> ??*. apply: cit_fold_ne=>//. move=> ??*?*?*. by apply cif_bsem_ne.
  Qed.
  #[export] Instance cif_sem_proper {δ} : Proper ((≡) ==> (≡)) (cif_sem δ).
  Proof. apply ne_proper, _. Qed.
  #[export] Instance cif_sem'_ne {δ} : NonExpansive (cif_sem' δ).
  Proof. move=> ???. rewrite !cif_sem'_app_unfold. solve_proper. Qed.
  #[export] Instance cif_sem'_proper {δ} : Proper ((≡) ==> (≡)) (cif_sem' δ).
  Proof. apply ne_proper, _. Qed.
  (** [Dsem] over [cif] *)
  #[export] Instance cif_dsem : Dsem JUDG (cifO CON Σ) (iProp Σ) :=
    DSEM (λ δ, cif_sem δ) _.
End iris.

(** ** Element [cifcon] *)

(** [Ecifcon]: Element [cifcon] *)
#[projections(primitive)]
Class Ecifcon CON' CON := ECIFCON {
  ecifc_sel : CON' → CON;
  ecifc_idom s : CON.(cifc_idom) (ecifc_sel s) = CON'.(cifc_idom) s;
  ecifc_cdom s : CON.(cifc_cdom) (ecifc_sel s) = CON'.(cifc_cdom) s;
  ecifc_data s : CON.(cifc_data) (ecifc_sel s) = CON'.(cifc_data) s;
}.
Arguments ECIFCON {_ _}.
Hint Mode Ecifcon ! - : typeclass_instances.

(** Inclusion into [sigTCC] *)
Definition sigT_ecifcon {A CONF a} :
  Ecifcon (CONF a) (@sigTCC A CONF) :=
  ECIFCON (CON:=sigTCC _) (existT a)
    (λ _, eq_refl) (λ _, eq_refl) (λ _, eq_refl).

(** ** [cif_ecustom]: Custom constructor under [Ecifcon] *)
Definition cif_ecustom_def CON' `{!Ecifcon CON' CON} {Σ} (s : CON')
  (Φx : CON'.(cifc_idom) s -pr> cif CON Σ)
  (Ψx : CON'.(cifc_cdom) s -pr> cif CON Σ) (d : CON'.(cifc_data) s $oi Σ)
  : cif CON Σ :=
  cif_custom (ecifc_sel s) (λ i, Φx (rew[id] ecifc_idom s in i))
    (λ c, Ψx (rew[id] ecifc_cdom s in c))
    (rew[λ F, F $oi Σ] eq_sym (ecifc_data s) in d).
Lemma cif_ecustom_aux : seal (@cif_ecustom_def). Proof. by eexists _. Qed.
Definition cif_ecustom CON' `{!Ecifcon CON' CON} {Σ} (s : CON')
  (Φx : CON'.(cifc_idom) s -pr> cif CON Σ)
  (Ψx : CON'.(cifc_cdom) s -pr> cif CON Σ) (d : CON'.(cifc_data) s $oi Σ)
  : cif CON Σ :=
  cif_ecustom_aux.(unseal) _ _ _ _ s Φx Ψx d.
Lemma cif_ecustom_unseal : @cif_ecustom = @cif_ecustom_def.
Proof. exact: seal_eq. Qed.

Section cif_ecustom.
  Context `{!Ecifcon CON' CON} {Σ}.

  (** Custom connectives are size-preserving over the inductive arguments
    and productive over the coinductive arguments *)
  #[export] Instance cif_ecustom_preserv_productive {s k} :
    Proper (proeq k ==> proeq_later k ==> (≡) ==> proeq k)
      (cif_ecustom CON' (Σ:=Σ) s).
  Proof.
    rewrite cif_ecustom_unseal=> ????? /fun_proeq_later eqc ???.
    apply cif_custom_preserv_productive.
    { by move. } { by apply fun_proeq_later. }
    move: (CON.(cifc_data) (ecifc_sel s)) (ecifc_data s)=> ??. by subst.
  Qed.

  (** Custom connectives are non-expansive *)
  #[export] Instance cif_ecustom_ne {s} :
    NonExpansive3 (cif_ecustom CON' (Σ:=Σ) s).
  Proof.
    rewrite cif_ecustom_unseal=> ??????????. apply cif_custom_ne.
    { by move. } { by move. }
    move: (CON.(cifc_data) (ecifc_sel s)) (ecifc_data s)=> ??. by subst.
  Qed.
  #[export] Instance cif_ecustom_proper {s} :
    Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) (cif_ecustom CON' (Σ:=Σ) s).
  Proof. move=> ??????????. apply cif_ecustom_ne; by apply equiv_dist. Qed.

  (** Discreteness of custom connectives *)
  #[export] Instance cif_ecustom_discrete {s}
    `{!∀ i, Discrete (Φx i), !∀ c, Discrete (Ψx c), !Discrete d} :
    Discrete (cif_ecustom CON' (Σ:=Σ) s Φx Ψx d).
  Proof.
    rewrite cif_ecustom_unseal. apply: cif_custom_discrete.
    move: (CON.(cifc_data) (ecifc_sel s)) (ecifc_data s)=> ??. by subst.
  Qed.
End cif_ecustom.

(** Semantics of an element [cifcon] *)
#[projections(primitive)]
Record SemEcifcon JUDG CON' CON Σ := SEM_ECIFCON {
  (** Semantics *)
  sem_ecifc :> ((JUDG -n> iProp Σ) -d> cif CON Σ -d> iProp Σ) →
    (JUDG -n> iProp Σ) → ∀ s,
    (CON'.(cifc_idom) s -d> iProp Σ) → (CON'.(cifc_cdom) s -d> cif CON Σ) →
      CON'.(cifc_data) s $oi Σ → iProp Σ;
  (** [sem_ecifc] is non-expansive over usual arguments
    and contractive over the self-reference *)
  sem_ecifc_ne {n} :: Proper
    (dist_later n ==> pointwise_relation _ (forall_relation (λ _,
      (≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡)))) sem_ecifc;
}.
Existing Class SemEcifcon.
Add Printing Constructor SemEcifcon.
Arguments SEM_ECIFCON {_ _ _ _} _ _.
Arguments sem_ecifc {_ _ _ _ semec} : rename.
Arguments sem_ecifc_ne {_ _ _ _ semec _ _} : rename.
Hint Mode SemEcifcon - ! - - : typeclass_instances.

(** [SemCifcon] over [sigT] by [SemEcifcon] *)
Program Definition sigT_sem_cifcon {JUDG A}
  `{semec : !∀ a, SemEcifcon JUDG (CONF a) (@sigTCC A CONF) Σ}
  : SemCifcon JUDG (sigTCC CONF) Σ :=
  SEM_CIFCON (λ sm δ s, semec _ sm δ (projT2 s)) _.
Next Obligation. move=> *?*???*?*?*. by apply sem_ecifc_ne. Qed.

(** Inclusion with respect to [SemEcifcon] and [SemCifcon] *)
Class EsemEcifcon JUDG CON' CON Σ `{!Ecifcon CON' CON}
  `{!SemEcifcon JUDG CON' CON Σ, !SemCifcon JUDG CON Σ} :=
  esem_ecifc : ∀ {sm δ s Φ Ψx d},
    sem_cifc (CON:=CON) sm δ (ecifc_sel s) (λ i, Φ (rew[id] ecifc_idom s in i))
      (λ c, Ψx (rew[id] ecifc_cdom s in c))
      (rew[λ F, F $oi Σ] eq_sym (ecifc_data s) in d) =
      sem_ecifc (CON':=CON') (CON:=CON) sm δ s Φ Ψx d.
Hint Mode EsemEcifcon - ! - - - - - : typeclass_instances.

(** [EsemEcifcon] into [sigT] *)
Lemma sigT_esem_cifcon {JUDG A}
  `{semec : !∀ a, SemEcifcon JUDG (CONF a) (@sigTCC A CONF) Σ} {a} :
  EsemEcifcon (Ecifcon0:=sigT_ecifcon) (SemCifcon0:=sigT_sem_cifcon)
    JUDG (CONF a) (sigTCC CONF) Σ.
Proof. done. Qed.

Section cif_ecustom.
  Context `{!Ecifcon CON' CON, !SemCifcon JUDG CON Σ,
    !SemEcifcon JUDG CON' CON Σ, !EsemEcifcon JUDG CON' CON Σ}.

  (** Semantics of [cif_ecustom] *)
  Lemma sem_ecustom {δ s Φx Ψx d} :
    cif_sem δ (cif_ecustom CON' s Φx Ψx d) ⊣⊢
      sem_ecifc cif_sem δ s (λ i, ⟦ Φx i ⟧(δ)) Ψx d.
  Proof.
    rewrite cif_ecustom_unseal /= -esem_ecifc. apply equiv_dist=> n.
    apply sem_cifc_ne=>// >; [|by rewrite to_of_cit].
    apply dist_dist_later, equiv_dist, cif_sem'_unfold.
  Qed.
  Lemma sem'_ecustom {δ s Φx Ψx d} :
    ⟦ cif_ecustom CON' s Φx Ψx d ⟧(δ) ⊣⊢
      sem_ecifc cif_sem δ s (λ i, ⟦ Φx i ⟧(δ)) Ψx d.
  Proof. exact sem_ecustom. Qed.
End cif_ecustom.

(** ** [AsCif]: Reify [iProp] into [cif] *)
Class AsCif `{!SemCifcon JUDG CON Σ} (Φ : (JUDG -n> iProp Σ) → iProp Σ) :=
  AS_CIF {
  as_cif : cif CON Σ;
  sem_as_cif {δ} : cif_sem δ as_cif ⊣⊢ Φ δ;
}.
Arguments AsCif {_} CON {_ _}. Arguments AS_CIF {_ _ _ _ _} _ _.
Arguments as_cif {_ _ _ _} Φ {_}. Arguments sem_as_cif {_ _ _ _ _ _ _}.

Section as_cif.
  Context `{!SemCifcon JUDG CON Σ}.

  (** Instances of [AsCif] *)
  #[export] Program Instance sem_cif_as_cif {Px} :
    AsCif CON (λ δ, cif_sem (CON:=CON) δ Px) | 100 := AS_CIF Px _.
  Next Obligation. done. Qed.
  #[export] Program Instance all_as_cif `{!∀ a : A, AsCif CON (Φ a)} :
    AsCif CON (λ δ, ∀ a, Φ a δ)%I | 5 := AS_CIF (∀ a, as_cif (Φ a)) _.
  Next Obligation. move=>/= *. f_equiv=> ?. exact sem_as_cif. Qed.
  #[export] Program Instance ex_as_cif `{!∀ a : A, AsCif CON (Φ a)} :
    AsCif CON (λ δ, ∃ a : A, Φ a δ)%I | 5 := AS_CIF (∃ a, as_cif (Φ a)) _.
  Next Obligation. move=>/= *. f_equiv=> ?. exact sem_as_cif. Qed.
  #[export] Program Instance and_as_cif
    `{!AsCif CON Φ, !AsCif CON Ψ} :
    AsCif CON (λ δ, Φ δ ∧ Ψ δ)%I | 5 := AS_CIF (as_cif Φ ∧ as_cif Ψ) _.
  Next Obligation. move=>/= *. f_equiv; exact sem_as_cif. Qed.
  #[export] Program Instance or_as_cif
    `{!AsCif CON Φ, !AsCif CON Ψ} :
    AsCif CON (λ δ, Φ δ ∨ Ψ δ)%I | 5 := AS_CIF (as_cif Φ ∨ as_cif Ψ) _.
  Next Obligation. move=>/= *. f_equiv; exact sem_as_cif. Qed.
  #[export] Program Instance imp_as_cif
    `{!AsCif CON Φ, !AsCif CON Ψ} :
    AsCif CON (λ δ, Φ δ → Ψ δ)%I | 5 := AS_CIF (as_cif Φ → as_cif Ψ) _.
  Next Obligation. move=>/= *. f_equiv; exact sem_as_cif. Qed.
  #[export] Program Instance sep_as_cif
    `{!AsCif CON Φ, !AsCif CON Ψ} :
    AsCif CON (λ δ, Φ δ ∗ Ψ δ)%I | 5 := AS_CIF (as_cif Φ ∗ as_cif Ψ) _.
  Next Obligation. move=>/= *. f_equiv; exact sem_as_cif. Qed.
  #[export] Program Instance wand_as_cif
    `{!AsCif CON Φ, !AsCif CON Ψ} :
    AsCif CON (λ δ, Φ δ -∗ Ψ δ)%I | 5 := AS_CIF (as_cif Φ -∗ as_cif Ψ) _.
  Next Obligation. move=>/= *. f_equiv; exact sem_as_cif. Qed.
  #[export] Program Instance plain_as_cif `{!AsCif CON Φ} :
    AsCif CON (λ δ, ■ Φ δ)%I | 5 := AS_CIF (■ as_cif Φ) _.
  Next Obligation. move=>/= *. f_equiv. exact sem_as_cif. Qed.
  #[export] Program Instance pers_as_cif `{!AsCif CON Φ} :
    AsCif CON (λ δ, □ Φ δ)%I | 5 := AS_CIF (□ as_cif Φ) _.
  Next Obligation. move=>/= *. f_equiv. exact sem_as_cif. Qed.
  #[export] Program Instance bupd_as_cif `{!AsCif CON Φ} :
    AsCif CON (λ δ, |==> Φ δ)%I | 5 := AS_CIF (|==> as_cif Φ) _.
  Next Obligation. move=>/= *. f_equiv. exact sem_as_cif. Qed.
  #[export] Program Instance except_0_as_cif `{!AsCif CON Φ} :
    AsCif CON (λ δ, ◇ Φ δ)%I | 5 := AS_CIF (◇ as_cif Φ) _.
  Next Obligation. move=>/= *. f_equiv. exact sem_as_cif. Qed.
  #[export] Program Instance pure_as_cif {φ} : AsCif CON (λ _, ⌜φ⌝)%I | 5 :=
    AS_CIF ⌜φ⌝ _.
  Next Obligation. done. Qed.
  #[export] Program Instance later_as_cif {P} : AsCif CON (λ _, ▷ P)%I | 100 :=
    AS_CIF (▷ P) _.
  Next Obligation. done. Qed.
End as_cif.
