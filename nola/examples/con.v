(** * Formula and judgment constructors *)

From nola.util Require Import tagged.
From nola.iris Require Export cif inv pborrow.
Import ProdNotation FunPRNotation DsemNotation CsemNotation iPropAppNotation.

Implicit Type (Σ : gFunctors) (N : namespace) (TY : synty) (α : lft) (FM : ofe)
  (A : Type).

(** ** Invariant *)

(** [inv_tokCT]: Constructor for [inv_tok] *)
Variant inv_tokCT_id := .
Definition inv_tokCT :=
  Cifcon inv_tokCT_id namespace (λ _, Empty_set) (λ _, unit) (λ _, unitO) _.
(** [inv_tokC]: [inv_tokCT] registered *)
Notation inv_tokC := (inC inv_tokCT).

Section inv_tokC.
  Context `{!inv_tokC CON} {Σ}.
  (** [cif_inv_tok]: Formula *)
  Definition cif_inv_tok N (Px : cif CON Σ) : cif CON Σ :=
    cif_in inv_tokCT N nullary (unary Px) ().
  (** [cif_inv] is non-expansive *)
  #[export] Instance cif_inv_tok_ne {N} : NonExpansive (cif_inv_tok N).
  Proof. move=> ????. apply cif_in_ne; solve_proper. Qed.
  #[export] Instance cif_inv_tok_proper {N} :
    Proper ((≡) ==> (≡)) (cif_inv_tok N).
  Proof. apply ne_proper, _. Qed.
  (** [cif_inv] is productive *)
  #[export] Instance cif_inv_tok_productive {N} : Productive (cif_inv_tok N).
  Proof.
    move=> ????. apply cif_in_preserv_productive=>//. by apply fun_proeq_later.
  Qed.

  Context `{!inv'GS (cifOF CON) Σ}.
  (** Semantics of [inv_tokCT] *)
  #[export] Program Instance inv_tokCT_ecsem {JUDG}
    : Ecsem inv_tokCT CON JUDG Σ :=
    ECSEM (λ _ _ N _ Φx _, inv_tok N (Φx ())) _.
  Next Obligation. move=>/= ???*???*?? eqv ???. f_equiv. apply eqv. Qed.
End inv_tokC.
(** [inv_tokCS]: Semantics of [inv_tokCT] registered *)
Notation inv_tokCS := (inCS inv_tokCT).

(** Reify [inv_tok] *)
#[export] Program Instance inv_tok_as_cif `{!Csem CON JUDG Σ}
  `{!inv_tokC CON, !inv'GS (cifOF CON) Σ, !inv_tokCS CON JUDG Σ} {N Px} :
  AsCif CON (λ _, inv_tok N Px) := AS_CIF (cif_inv_tok N Px) _.
Next Obligation. move=>/= *. by rewrite sem_cif_in. Qed.

(** ** Borrow *)

(** [bor_tokCT]: Constructor for [bor_tok] *)
Variant bor_tokCT_id := .
Definition bor_tokCT :=
  Cifcon bor_tokCT_id lft (λ _, Empty_set) (λ _, unit) (λ _, unitO) _.
(** [bor_tokC]: [bor_tokCT] registered *)
Notation bor_tokC := (inC bor_tokCT).

Section bor_tokC.
  Context `{!bor_tokC CON} {Σ}.
  (** [cif_bor_tok]: Formula *)
  Definition cif_bor_tok α (Px : cif CON Σ) : cif CON Σ :=
    cif_in bor_tokCT α nullary (unary Px) ().
  (** [cif_bor_tok] is non-expansive *)
  #[export] Instance cif_bor_tok_ne {α} : NonExpansive (cif_bor_tok α).
  Proof. move=> ????. apply cif_in_ne; solve_proper. Qed.
  #[export] Instance cif_bor_tok_proper {α} :
    Proper ((≡) ==> (≡)) (cif_bor_tok α).
  Proof. apply ne_proper, _. Qed.
  (** [cif_bor_tok] is productive *)
  #[export] Instance cif_bor_tok_productive {α} : Productive (cif_bor_tok α).
  Proof.
    move=> ????. apply cif_in_preserv_productive=>//. by apply fun_proeq_later.
  Qed.

  Context `{!borrowGS (cifOF CON) Σ}.
  (** Semantics of [bor_tokCT] *)
  #[export] Program Instance bor_tokCT_ecsem {JUDG}
    : Ecsem bor_tokCT CON JUDG Σ :=
    ECSEM (λ _ _ α _ Φx _, bor_tok α (Φx ())) _.
  Next Obligation. move=>/= ???*???*?? eqv ???. f_equiv. apply eqv. Qed.
End bor_tokC.
(** Semantics of [bor_tokCT] registered *)
Notation bor_tokCS := (inCS bor_tokCT).

(** Reify [bor_tok] *)
#[export] Program Instance bor_tok_as_cif `{!Csem CON JUDG Σ}
  `{!bor_tokC CON, !borrowGS (cifOF CON) Σ, !bor_tokCS CON JUDG Σ} {α Px} :
  AsCif CON (λ _, bor_tok α Px) := AS_CIF (cif_bor_tok α Px) _.
Next Obligation. move=>/= *. by rewrite sem_cif_in. Qed.

(** ** Prophetic borrow *)

(** [pbor_tokCT]: Constructor for [pbor_tok] *)
Variant pbor_tokCT_id A TY := .
Definition pbor_tokCT A TY :=
  Cifcon (pbor_tokCT_id A TY) TY (λ _, Empty_set) (λ X, A *' clair TY X)%type
    (λ X, leibnizO (lft *' A *' clair TY X *' prvar X)) _.
(** [pbor_tokC]: [pbor_tokCT] registered *)
Notation pbor_tokC A TY := (inC (pbor_tokCT A TY)).
Section pbor_tokCT.
  Context `{!pbor_tokC A TY CON} {Σ}.
  Implicit Type X : TY.
  (** [cif_pbor_tok]: Formula *)
  Definition cif_pbor_tok {X} α a xπ ξ (Φx : A -pr> clair TY X -pr> cif CON Σ)
    : cif CON Σ :=
    cif_in (pbor_tokCT A TY) X nullary (λ '(a, xπ)', Φx a xπ) (α, a, xπ, ξ)'.
  (** [cif_pbor_tok] is non-expansive *)
  #[export] Instance cif_pbor_tok_ne {X α a xπ ξ} :
    NonExpansive (@cif_pbor_tok X α a xπ ξ).
  Proof. unfold cif_pbor_tok=> ??? eqv. f_equiv=> ?. apply (eqv _ _). Qed.
  #[export] Instance cif_pbor_tok_proper {X α a xπ ξ} :
    Proper ((≡) ==> (≡)) (@cif_pbor_tok X α a xπ ξ).
  Proof. apply ne_proper, _. Qed.
  (** [cif_pbor_tok] is productive *)
  #[export] Instance cif_pbor_tok_productive {X α a xπ ξ} :
    Productive (@cif_pbor_tok X α a xπ ξ).
  Proof.
    unfold cif_pbor_tok=> k ?? eqv. f_equiv. destruct k as [|k]=>//= ?.
    apply eqv.
  Qed.

  Context `{!borrowGS (cifOF CON) Σ, !prophGS TY Σ, !proph_agG A TY Σ,
    !proph_agC A TY CON}.
  (** Semantics of [pbor_tokCT] *)
  #[export] Program Instance pbor_tokCT_ecsem {JUDG}
    : Ecsem (pbor_tokCT A TY) CON JUDG Σ :=
    ECSEM (λ _ _ X _ Φx '(α, a, xπ, ξ)',
      pbor_tok α a xπ ξ (λ a xπ, Φx (a, xπ)')) _.
  Next Obligation.
    move=>/= ???*???*?*?? /leibniz_equiv_iff<-. by f_equiv=> ??.
  Qed.
End pbor_tokCT.
(** Semantics of [pbor_tokCT] registered *)
Notation pbor_tokCS A TY := (inCS (pbor_tokCT A TY)).

(** Reify [pbor_tok] *)
#[export] Program Instance pbor_tok_as_cif
  `{!pbor_tokC A TY CON, !borrowGS (cifOF CON) Σ, !prophGS TY Σ,
    !proph_agG A TY Σ, !proph_agC A TY CON, !Csem CON JUDG Σ,
    !pbor_tokCS A TY CON JUDG Σ}
  {X α a xπ ξ Φx} :
  AsCif CON (λ _, pbor_tok (X:=X) α a xπ ξ Φx) :=
  AS_CIF (cif_pbor_tok α a xπ ξ Φx) _.
Next Obligation. move=>/= *. by rewrite sem_cif_in. Qed.

(** ** Judgment for [iff] *)

(** [iffJT]: Judgment for [iff] *)
Variant iffJT_id FM := .
Definition iffJT (FM : ofe) : ofe := tagged (iffJT_id FM) (FM * FM).
(** [iffJ] : [iffJT] registered *)
Notation iffJ FM := (inJ (iffJT FM)).

Section iffJ.
  Context `{iff_j : !iffJ FM JUDG}.

  (** [jiff]: Judgment for [iff] *)
  Definition jiff (Px Qx : FM) : JUDG := iff_j (Tagged (Px, Qx)).
  #[export] Instance jiff_ne : NonExpansive2 jiff.
  Proof. solve_proper. Qed.

  Context `{!Dsem JUDG FM (iProp Σ)}.
  (** [iffJT_sem]: Semantics of [iffJT] *)
  Definition iffJT_sem δ (J : iffJT FM) : iProp Σ :=
    □ (⟦ J.(untag).1 ⟧(δ) ∗-∗ ⟦ J.(untag).2 ⟧(δ)).
  (** [iffJT_sem] is non-expansive *)
  #[export] Instance iffJT_sem_ne {δ} : NonExpansive (iffJT_sem δ).
  Proof. solve_proper. Qed.
  (** [Dsem] over [iffJT] *)
  #[export] Instance iffJT_dsem
    : Dsem JUDG (iffJT FM) (iProp Σ) := DSEM iffJT_sem _.
End iffJ.
(** [iffJS]: Judgment semantics for [iff] *)
Notation iffJS FML JUDG Σ := (inJS (iffJT (FML $oi Σ)) JUDG (iProp Σ)).

Section iffJ.
  Context `{!Dsem JUDG (FML $oi Σ) (iProp Σ), !Jsem JUDG (iProp Σ),
    !iffJ (FML $oi Σ) JUDG, !iffJS FML JUDG Σ}.

  (** Derivability of [jiff] is persistent *)
  #[export] Instance Deriv_jiff_persistent `{!Deriv (JUDG:=JUDG) ih δ} {Px Qx} :
    Persistent (δ (jiff Px Qx)).
  Proof. apply: Deriv_persistent=> ????. rewrite in_js. exact _. Qed.
End iffJ.

(** ** Relaxed invariant *)
(** [inv']: Proposition *)
Section inv'.
  Context `{!inv'GS (cifOF CON) Σ, !iffJ (cifO CON Σ) JUDG}.
  Implicit Type δ : JUDG -n> iProp Σ.
  (** [inv']: Relaxed invariant *)
  Definition inv' δ N Px : iProp Σ := ∃ Qx, δ (jiff Px Qx) ∗ inv_tok N Qx.
  (** [inv'] is non-expansive *)
  #[export] Instance inv'_ne {δ N} : NonExpansive (inv' δ N).
  Proof. solve_proper. Qed.
  #[export] Instance inv'_proper {δ N} :
    Proper ((≡) ==> (⊣⊢)) (inv' δ N).
  Proof. apply ne_proper, _. Qed.
End inv'.
(** Notation *)
Notation invd := (inv' der).

(** [invCT]: Constructor for [inv'] *)
Variant invCT_id := .
Definition invCT :=
  Cifcon invCT_id namespace (λ _, Empty_set) (λ _, unit) (λ _, unitO) _.
(** [invC]: [invCT] registered *)
Notation invC := (inC invCT).

Section invC.
  Context `{!invC CON} {Σ}.
  (** [cif_inv]: Formula for [inv'] *)
  Definition cif_inv N (Px : cif CON Σ) : cif CON Σ :=
    cif_in invCT N nullary (unary Px) ().
  (** [cif_inv] is non-expansive *)
  #[export] Instance cif_inv_ne {N} : NonExpansive (cif_inv N).
  Proof. move=> ????. apply cif_in_ne; solve_proper. Qed.
  #[export] Instance cif_inv_proper {N} : Proper ((≡) ==> (≡)) (cif_inv N).
  Proof. apply ne_proper, _. Qed.
  (** [cif_inv] is productive *)
  #[export] Instance cif_inv_productive {N} : Productive (cif_inv N).
  Proof.
    move=> ????. apply cif_in_preserv_productive=>//. by apply fun_proeq_later.
  Qed.

  Context `{!inv'GS (cifOF CON) Σ, !iffJ (cifO CON Σ) JUDG}.
  (** Semantics of [invCT] *)
  #[export] Program Instance invCT_ecsem : Ecsem invCT CON JUDG Σ :=
    ECSEM (λ _ δ N _ Φx _, inv' δ N (Φx ())) _.
  Next Obligation. move=> ??*???*?? eqv ?*. f_equiv. apply eqv. Qed.
End invC.
(** [invC] semantics registered *)
Notation invCS := (inCS invCT).

(** Reify [inv'] *)
#[export] Program Instance inv'_as_cif `{!Csem CON JUDG Σ, !invC CON}
  `{!inv'GS (cifOF CON) Σ, !iffJ (cifO CON Σ) JUDG, !invCS CON JUDG Σ} {N Px} :
  AsCif CON (λ δ, inv' δ N Px) := AS_CIF (cif_inv N Px) _.
Next Obligation. move=>/= *. by rewrite sem_cif_in. Qed.
