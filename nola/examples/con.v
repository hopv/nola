(** * Formula and judgment constructors *)

From nola.util Require Import tagged.
From nola.iris Require Export cif inv pborrow.
Import ProdNotation FunPRNotation DsemNotation.

Implicit Type (Σ : gFunctors) (N : namespace) (TY : synty) (α : lft) (FM : ofe)
  (A : Type).

(** ** Invariant *)
(** [invCC]: Constructor *)
Variant invCC_id := .
Definition invCC :=
  Cifcon invCC_id namespace (λ _, Empty_set) (λ _, unit) (λ _, unitO) _.
(** [InvCon]: [invCC] registered *)
Notation InvCon := (Ecifcon invCC).
Section cif_inv.
  Context `{!InvCon CON} {Σ}.
  (** [cif_inv]: Formula *)
  Definition cif_inv N (Px : cif CON Σ) : cif CON Σ :=
    cif_ecustom invCC N nullary (unary Px) ().
  (** [cif_inv] is non-expansive *)
  #[export] Instance cif_inv_ne {N} : NonExpansive (cif_inv N).
  Proof. move=> ????. apply cif_ecustom_ne; solve_proper. Qed.
  #[export] Instance cif_inv_proper {N} : Proper ((≡) ==> (≡)) (cif_inv N).
  Proof. apply ne_proper, _. Qed.
  (** [cif_inv] is productive *)
  #[export] Instance cif_inv_productive {N} : Productive (cif_inv N).
  Proof.
    move=> ????. apply cif_ecustom_preserv_productive=>//.
    by apply fun_proeq_later.
  Qed.
  Context `{!inv'GS (cifOF CON) Σ}.
  (** Semantics of [invCC] *)
  #[export] Program Instance inv_sem_ecifcon {JUDG}
    : SemEcifcon invCC CON JUDG Σ :=
    SEM_ECIFCON (λ _ _ N _ Φx _, inv_tok N (Φx ())) _.
  Next Obligation. move=>/= ???*???*?? eqv ???. f_equiv. apply eqv. Qed.
End cif_inv.
(** [invCC] semantics registered *)
Notation InvSem := (EsemEcifcon invCC).

(** Reify [inv_tok] *)
#[export] Program Instance inv_tok_as_cif `{!SemCifcon CON JUDG Σ, !InvCon CON}
  `{!inv'GS (cifOF CON) Σ, !InvSem CON JUDG Σ} {N Px} :
  AsCif CON (λ _, inv_tok N Px) := AS_CIF (cif_inv N Px) _.
Next Obligation. move=>/= *. by rewrite sem_ecustom. Qed.

(** ** Borrow *)
(** [borCC]: Constructor *)
Variant borCC_id := .
Definition borCC :=
  Cifcon borCC_id lft (λ _, Empty_set) (λ _, unit) (λ _, unitO) _.
(** [BorCon]: [borCC] registered *)
Notation BorCon := (Ecifcon borCC).
Section cif_bor.
  Context `{!BorCon CON} {Σ}.
  (** [cif_bor]: Formula *)
  Definition cif_bor α (Px : cif CON Σ) : cif CON Σ :=
    cif_ecustom borCC α nullary (unary Px) ().
  (** [cif_bor] is non-expansive *)
  #[export] Instance cif_bor_ne {α} : NonExpansive (cif_bor α).
  Proof. move=> ????. apply cif_ecustom_ne; solve_proper. Qed.
  #[export] Instance cif_bor_proper {α} : Proper ((≡) ==> (≡)) (cif_bor α).
  Proof. apply ne_proper, _. Qed.
  (** [cif_bor] is productive *)
  #[export] Instance cif_bor_productive {α} : Productive (cif_bor α).
  Proof.
    move=> ????. apply cif_ecustom_preserv_productive=>//.
    by apply fun_proeq_later.
  Qed.
  Context `{!borrowGS (cifOF CON) Σ}.
  (** Semantics of [borCC] *)
  #[export] Program Instance bor_sem_ecifcon {JUDG}
    : SemEcifcon borCC CON JUDG Σ :=
    SEM_ECIFCON (λ _ _ α _ Φx _, bor_tok α (Φx ())) _.
  Next Obligation. move=>/= ???*???*?? eqv ???. f_equiv. apply eqv. Qed.
End cif_bor.
(** [borCC] semantics registered *)
Notation BorSem := (EsemEcifcon borCC).

(** Reify [bor_tok] *)
#[export] Program Instance bor_tok_as_cif `{!SemCifcon CON JUDG Σ, !BorCon CON}
  `{!borrowGS (cifOF CON) Σ, !BorSem CON JUDG Σ} {α Px} :
  AsCif CON (λ _, bor_tok α Px) := AS_CIF (cif_bor α Px) _.
Next Obligation. move=>/= *. by rewrite sem_ecustom. Qed.

(** ** Prophetic borrow *)
(** [pborCC]: Constructor *)
Variant pborCC_id A TY := .
Definition pborCC A TY :=
  Cifcon (pborCC_id A TY) TY (λ _, Empty_set) (λ X, A *' clair TY X)%type
    (λ X, leibnizO (lft *' A *' clair TY X *' prvar X)) _.
(** [PborCon]: [pborCC] registered *)
Notation PborCon A TY := (Ecifcon (pborCC A TY)).
Section cif_pbor.
  Context `{!PborCon A TY CON} {Σ}.
  Implicit Type X : TY.
  (** [cif_pbor]: Formula *)
  Definition cif_pbor {X} α a xπ ξ (Φx : A -pr> clair TY X -pr> cif CON Σ)
    : cif CON Σ :=
    cif_ecustom (pborCC A TY) X nullary (λ '(a, xπ)', Φx a xπ) (α, a, xπ, ξ)'.
  (** [cif_pbor] is non-expansive *)
  #[export] Instance cif_pbor_ne {X α a xπ ξ} :
    NonExpansive (@cif_pbor X α a xπ ξ).
  Proof. unfold cif_pbor=> ??? eqv. f_equiv=> ?. apply (eqv _ _). Qed.
  #[export] Instance cif_pbor_proper {X α a xπ ξ} :
    Proper ((≡) ==> (≡)) (@cif_pbor X α a xπ ξ).
  Proof. apply ne_proper, _. Qed.
  (** [cif_pbor] is productive *)
  #[export] Instance cif_pbor_productive {X α a xπ ξ} :
    Productive (@cif_pbor X α a xπ ξ).
  Proof.
    unfold cif_pbor=> k ?? eqv. f_equiv. destruct k as [|k]=>//= ?. apply eqv.
  Qed.
  Context `{!borrowGS (cifOF CON) Σ, !prophGS TY Σ, !proph_agG A TY Σ,
    !PborrowCon A TY CON}.
  (** Semantics of [pborCC] *)
  #[export] Program Instance pbor_sem_ecifcon {JUDG}
    : SemEcifcon (pborCC A TY) CON JUDG Σ :=
    SEM_ECIFCON (λ _ _ X _ Φx '(α, a, xπ, ξ)',
      pbor_tok α a xπ ξ (λ a xπ, Φx (a, xπ)')) _.
  Next Obligation.
    move=>/= ???*???*?*?? /leibniz_equiv_iff<-. by f_equiv=> ??.
  Qed.
End cif_pbor.
(** [pborCC] semantics registered *)
Notation PborSem A TY := (EsemEcifcon (pborCC A TY)).

(** Reify [pbor_tok] *)
#[export] Program Instance pbor_tok_as_cif
  `{!PborCon A TY CON, !borrowGS (cifOF CON) Σ, !prophGS TY Σ,
    !proph_agG A TY Σ, !PborrowCon A TY CON, !SemCifcon CON JUDG Σ,
    !PborSem A TY CON JUDG Σ}
  {X α a xπ ξ Φx} :
  AsCif CON (λ _, pbor_tok (X:=X) α a xπ ξ Φx) :=
  AS_CIF (cif_pbor α a xπ ξ Φx) _.
Next Obligation. move=>/= *. by rewrite sem_ecustom. Qed.

(** ** Judgment *)
Variant iff_judg_id FM := .
Definition iff_judgty (FM : ofe) : ofe := tagged (iff_judg_id FM) (FM * FM).
Notation IffJudg FM := (Ejudg (iff_judgty FM)).
Section iff_judg.
  Context `{iff_judg : !IffJudg FM JUDG}.
  Definition jiff (Px Qx : FM) : JUDG := iff_judg (Tagged (Px, Qx)).
  #[export] Instance jiff_ne : NonExpansive2 jiff.
  Proof. solve_proper. Qed.

  Context `{!Dsem JUDG FM (iProp Σ)}.
  (** ** [iff_judg_sem]: Semantics of [iff_judgty] *)
  Definition iff_judg_sem δ (PQx : iff_judgty FM) : iProp Σ :=
    □ (⟦ PQx.(untag).1 ⟧(δ) ∗-∗ ⟦ PQx.(untag).2 ⟧(δ)).
  (** [iff_judg_sem] is non-expansive *)
  #[export] Instance iff_judg_sem_ne {δ} : NonExpansive (iff_judg_sem δ).
  Proof. solve_proper. Qed.
  (** [Dsem] over [iff_judgty] *)
  #[export] Instance iff_judg_dsem
    : Dsem JUDG (iff_judgty FM) (iProp Σ) := DSEM iff_judg_sem _.
End iff_judg.
(** ** [IffJsem]: Judgment semantics for [iff] *)
Notation IffJsem FM JUDG Σ := (Ejsem (iff_judgty FM) JUDG (iProp Σ)).

Section iff_judg.
  Context `{!Jsem JUDG (iProp Σ), !Dsem JUDG FM (iProp Σ), !IffJudg FM JUDG,
    !IffJsem FM JUDG Σ}.

  (** Derivability of [jiff] is persistent *)
  #[export] Instance Deriv_jiff_persistent `{!Deriv (JUDG:=JUDG) ih δ} {Px Qx} :
    Persistent (δ (jiff Px Qx)).
  Proof. apply: Deriv_persistent=> ????. rewrite sem_ejudg. exact _. Qed.
End iff_judg.

(** ** Relaxed invariant *)
(** [inv']: Proposition *)
Section inv'.
  Context `{!inv'GS (cifOF CON) Σ, !IffJudg (cifO CON Σ) JUDG}.
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
(** [inv'CC]: Constructor *)
Variant inv'CC_id := .
Definition inv'CC :=
  Cifcon inv'CC_id namespace (λ _, Empty_set) (λ _, unit) (λ _, unitO) _.
(** [Inv'Con]: [inv'CC] registered *)
Notation Inv'Con := (Ecifcon inv'CC).
Section cif_inv'.
  Context `{!Inv'Con CON} {Σ}.
  (** [cif_inv']: Formula *)
  Definition cif_inv' N (Px : cif CON Σ) : cif CON Σ :=
    cif_ecustom inv'CC N nullary (unary Px) ().
  (** [cif_inv'] is non-expansive *)
  #[export] Instance cif_inv'_ne {N} : NonExpansive (cif_inv' N).
  Proof. move=> ????. apply cif_ecustom_ne; solve_proper. Qed.
  #[export] Instance cif_inv'_proper {N} : Proper ((≡) ==> (≡)) (cif_inv' N).
  Proof. apply ne_proper, _. Qed.
  (** [cif_inv'] is productive *)
  #[export] Instance cif_inv'_productive {N} : Productive (cif_inv' N).
  Proof.
    move=> ????. apply cif_ecustom_preserv_productive=>//.
    by apply fun_proeq_later.
  Qed.

  Context `{!inv'GS (cifOF CON) Σ, !IffJudg (cifO CON Σ) JUDG}.
  (** Semantics of [invCC] *)
  #[export] Program Instance inv'_sem_ecifcon
    : SemEcifcon inv'CC CON JUDG Σ :=
    SEM_ECIFCON (λ _ δ N _ Φx _, inv' δ N (Φx ())) _.
  Next Obligation. move=> ??*???*?? eqv ?*. f_equiv. apply eqv. Qed.
End cif_inv'.
(** [inv'CC] semantics registered *)
Notation Inv'Sem := (EsemEcifcon inv'CC).

(** Reify [inv'] *)
#[export] Program Instance inv'_as_cif `{!SemCifcon CON JUDG Σ, !Inv'Con CON}
  `{!inv'GS (cifOF CON) Σ, !IffJudg (cifO CON Σ) JUDG, !Inv'Sem CON JUDG Σ}
  {N Px} :
  AsCif CON (λ δ, inv' δ N Px) := AS_CIF (cif_inv' N Px) _.
Next Obligation. move=>/= *. by rewrite sem_ecustom. Qed.
