(** * Formula and judgment constructors *)

From nola.util Require Import tagged.
From nola.iris Require Export cif inv pborrow.
Import ProdNotation FunPRNotation DsemNotation.

Implicit Type (Σ : gFunctors) (N : namespace) (TY : synty) (α : lft) (FM : ofe).

(** ** Invariant *)
(** [invCC]: Constructor *)
Variant invCC_id := .
Definition invCC :=
  Cifcon invCC_id namespace (λ _, Empty_set) (λ _, unit) (λ _, unitO) _.
(** [InvCon]: [invCC] registered *)
Notation InvCon CON := (Ecifcon invCC CON).
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
    : SemEcifcon JUDG invCC CON Σ :=
    SEM_ECIFCON (λ _ _ N _ Φx _, inv_tok N (Φx ())) _.
  Next Obligation. move=>/= ???*???*?? eqv ???. f_equiv. apply eqv. Qed.
End cif_inv.
(** [invCC] semantics registered *)
Notation InvSem JUDG CON Σ := (EsemEcifcon JUDG invCC CON Σ).

(** Reify [inv_tok] *)
#[export] Program Instance inv_tok_as_cif `{!SemCifcon JUDG CON Σ, !InvCon CON}
  `{!inv'GS (cifOF CON) Σ, !InvSem JUDG CON Σ} {N Px} :
  AsCif CON (λ _, inv_tok N Px) := AS_CIF (cif_inv N Px) _.
Next Obligation. move=>/= *. by rewrite sem_ecustom. Qed.

(** ** Borrow *)
(** [borCC]: Constructor *)
Variant borCC_id := .
Definition borCC :=
  Cifcon borCC_id lft (λ _, Empty_set) (λ _, unit) (λ _, unitO) _.
(** [BorCon]: [borCC] registered *)
Notation BorCon CON := (Ecifcon borCC CON).
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
  Context `{!pborrowGS TY (cifOF CON) Σ}.
  (** Semantics of [borCC] *)
  #[export] Program Instance bor_sem_ecifcon {JUDG}
    : SemEcifcon JUDG borCC CON Σ :=
    SEM_ECIFCON (λ _ _ α _ Φx _, nbor_tok α (Φx ())) _.
  Next Obligation. move=>/= ???*???*?? eqv ???. f_equiv. apply eqv. Qed.
End cif_bor.
(** [borCC] semantics registered *)
Notation BorSem JUDG CON Σ := (EsemEcifcon JUDG borCC CON Σ).

(** Reify [nbor_tok] *)
#[export] Program Instance nbor_tok_as_cif `{!SemCifcon JUDG CON Σ, !BorCon CON}
  `{!pborrowGS TY (cifOF CON) Σ, !BorSem JUDG CON Σ} {α Px} :
  AsCif CON (λ _, nbor_tok α Px) := AS_CIF (cif_bor α Px) _.
Next Obligation. move=>/= *. by rewrite sem_ecustom. Qed.

(** ** Prophetic borrow *)
(** [pborCC]: Constructor *)
Variant pborCC_id TY := .
Definition pborCC TY :=
  Cifcon (pborCC_id TY) (lft *' TY) (λ _, Empty_set) (λ '(_, X)', X)
    (λ '(_, X)', leibnizO (X *' prvar X)) _.
(** [PborCon]: [pborCC] registered *)
Notation PborCon TY CON := (Ecifcon (pborCC TY) CON).
Section cif_pbor.
  Context `{!PborCon TY CON} {Σ}.
  Implicit Type X : TY.
  (** [cif_pbor]: Formula *)
  Definition cif_pbor {X} α (x : X) (ξ : prvar X) (Φx : X -pr> cif CON Σ)
    : cif CON Σ :=
    cif_ecustom (pborCC TY) (α, X)' nullary Φx (x, ξ)'.
  (** [cif_pbor] is non-expansive *)
  #[export] Instance cif_pbor_ne {X α x ξ} : NonExpansive (@cif_pbor X α x ξ).
  Proof. solve_proper. Qed.
  #[export] Instance cif_pbor_proper {X α x ξ} :
    Proper ((≡) ==> (≡)) (@cif_pbor X α x ξ).
  Proof. apply ne_proper, _. Qed.
  (** [cif_pbor] is productive *)
  #[export] Instance cif_pbor_productive {X α x ξ} :
    Productive (@cif_pbor X α x ξ).
  Proof. solve_proper. Qed.
  Context `{!pborrowGS TY (cifOF CON) Σ}.
  (** Semantics of [pborCC] *)
  #[export] Program Instance pbor_sem_ecifcon {JUDG}
    : SemEcifcon JUDG (pborCC TY) CON Σ :=
    SEM_ECIFCON (λ _ _ '(α, X)' _ Φx '(x, ξ)', pbor_tok α x ξ Φx) _.
  Next Obligation. move=>/= ???*???*?*?? /leibniz_equiv_iff. solve_proper. Qed.
End cif_pbor.
(** [pborCC] semantics registered *)
Notation PborSem TY JUDG CON Σ := (EsemEcifcon JUDG (pborCC TY) CON Σ).

(** Reify [pbor_tok] *)
#[export] Program Instance pbor_tok_as_cif `{!SemCifcon JUDG CON Σ}
  `{!PborCon TY CON, !pborrowGS TY (cifOF CON) Σ, !PborSem TY JUDG CON Σ}
  {X α x ξ Φx} :
  AsCif CON (λ _, pbor_tok (X:=X) α x ξ Φx) := AS_CIF (cif_pbor α x ξ Φx) _.
Next Obligation. move=>/= *. by rewrite sem_ecustom. Qed.

(** ** Judgment *)
Variant iff_judg_id FM := .
Definition iff_judgty (FM : ofe) : ofe := tagged (iff_judg_id FM) (FM * FM).
Notation IffJudg FM JUDG := (Ejudg (iff_judgty FM) JUDG).
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
Notation IffJsem FM Σ JUDG := (Ejsem (iff_judgty FM) JUDG (iProp Σ)).

Section iff_judg.
  Context `{!Jsem JUDG (iProp Σ), !Dsem JUDG FM (iProp Σ), !IffJudg FM JUDG,
    !IffJsem FM Σ JUDG}.

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
Notation Inv'Con CON := (Ecifcon inv'CC CON).
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
    : SemEcifcon JUDG inv'CC CON Σ :=
    SEM_ECIFCON (λ _ δ N _ Φx _, inv' δ N (Φx ())) _.
  Next Obligation. move=> ??*???*?? eqv ?*. f_equiv. apply eqv. Qed.
End cif_inv'.
(** [inv'CC] semantics registered *)
Notation Inv'Sem JUDG CON Σ := (EsemEcifcon JUDG inv'CC CON Σ).

(** Reify [inv'] *)
#[export] Program Instance inv'_as_cif `{!SemCifcon JUDG CON Σ, !Inv'Con CON}
  `{!inv'GS (cifOF CON) Σ, !IffJudg (cifO CON Σ) JUDG, !Inv'Sem JUDG CON Σ}
  {N Px} :
  AsCif CON (λ δ, inv' δ N Px) := AS_CIF (cif_inv' N Px) _.
Next Obligation. move=>/= *. by rewrite sem_ecustom. Qed.
