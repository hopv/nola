(** * Recursive type *)

From nola.examples.rust_halt Require Export type.

(** [ty_rec]: Recursive type *)
Definition ty_rec {CON Σ X} (F : ty CON Σ X → ty CON Σ X) `{!Productive F}
  : ty CON Σ X := profix F.

Section ty_rec.
  Context {CON Σ X} {F : ty CON Σ X → ty CON Σ X} `{!Productive F}.

  (** Unfold [ty_rec] *)
  Lemma ty_rec_unfold : @ty_rec CON Σ X F _ ≡ F (ty_rec F).
  Proof. exact profix_unfold. Qed.

  (** Uniqueness of [ty_rec] *)
  Lemma ty_rec_unique {T} : T ≡ F T → T ≡ ty_rec F.
  Proof. exact profix_unique. Qed.

  (** Approximate [ty_rec] by an iteration *)
  Lemma ty_rec_iter {k} : ty_rec F ≡[k]≡ F (Nat.iter k F inhabitant).
  Proof. exact profix_iter. Qed.

  (** Equivalence between [ty_rec]s *)
  Lemma ty_rec_equiv {G : ty CON Σ X → ty CON Σ X} `{!Productive G} :
    (∀ T U, T ≡ U → F T ≡ G U) → ty_rec F ≡ ty_rec G.
  Proof. exact profix_proper. Qed.

  (** [ty_rec] is size-preserving *)
  Lemma ty_rec_preserv {G : ty CON Σ X → ty CON Σ X} `{!Productive G} {k} :
    F ≡[k]@{funPR _}≡ G → ty_rec F ≡[k]≡ ty_rec G.
  Proof. exact profix_preserv. Qed.
  (** [ty_rec] preserves size preservation and productivity *)
  #[export] Instance ty_rec_map_preserv {Y}
    {H : ty CON Σ Y → ty CON Σ X → ty CON Σ X} `{!∀ T, Productive (H T)}
    `{!∀ U, Preserv (λ T, H T U)} :
    Preserv (λ T, ty_rec (H T)).
  Proof. exact profix_map_preserv. Qed.
  #[export] Instance ty_rec_map_productive {Y}
    {H : ty CON Σ Y → ty CON Σ X → ty CON Σ X} `{!∀ T, Productive (H T)}
    `{!∀ U, Productive (λ T, H T U)} :
    Productive (λ T, ty_rec (H T)).
  Proof. exact profix_map_productive. Qed.

  (** [Send] on [ty_rec], coinductively *)
  #[export] Instance ty_rec_send `{Send0 : !∀ T, Send T → Send (F T)} :
    Send (ty_rec F).
  Proof.
    move=> ??. apply equiv_proeq=> k. etrans; [by apply ty_rec_iter|].
    etrans; [|symmetry; by apply ty_rec_iter]. apply equiv_proeq, Send0.
    elim: k; [by move|exact _].
  Qed.
  (** [Sync] on [ty_rec], coinductively *)
  #[export] Instance ty_rec_sync `{Sync0 : !∀ T, Sync T → Sync (F T)} :
    Sync (ty_rec F).
  Proof.
    move=> ??. apply equiv_proeq=> k. etrans; [by apply ty_rec_iter|].
    etrans; [|symmetry; by apply ty_rec_iter]. apply equiv_proeq, Sync0.
    elim: k; [by move|exact _].
  Qed.

  Context `{!Csem CON JUDG Σ, !Jsem JUDG (iProp Σ), !rust_haltGS CON Σ,
    rust_haltJ CON JUDG Σ}.
  Implicit Type δ : JUDG -n> iProp Σ.

  (** Unfold and fold [ty_rec] in subtyping *)
  Lemma ty_rec_unfold_sub {δ} :
    ⊢ subty (X:=X) δ (ty_rec (CON:=CON) F) (F (ty_rec F)) id.
  Proof.
    erewrite subty_proper; [exact subty_refl|exact ty_rec_unfold|done..].
  Qed.
  Lemma ty_rec_fold_sub {δ} :
    ⊢ subty (X:=X) δ (F (ty_rec F)) (ty_rec (CON:=CON) F) id.
  Proof.
    erewrite subty_proper; [exact subty_refl|done|exact ty_rec_unfold|done].
  Qed.

  (** [Ty] on [ty_rec] *)
  #[export] Instance ty_rec_ty `{!∀ T, Ty (F T) sz} : Ty (ty_rec F) sz.
  Proof. by rewrite ty_rec_unfold. Qed.

  (** [Copy] on [ty_rec] *)
  #[export] Instance ty_rec_copy `{!∀ T, Copy (F T)} : Copy (ty_rec F).
  Proof. by rewrite ty_rec_unfold. Qed.

  (** [TyOp] on [ty_rec] *)
  Lemma ty_rec_ty_op_lt {Yl} (Ul : plist (ty CON Σ) Yl)
    `{TyOp0: !∀ d T, TyOpLt T α d → TCPlistForall (λ _ U, TyOpLt U α d) Ul →
        TyOpAt (F T) α d} {d} :
    TCPlistForall (λ _ U, TyOpLt U α d) Ul → TyOpAt (ty_rec F) α d.
  Proof.
    rewrite ty_rec_unfold=> OpUl. apply TyOp0; [|done]. rewrite ty_rec_unfold.
    move: OpUl. elim: d; [move=> ??; lia|]=> d IH OpUl d' ?.
    apply TyOp0; last first.
    { move: OpUl. apply TCPlistForall_mono=> ??. apply: TyOpLt_mono=>//=. lia. }
    have le : d' ≤ d by lia. apply: TyOpLt_mono=>//.
    rewrite ty_rec_unfold. apply IH. move: OpUl. apply TCPlistForall_mono=> ??.
    apply: TyOpLt_mono=>//=. lia.
  Qed.
  Lemma ty_rec_ty_op `{!∀ d T, TyOpLt T α d → TyOpAt (F T) α d} :
    TyOp (ty_rec F) α.
  Proof. move=> ?. by apply (ty_rec_ty_op_lt ᵖ[]). Qed.
End ty_rec.
