(** * Recursive type *)

From nola.examples.rust_halt Require Export type.

Implicit Type PR : prost.

Section ty_rec.
  Context {CON Σ X} {F : ty CON Σ X → ty CON Σ X} `{!Productive F}.

  (** [ty_rec]: Recursive type *)
  Definition ty_rec {X} (F : ty CON Σ X → ty CON Σ X) `{!Productive F}
    : ty CON Σ X := profix F.

  (** Unfold [ty_rec] *)
  Lemma ty_rec_unfold : @ty_rec X F _ ≡ F (ty_rec F).
  Proof. exact profix_unfold. Qed.

  (** Uniqueness of [ty_rec] *)
  Lemma ty_rec_unique {T} : T ≡ F T → T ≡ ty_rec F.
  Proof. exact profix_unique. Qed.

  (** Approximate [ty_rec] by an iteration *)
  Lemma ty_rec_iter {k} : ty_rec F ≡[k]≡ F (Nat.iter k F inhabitant).
  Proof. exact profix_iter. Qed.

  (** [ty_rec] is size-preserving *)
  Lemma ty_rec_preserv {G : ty CON Σ X → ty CON Σ X} `{!Productive G} {k} :
    (∀ T, F T ≡[k]≡ G T) → ty_rec F ≡[k]≡ ty_rec G.
  Proof. exact profix_preserv. Qed.
  Lemma ty_rec_proper {G : ty CON Σ X → ty CON Σ X} `{!Productive G} :
    (∀ T, F T ≡ G T) → ty_rec F ≡ ty_rec G.
  Proof. exact profix_proper. Qed.
  (** [ty_rec] preserves size preservation and productivity *)
  #[export] Instance ty_rec_map_preserv
    `(!∀ T : PR, Productive (H T), !∀ U : ty CON Σ X, Preserv (λ T, H T U)) :
    Preserv (λ T, ty_rec (H T)).
  Proof. exact profix_map_preserv. Qed.
  #[export] Instance ty_rec_map_productive
    `(!∀ T : PR, Productive (H T), !∀ U : ty CON Σ X, Productive (λ T, H T U)) :
    Productive (λ T, ty_rec (H T)).
  Proof. exact profix_map_productive. Qed.

  (** [Send] on [ty_rec], coinductively *)
  #[export] Instance ty_rec_send `{Send0 : !∀ T, Send T → Send (F T)} :
    Send (ty_rec F).
  Proof.
    move=> >. apply equiv_proeqv=> k. etrans; [by apply ty_rec_iter|].
    etrans; [|symmetry; by apply ty_rec_iter]. apply equiv_proeqv, Send0.
    elim: k; [by move|exact _].
  Qed.
  (** [Sync] on [ty_rec], coinductively *)
  #[export] Instance ty_rec_sync `{Sync0 : !∀ T, Sync T → Sync (F T)} :
    Sync (ty_rec F).
  Proof.
    move=> >. apply equiv_proeqv=> k. etrans; [by apply ty_rec_iter|].
    etrans; [|symmetry; by apply ty_rec_iter]. apply equiv_proeqv.
    apply: (Sync0). elim: k; [by move|exact _].
  Qed.

  Context `{!Csem CON JUDG Σ, !Jsem JUDG (iProp Σ), !rust_haltGS CON Σ,
    !rust_haltJ CON JUDG Σ}.
  Implicit Type δ : JUDG -n> iProp Σ.

  (** Unfold and fold [ty_rec] in subtyping *)
  Lemma ty_rec_unfold_sub {δ} : ⊢ subty (X:=X) δ (ty_rec F) (F (ty_rec F)) id.
  Proof.
    erewrite subty_proper; [exact subty_refl|exact ty_rec_unfold|done..].
  Qed.
  Lemma ty_rec_fold_sub {δ} : ⊢ subty (X:=X) δ (F (ty_rec F)) (ty_rec F) id.
  Proof.
    erewrite subty_proper; [exact subty_refl|done|exact ty_rec_unfold|done].
  Qed.

  (** [Ty] on [ty_rec] *)
  #[export] Instance ty_rec_ty `{!∀ T, Ty (F T)} : Ty (ty_rec F).
  Proof. by rewrite ty_rec_unfold. Qed.

  (** [Copy] on [ty_rec] *)
  #[export] Instance ty_rec_copy `{!∀ T, Copy (F T)} : Copy (ty_rec F).
  Proof. by rewrite ty_rec_unfold. Qed.

  (** [TyOp] on [ty_rec] *)
  Lemma ty_rec_ty_op_lt {Yl} (Ul : plist (ty CON Σ) Yl)
    `(TyOp0: !∀ d T, TyOpLt T κ d → TCPlistForall (λ _ U, TyOpLt U κ d) Ul →
        TyOpAt (F T) κ d) {d} :
    TCPlistForall (λ _ U, TyOpLt U κ d) Ul → TyOpAt (ty_rec F) κ d.
  Proof.
    rewrite ty_rec_unfold=> OpUl. apply TyOp0; [|done]. rewrite ty_rec_unfold.
    move: OpUl. elim: d; [move=> ??; lia|]=> d IH OpUl d' ?.
    apply TyOp0; last first.
    { move: OpUl. apply TCPlistForall_mono=> ??. apply: TyOpLt_mono=>//=. lia. }
    have le : d' ≤ d by lia. apply: TyOpLt_mono=>//.
    rewrite ty_rec_unfold. apply IH. move: OpUl. apply TCPlistForall_mono=> ??.
    apply: TyOpLt_mono=>//=. lia.
  Qed.
  Lemma ty_rec_ty_op `(!∀ d T, TyOpLt T κ d → TyOpAt (F T) κ d) :
    TyOp (ty_rec F) κ.
  Proof. move=> ?. by apply (ty_rec_ty_op_lt ᵖ[] _). Qed.

  (** Resolution over [ty_rec] *)
  Lemma ty_rec_resol_lt {Yl} (Uposl : plist (λ Y, ty CON Σ Y *' (Y → Prop)) Yl)
    `(Resol0: !∀ d T, ResolLt T κ post d →
        TCPlistForall (λ _ '(U, pos)', ResolLt U κ pos d) Uposl →
        ResolAt (F T) κ post d) {d} :
    TCPlistForall (λ _ '(U, pos)', ResolLt U κ pos d) Uposl →
      ResolAt (ty_rec F) κ post d.
  Proof.
    rewrite ty_rec_unfold=> ResolUl. apply Resol0; [|done].
    rewrite ty_rec_unfold. move: ResolUl. elim: d; [move=> ??; lia|].
    move=> d IH ResolUl d' ?. apply Resol0; last first.
    { move: ResolUl. apply TCPlistForall_mono=> ??. apply: ResolLt_mono=>//=.
      lia. }
    have le : d' ≤ d by lia. apply: ResolLt_mono=>//. rewrite ty_rec_unfold.
    apply IH. move: ResolUl. apply TCPlistForall_mono=> ??.
    apply: ResolLt_mono=>//=. lia.
  Qed.
  Lemma ty_rec_resol `(!∀ d T, ResolLt T κ post d → ResolAt (F T) κ post d) :
    Resol (ty_rec F) κ post.
  Proof. move=> ?. by apply (ty_rec_resol_lt ᵖ[] _). Qed.
End ty_rec.
