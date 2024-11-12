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
  Lemma ty_rec_ty_op {Yl} (Tl : plist (ty CON Σ) Yl) {κ d} :
    (∀ d, TyOpLt (ty_rec F) κ d →
      TCPlistForall (λ _ T, TyOpLt T κ d) Tl → TyOpAt (F (ty_rec F)) κ d) →
    TCPlistForall (λ _ T, TyOpLt T κ d) Tl → TyOpAt (ty_rec F) κ d.
  Proof.
    move=> Gen. rewrite ty_rec_unfold=> OnTl. apply Gen; [|done].
    rewrite ty_rec_unfold=> +. move: OnTl.
    elim: d; [move=> ??; lia|]=> d IH OnTl d' ?. apply Gen; last first.
    { move: OnTl. apply TCPlistForall_mono=> ??. apply TyOpLt_mono=>//=. lia. }
    move=> ??. rewrite ty_rec_unfold. apply IH; [|lia]. move: OnTl.
    apply TCPlistForall_mono=> ??. apply TyOpLt_mono=>//=. lia.
  Qed.
  Lemma ty_rec_ty_op' {κ} :
    (∀ d, TyOpLt (ty_rec F) κ d → TyOpAt (F (ty_rec F)) κ d) →
      TyOp (ty_rec F) κ.
  Proof. move=> ??. exact: (ty_rec_ty_op ᵖ[]). Qed.

  (** Resolution over [ty_rec] *)
  Lemma ty_rec_resol {Yl} (Tposl : plist (λ Y, ty CON Σ Y *' (Y → Prop)) Yl)
    {κ post d} :
    (∀ d, ResolLt (ty_rec F) κ post d →
      TCPlistForall (λ _ '(T, pos)', ResolLt T κ pos d) Tposl →
      ResolAt (F (ty_rec F)) κ post d) →
    TCPlistForall (λ _ '(T, pos)', ResolLt T κ pos d) Tposl →
      ResolAt (ty_rec F) κ post d.
  Proof.
    move=> Gen. rewrite ty_rec_unfold=> OnTl. apply Gen; [|done].
    rewrite ty_rec_unfold=> +. move: OnTl.
    elim: d; [move=> ??; lia|]=> d IH OnTl d' ?. apply Gen; last first.
    { move: OnTl. apply TCPlistForall_mono=> ??. apply ResolLt_mono=>//=. lia. }
    move=> ??. rewrite ty_rec_unfold. apply IH; [|lia]. move: OnTl.
    apply TCPlistForall_mono=> ??. apply ResolLt_mono=>//=. lia.
  Qed.
  Lemma ty_rec_resol' {κ post} :
    (∀ d T, ResolLt T κ post d → ResolAt (F T) κ post d) →
      Resol (ty_rec F) κ post.
  Proof. move=> ??. exact: (ty_rec_resol ᵖ[]). Qed.

  (** Real part over [ty_rec] *)
  Lemma ty_rec_real {Yl}
    (BTgel : plist (λ Y, sigT (λ B, ty CON Σ Y *' (Y → B))) Yl) {A κ get d} :
    (∀ d, RealLt (A:=A) (ty_rec F) κ get d →
      TCPlistForall (λ _ '(existT B (T, ge)'), RealLt (A:=B) T κ ge d) BTgel →
      RealAt (F (ty_rec F)) κ get d) →
    TCPlistForall (λ _ '(existT B (T, ge)'), RealLt T κ ge d) BTgel →
      RealAt (A:=A) (ty_rec F) κ get d.
  Proof.
    move=> Gen. rewrite ty_rec_unfold=> OnTl. apply Gen; [|done].
    rewrite ty_rec_unfold=> +. move: OnTl.
    elim: d; [move=> ??; lia|]=> d IH OnTl d' ?. apply Gen; last first.
    { move: OnTl. apply TCPlistForall_mono=> ?[??]. apply RealLt_mono=>//=.
      lia. }
    move=> ??. rewrite ty_rec_unfold. apply IH; [|lia]. move: OnTl.
    apply TCPlistForall_mono=> ?[??]. apply RealLt_mono=>//=. lia.
  Qed.
  Lemma ty_rec_real' {A κ get} :
    (∀ d, RealLt (A:=A) (ty_rec F) κ get d → RealAt (F (ty_rec F)) κ get d) →
      Real (ty_rec F) κ get.
  Proof. move=> ??. exact: (ty_rec_real ᵖ[]). Qed.
End ty_rec.
