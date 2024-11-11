(** * Type model *)

From nola.examples.rust_halt Require Export base.

Implicit Type (CON : cifcon) (Σ : gFunctors) (X : xty).

(** ** Type model *)

Canonical natPR : prost := discretePR nat.

(** Ownership formula *)
Definition ownty CON Σ X : prost :=
  thread_id -pr> nat -pr> clair X -pr> list val -pr> cif CON Σ.
(** Sharing formula *)
Definition shrty CON Σ X : prost :=
  thread_id -pr> nat -pr> loc -pr> lft -pr> clair X -pr> cif CON Σ.
(** Type model *)
Definition ty' CON Σ X : prost := (ownty CON Σ X * shrty CON Σ X)%type.
Definition ty CON Σ X : prost := (natPR * ty' CON Σ X)%type.

(** Accessing members *)
Notation ty_size T := T.1 (only parsing).
Notation ty_own T := T.2.1 (only parsing).
Notation ty_shr T := T.2.2 (only parsing).

(** Simple type, with the sharing formula defined from the ownership formula *)
Definition sty CON Σ X : prost := (natPR * ownty CON Σ X)%type.
Notation sty_size T := T.1 (only parsing).
Notation sty_own T := T.2 (only parsing).
Section ty_sty.
  Context `{!rust_haltGS CON Σ, !rust_haltC CON}.
  Definition ty'_sty_def {X} (T : sty CON Σ X) : ty' CON Σ X :=
    (sty_own T, λ t d l α xπ, ∃ vl, ▷ l ↦∗ˢ[α] vl ∗ sty_own T t d xπ vl)%cif.
  Lemma ty'_sty_aux : seal (@ty'_sty_def). Proof. by eexists. Qed.
  Definition ty'_sty {X} := ty'_sty_aux.(unseal) X.
  Lemma ty'_sty_unseal : @ty'_sty = @ty'_sty_def. Proof. exact: seal_eq. Qed.
  Definition ty_sty {X} (T : sty CON Σ X) : ty CON Σ X :=
    (sty_size T, ty'_sty T).
  Lemma ty_sty_unseal : @ty_sty = λ _ T, (sty_size T, ty'_sty_def T).
  Proof. by rewrite /ty_sty ty'_sty_unseal. Qed.
End ty_sty.

(** Plain type, with the ownership formula ignoring the thread id, the depth,
  and the prophecy assignment *)
Definition ownpty CON Σ X : prost := X -d> list val -d> cif CON Σ.
Definition pty CON Σ X := (natPR * ownpty CON Σ X)%type.
Notation pty_size T := T.1 (only parsing).
Notation pty_own T := T.2 (only parsing).
Definition sty_pty {CON Σ X} (T : pty CON Σ X) : sty CON Σ X :=
  pair (pty_size T)
    (λ _ _ xπ vl, ∃ x, ⌜∀ π, xπ π = x⌝ ∧ pty_own T x vl)%cif.
Section ty_pty.
  Context `{!rust_haltGS CON Σ, !rust_haltC CON}.
  Definition ty_pty {X} (T : pty CON Σ X) : ty CON Σ X := ty_sty (sty_pty T).
  Lemma ty_pty_unseal : @ty_pty = λ _ T, (pty_size T, ty'_sty_def (sty_pty T)).
  Proof. by rewrite /ty_pty ty_sty_unseal. Qed.
End ty_pty.

Section ty.
  Context `{!rust_haltGS CON Σ, !rust_haltC CON}.

  (** [ty_sty] is size-preserving *)
  #[export] Instance ty_sty_preserv {X} : Preserv (ty_sty (X:=X)).
  Proof.
    move=> ?[??][??][/=/leibniz_equiv_iff<- eq]. rewrite ty_sty_unseal.
    split=>//=. split=>//= >. f_equiv=> ?. f_equiv. apply eq.
  Qed.
  (** [sty_pty] is size-preserving *)
  #[export] Instance sty_pty_preserv {X} : Preserv (@sty_pty CON Σ X).
  Proof.
    move=> ?[??][??][/=/leibniz_equiv_iff<- eq]. unfold sty_pty=>/=.
    f_equiv=> >. f_equiv=> ?. f_equiv. apply eq.
  Qed.
  (** [ty_pty] is size-preserving *)
  #[export] Instance ty_pty_preserv {X} : Preserv (ty_pty (X:=X)).
  Proof. solve_proper. Qed.

  (** Simplify [≡] over [ty] *)
  Lemma ty_equiv {X T U} :
    T ≡@{ty CON Σ X} U ↔ ty_size T = ty_size U ∧
      (∀ t d xπ vl, ty_own T t d xπ vl ≡ ty_own U t d xπ vl) ∧
      (∀ t d l α xπ, ty_shr T t d l α xπ ≡ ty_shr U t d l α xπ).
  Proof. done. Qed.
  (** Simplify [proeqv] over [ty] *)
  Lemma ty_proeqv {X T U k} :
    T ≡[k]@{ty CON Σ X}≡ U ↔ ty_size T = ty_size U ∧
      (∀ t d xπ vl, ty_own T t d xπ vl ≡[k]≡ ty_own U t d xπ vl) ∧
      (∀ t d l α xπ, ty_shr T t d l α xπ ≡[k]≡ ty_shr U t d l α xπ).
  Proof. done. Qed.
  (** Simplify [proeqv_later] over [ty] *)
  Lemma ty_proeqv_later {X T U k} :
    T ≡[<k]@{ty CON Σ X}≡ U →
      (∀ t d xπ vl, ty_own T t d xπ vl ≡[<k]≡ ty_own U t d xπ vl) ∧
      (∀ t d l α xπ, ty_shr T t d l α xπ ≡[<k]≡ ty_shr U t d l α xπ).
  Proof. by case: k=>//= ?[??]. Qed.

  (** Simplify [≡] over [sty] *)
  Lemma sty_equiv {X T U} :
    T ≡@{sty CON Σ X} U ↔ sty_size T = sty_size U ∧
      (∀ t d xπ vl, sty_own T t d xπ vl ≡ sty_own U t d xπ vl).
  Proof. done. Qed.
  (** Simplify [proeqv] over [sty] *)
  Lemma sty_proeqv {X T U k} :
    T ≡[k]@{sty CON Σ X}≡ U ↔ sty_size T = sty_size U ∧
      (∀ t d xπ vl, sty_own T t d xπ vl ≡[k]≡ sty_own U t d xπ vl).
  Proof. done. Qed.

  (** Simplify [≡] over [pty] *)
  Lemma pty_equiv {X T U} :
    T ≡@{pty CON Σ X} U ↔ pty_size T = pty_size U ∧
      (∀ x vl, pty_own T x vl ≡ pty_own U x vl).
  Proof. done. Qed.
  (** Simplify [proeqv] over [pty] *)
  Lemma pty_proeqv {X T U k} :
    T ≡[k]@{pty CON Σ X}≡ U ↔ pty_size T = pty_size U ∧
      (∀ x vl, pty_own T x vl ≡[k]≡ pty_own U x vl).
  Proof. done. Qed.
End ty.

(** ** Basic properties of a type *)

Section ty.
  Context `{!Csem CON JUDG Σ}.

  (** Basic properties of a type *)
  Class Ty {X} (T : ty CON Σ X) : Prop := TY {
    (** The sharing predicate is persistent *)
    ty_shr_persistent {t d l α xπ δ} :: Persistent ⟦ ty_shr T t d l α xπ ⟧ᶜ(δ);
    (** The ownership predicate entails the size constraint *)
    ty_own_size {t d xπ vl δ} :
      ⟦ ty_own T t d xπ vl ⟧ᶜ(δ) ⊢ ⌜length vl = ty_size T⌝;
    (** The depth of the ownership and sharing predicates can be bumped up *)
    ty_own_depth {t d d' xπ vl δ} :
      d ≤ d' → ⟦ ty_own T t d xπ vl ⟧ᶜ(δ) ⊢ ⟦ ty_own T t d' xπ vl ⟧ᶜ(δ);
    ty_shr_depth {t d d' l α xπ δ} :
      d ≤ d' → ⟦ ty_shr T t d l α xπ ⟧ᶜ(δ) ⊢ ⟦ ty_shr T t d' l α xπ ⟧ᶜ(δ);
    (** The ownership and sharing predicates are proper over the clairvoyant
      value *)
    ty_own_clair {t d xπ xπ' vl δ} : (∀ π, xπ π = xπ' π) →
      ⟦ ty_own T t d xπ vl ⟧ᶜ(δ) ⊢ ⟦ ty_own T t d xπ' vl ⟧ᶜ(δ);
    ty_shr_clair {t d l α xπ xπ' δ} : (∀ π, xπ π = xπ' π) →
      ⟦ ty_shr T t d l α xπ ⟧ᶜ(δ) ⊢ ⟦ ty_shr T t d l α xπ' ⟧ᶜ(δ);
  }.

  (** [ty_own_clair] applied to [⊣⊢] *)
  Lemma ty_own_clair' `{!@Ty X T} {t d xπ xπ' vl δ} : (∀ π, xπ π = xπ' π) →
    ⟦ ty_own T t d xπ vl ⟧ᶜ(δ) ⊣⊢ ⟦ ty_own T t d xπ' vl ⟧ᶜ(δ).
  Proof. move=> ?. apply bi.equiv_entails. split; by apply: ty_own_clair. Qed.
  (** [ty_shr_clair] applied to [⊣⊢] *)
  Lemma ty_shr_clair' `{!@Ty X T} {t d l α xπ xπ' δ} : (∀ π, xπ π = xπ' π) →
    ⟦ ty_shr T t d l α xπ ⟧ᶜ(δ) ⊣⊢ ⟦ ty_shr T t d l α xπ' ⟧ᶜ(δ).
  Proof. move=> ?. apply bi.equiv_entails. split; by apply: ty_shr_clair. Qed.

  (** Basic properties of a simple type *)
  Class Sty {X} (T : sty CON Σ X) : Prop := STY {
    (** The ownership predicate is persistent *)
    sty_own_persistent {t d xπ vl δ} :: Persistent ⟦ sty_own T t d xπ vl ⟧ᶜ(δ);
    (** The ownership predicate entails the size constraint *)
    sty_own_size {t d xπ vl δ} :
      ⟦ sty_own T t d xπ vl ⟧ᶜ(δ) ⊢ ⌜length vl = sty_size T⌝;
    (** The depth of the ownership predicate can be bumped up *)
    sty_own_depth {t d d' xπ vl δ} :
      d ≤ d' → ⟦ sty_own T t d xπ vl ⟧ᶜ(δ) ⊢ ⟦ sty_own T t d' xπ vl ⟧ᶜ(δ);
    (** The ownership predicates is proper over the clairvoyant value *)
    sty_own_clair {t d xπ xπ' vl δ} : (∀ π, xπ π = xπ' π) →
      ⟦ sty_own T t d xπ vl ⟧ᶜ(δ) ⊢ ⟦ sty_own T t d xπ' vl ⟧ᶜ(δ);
  }.

  (** [sty_own_clair] applied to [⊣⊢] *)
  Lemma sty_own_clair' `{!@Sty X T} {t d xπ xπ' vl δ} : (∀ π, xπ π = xπ' π) →
    ⟦ sty_own T t d xπ vl ⟧ᶜ(δ) ⊣⊢ ⟦ sty_own T t d xπ' vl ⟧ᶜ(δ).
  Proof. move=> ?. apply bi.equiv_entails. split; exact: sty_own_clair. Qed.

  (** Basic properties of a plain type *)
  Class Pty {X} (T : pty CON Σ X) : Prop := PTY {
    (** The ownership predicate is persistent *)
    pty_own_persistent {x vl δ} :: Persistent ⟦ pty_own T x vl ⟧ᶜ(δ);
    (** The ownership predicate entails the size constraint *)
    pty_own_size {x vl δ} : ⟦ pty_own T x vl ⟧ᶜ(δ) ⊢ ⌜length vl = pty_size T⌝;
  }.

  (** [Ty], [Sty], [Pty] are proper *)
  #[export] Instance Ty_proper {X} : Proper ((≡) ==> (↔)) (@Ty X).
  Proof.
    have pro : Proper ((≡) ==> impl) (@Ty X); last first.
    { move=> ?*. split; by apply pro. }
    move=> ?? /ty_equiv[eqZ[eqvO eqvS]]. split=>/= >.
    - rewrite -(eqvS _ _ _ _ _). exact _.
    - rewrite -(eqvO _ _ _ _) -eqZ. exact ty_own_size.
    - rewrite -!(eqvO _ _ _ _). exact ty_own_depth.
    - rewrite -!(eqvS _ _ _ _ _). exact ty_shr_depth.
    - rewrite -!(eqvO _ _ _ _). exact ty_own_clair.
    - rewrite -!(eqvS _ _ _ _ _). exact ty_shr_clair.
  Qed.
  #[export] Instance Sty_proper {X} : Proper ((≡) ==> (↔)) (@Sty X).
  Proof.
    have pro : Proper ((≡) ==> impl) (@Sty X); last first.
    { move=> ?*. split; by apply pro. }
    move=> ?? /sty_equiv[eqZ eqvO]. split=> >; rewrite -!(eqvO _ _ _ _).
    { exact _. } { rewrite -eqZ. exact sty_own_size. }
    { exact sty_own_depth. } { exact sty_own_clair. }
  Qed.
  #[export] Instance Pty_proper {X} : Proper ((≡) ==> (↔)) (@Pty X).
  Proof.
    have pro : Proper ((≡) ==> impl) (@Pty X); last first.
    { move=> ?*. split; by apply pro. }
    move=> ?? /pty_equiv[eqZ eqvO]. split=> >; rewrite -(eqvO _ _).
    { exact _. } { rewrite -eqZ. exact pty_own_size. }
  Qed.

  Context `{!rust_haltGS CON Σ, !rust_haltC CON, !rust_haltJ CON JUDG Σ,
    !rust_haltCS CON JUDG Σ}.

  (** [Sty] entails [Ty] *)
  #[export] Instance Ty_Sty `{!@Sty X T} : Ty (ty_sty T).
  Proof.
    rewrite ty_sty_unseal. split=>/= >. { exact _. }
    { exact sty_own_size. } { exact sty_own_depth. }
    { move=> ?. do 3 f_equiv. by apply sty_own_depth. } { exact sty_own_clair. }
    { move=> ?. do 3 f_equiv. by apply sty_own_clair. }
  Qed.

  (** [Pty] entails [Sty] *)
  #[export] Instance Sty_Pty `{!@Pty X T} : Sty (sty_pty T).
  Proof.
    split=> > /=; [exact _| |done|].
    - iIntros "[%[% ?]]". iStopProof. exact pty_own_size.
    - move=> eq. f_equiv=> ?. do 2 f_equiv. move=> ??. by rewrite -eq.
  Qed.
End ty.
Hint Mode Ty - - - - - ! : typeclass_instances.
Hint Mode Sty - - - - - ! : typeclass_instances.
Hint Mode Pty - - - - - ! : typeclass_instances.

(** ** Basic operations on a type *)

Section ty_op.
  Context `{!rust_haltGS CON Σ, !rust_haltJ CON JUDG Σ, !Csem CON JUDG Σ,
    !Jsem JUDG (iProp Σ)}.

  (** The body formula of the borrow for [ty_share] *)
  Definition cif_pointsto_ty {X} (T : ty CON Σ X) l t d xπ : cifOF CON $oi Σ :=
    (∃ vl, ▷ l ↦∗ vl ∗ ty_own T t d xπ vl)%cif.

  (** [TyOpAt]: Basic operations on a type at a depth *)
  Class TyOpAt {X} (T : ty CON Σ X) (κ : lft) (d : nat) : Prop := TY_OP_AT {
    (** Take out prophecy tokens from ownership and sharing formulas *)
    ty_own_proph {t xπ vl q} :
      q.[κ] -∗ ⟦ ty_own T t d xπ vl ⟧ᶜ =[rust_halt_wsat]{⊤}=∗ ∃ ξl r,
        ⌜proph_dep xπ ξl⌝ ∧ r:∗[ξl] ∗
        (r:∗[ξl] =[rust_halt_wsat]{⊤}=∗ q.[κ] ∗ ⟦ ty_own T t d xπ vl ⟧ᶜ);
    ty_shr_proph {t l α xπ q} :
      q.[κ ⊓ α] -∗ ⟦ ty_shr T t d l α xπ ⟧ᶜ =[rust_halt_wsat]{⊤}=∗ ∃ ξl r,
        ⌜proph_dep xπ ξl⌝ ∧
        r:∗[ξl] ∗ (r:∗[ξl] =[rust_halt_wsat]{⊤}=∗ q.[κ ⊓ α]);
    (** A borrow over the ownership formula can turn into the sharing formula *)
    ty_share {t l α xπ q} :
      q.[κ ⊓ α] -∗ bord α (cif_pointsto_ty T l t d xπ)
        =[rust_halt_wsat]{⊤}=∗ q.[κ ⊓ α] ∗ ⟦ ty_shr T t d l α xπ ⟧ᶜ;
  }.

  (** [TyOpAt] is monotone *)
  #[export] Instance TyOpAt_mono {X} :
    Proper ((≡) ==> (⊑) --> (=) ==> impl) (@TyOpAt X).
  Proof.
    move=> T T' /ty_equiv[?[eqvO eqvS]] κ κ' /= ??? <- ?.
    have ? : LftIncl κ' κ by done. split.
    - move=> >. setoid_rewrite <-(eqvO _ _ _ _). iIntros "κ' T".
      iDestruct (lft_incl'_live_acc (α:=κ) with "κ'") as (?) "[κ →κ']"=>//.
      iMod (ty_own_proph with "κ T") as (??) "($ & $ & →T)". iModIntro.
      iIntros "ξl". iMod ("→T" with "ξl") as "[κ $]". iModIntro.
      by iApply "→κ'".
    - move=> ?? α ??. setoid_rewrite <-(eqvS _ _ _ _ _). iIntros "κ'α T".
      iDestruct (lft_incl'_live_acc (α:=κ ⊓ α) with "κ'α") as (?) "[κα →κ'α]".
      iMod (ty_shr_proph with "κα T") as (??) "($ & $ & →κα)". iModIntro.
      iIntros "ξl". iMod ("→κα" with "ξl") as "κα". iModIntro. by iApply "→κ'α".
    - move=> ?? α ??. rewrite -(eqvS _ _ _ _ _). iIntros "κ'α b".
      iDestruct (lft_incl'_live_acc (α:=κ ⊓ α) with "κ'α") as (?) "[κα →κ'α]".
      iMod (ty_share with "κα [b]") as "[κα $]"; last first.
      { iModIntro. by iApply "→κ'α". }
      iStopProof. apply bi.equiv_entails. unfold cif_pointsto_ty.
      (do 2 f_equiv)=> ?. by rewrite (eqvO _ _ _ _).
  Qed.
  #[export] Instance TyOpAt_flip_mono {X} :
    Proper ((≡) ==> (⊑) ==> (=) ==> flip impl) (@TyOpAt X).
  Proof. move=> ?*?*??<- /=. exact: TyOpAt_mono. Qed.
  #[export] Instance TyOpAt_proper {X} :
    Proper ((≡) ==> (=) --> (=) ==> (↔)) (@TyOpAt X).
  Proof. move=> ?*??<-??<-. split; exact: TyOpAt_mono. Qed.

  (** [TyOpLt]: Basic operations on a type below a depth *)
  Class TyOpLt {X} (T : ty CON Σ X) (κ : lft) (d : nat) : Prop :=
    ty_op_lt : ∀ {d'}, d' < d → TyOpAt T κ d'.

  (** [TyOpLt] is monotone *)
  #[export] Instance TyOpLt_mono {X} :
    Proper ((≡) ==> (⊑) --> (≤) --> impl) (@TyOpLt X).
  Proof.
    move=> ?*?* d d' /= ? wl d'' ?. have lt : d'' < d by lia. move: (wl _ lt).
    exact: TyOpAt_mono.
  Qed.
  #[export] Instance TyOpLt_flip_mono {X} :
    Proper ((≡) ==> (⊑) ==> (≤) ==> flip impl) (@TyOpLt X).
  Proof. move=> ?*?*?* /=. exact: TyOpLt_mono. Qed.
  #[export] Instance TyOpLt_proper {X} :
    Proper ((≡) ==> (=) ==> (=) ==> (↔)) (@TyOpLt X).
  Proof. move=> ?*?? <- ?? <-. split; exact: TyOpLt_mono. Qed.

  (** Lemmas under [TyOpLt] *)
  Section ty_op_lt.
    Context `(!@TyOpLt X T κ d0).
    Lemma ty_own_proph_lt {t d xπ vl q} : d < d0 →
      q.[κ] -∗ ⟦ ty_own T t d xπ vl ⟧ᶜ =[rust_halt_wsat]{⊤}=∗ ∃ ξl r,
        ⌜proph_dep xπ ξl⌝ ∧ r:∗[ξl] ∗
        (r:∗[ξl] =[rust_halt_wsat]{⊤}=∗ q.[κ] ∗ ⟦ ty_own T t d xπ vl ⟧ᶜ).
    Proof. move=> ?. by apply ty_op_lt. Qed.
    Lemma ty_shr_proph_lt {t d l α xπ q} : d < d0 →
      q.[κ ⊓ α] -∗ ⟦ ty_shr T t d l α xπ ⟧ᶜ =[rust_halt_wsat]{⊤}=∗ ∃ ξl r,
        ⌜proph_dep xπ ξl⌝ ∧
        r:∗[ξl] ∗ (r:∗[ξl] =[rust_halt_wsat]{⊤}=∗ q.[κ ⊓ α]).
    Proof. move=> ?. by apply ty_op_lt. Qed.
    Lemma ty_share_lt {t d l α xπ q} : d < d0 →
      q.[κ ⊓ α] -∗ bord α (∃ vl, ▷ l ↦∗ vl ∗ ty_own T t d xπ vl)%cif
        =[rust_halt_wsat]{⊤}=∗ q.[κ ⊓ α] ∗ ⟦ ty_shr T t d l α xπ ⟧ᶜ.
    Proof. move=> ?. by apply ty_op_lt. Qed.
  End ty_op_lt.

  Context `{!rust_haltC CON, !rust_haltCS CON JUDG Σ, !rust_haltJS CON JUDG Σ}.

  (** Basic operations on a simple type at a depth *)
  Lemma sty_op_at `{!Sty (X:=X) T} {d} κ :
    (∀ t xπ vl q,
      q.[κ] -∗ ⟦ sty_own T t d xπ vl ⟧ᶜ =[rust_halt_wsat]{⊤}=∗ ∃ ξl r,
        ⌜proph_dep xπ ξl⌝ ∧ r:∗[ξl] ∗ (r:∗[ξl] =[rust_halt_wsat]{⊤}=∗ q.[κ])) →
    TyOpAt (ty_sty T) κ d.
  Proof.
    move=> sty_proph. rewrite ty_sty_unseal. split=>/= >.
    - iIntros "κ #T". iFrame "T". iApply (sty_proph with "κ T").
    - iIntros "[κ $] (%vl & _ & T)".
      iMod (sty_proph with "κ T") as (??) "($ & $ & cl)". iIntros "!> ξl".
      by iApply "cl".
    - iIntros "[$ α] b".
      iMod (bord_open (M:=borrowM) with "α b") as "/=[o (% & >↦ & #T)]".
      iFrame "T".
      iMod (obord_subdiv (FML:=cifOF _) (M:=borrowM) [▷ _]%cif
        with "[] o [$↦ //] []") as "(α & _ & [b _])"=>/=.
      { iApply lft_sincl_refl. } { by iIntros "_ [$ _]". }
      by iMod (spointsto_vec_alloc with "α b") as "[$$]".
  Qed.

  (** Basic operations on a plain type at a depth *)
  #[export] Instance pty_op_at `{!Pty (X:=X) T} {κ d} :
    TyOpAt (ty_pty T) κ d.
  Proof.
    apply sty_op_at=>/= ????. iIntros "$ (% & % & ?) !>". iExists [], 1%Qp.
    iSplit; [iPureIntro; exact: proph_dep_const|]. iSplit=>//. by iIntros.
  Qed.
End ty_op.
Hint Mode TyOpAt - - - - - - - - ! - - : typeclass_instances.
Hint Mode TyOpLt - - - - - - - - ! - - : typeclass_instances.

(** [TyOp]: Basic operations on a type *)
Notation TyOp T κ := (∀ d, TyOpAt T κ d).
Notation TyOp' X T κ := (∀ d, TyOpAt (X:=X) T κ d) (only parsing).

(** ** Namespaces and masks *)

(** For RustHalt *)
Definition rust_haltN : namespace := nroot.@"rust_halt".
(** For sharing *)
Definition shrN : namespace := rust_haltN.@"shr".

(** The mask for the region from the location *)
Fixpoint shr_locsE (l : loc) (sz : nat) : coPset :=
  match sz with 0 => ∅ | S sz' => ↑shrN.@l ∪ shr_locsE (l +ₗ 1%nat) sz' end.

(** [shr_locsE] over a sum size *)
Lemma shr_locsE_add {l sz sz'} :
  shr_locsE l (sz + sz') = shr_locsE l sz ∪ shr_locsE (l +ₗ sz) sz'.
Proof.
  apply leibniz_equiv. move: l. elim: sz=>/=.
  { move=> ?. by rewrite shift_loc_0 left_id. }
  move=> ? IH l. rewrite -union_assoc IH. do 3 f_equiv. by rewrite -shift_loc_S.
Qed.
(** Disjointness of adjacent [shr_locsE]s *)
Lemma shr_locsE_disj {l sz sz'} : shr_locsE l sz ## shr_locsE (l +ₗ sz) sz'.
Proof.
  move: l. elim: sz=>/=; [set_solver|]=> n IH l. apply disjoint_union_l.
  split; [|by rewrite (shift_loc_S _ n)]. clear IH. move: n.
  elim: sz'=>/=; [set_solver|]=> ? IH ?. apply disjoint_union_r.
  split; [|by rewrite shift_loc_assoc_nat Nat.add_comm]. apply ndot_ne_disjoint.
  case l=> ??. case. lia.
Qed.
(** Inclusion into [shrN] *)
Lemma shr_locsE_shrN {l sz} : shr_locsE l sz ⊆ ↑shrN.
Proof.
  move: l. elim: sz=>/=; [set_solver|]=> *. apply union_least; [|done].
  solve_ndisj.
Qed.
(** [shr_locsE] is monotone over the size *)
Lemma shr_locsE_mono {l sz sz'} : sz ≤ sz' → shr_locsE l sz ⊆ shr_locsE l sz'.
Proof.
  move: l. move: sz'. elim: sz=>/=; [set_solver|]=> ? IH. case; [lia|]=>/= ???.
  apply union_mono_l. apply IH. lia.
Qed.

(** ** Type classes *)

Section classes.
  Context {CON Σ}.

  (** [Send]: the ownership formula does not depend on the thread id *)
  Class Send {X} (T : ty CON Σ X) : Prop :=
    send : ∀ {t t' d xπ vl}, ty_own T t d xπ vl ≡ ty_own T t' d xπ vl.
  (** [Send] is proper *)
  #[export] Instance Send_proper {X} : Proper ((≡) ==> (↔)) (@Send X).
  Proof.
    move=> ?? /ty_equiv[_[eqv _]]. do 5 apply forall_proper=> ?.
    by rewrite !eqv.
  Qed.

  (** [Sync]: the sharing formula does not depend on the thread id *)
  Class Sync {X} (T : ty CON Σ X) : Prop :=
    sync : ∀ {t t' l α xπ}, ty_shr T t l α xπ ≡ ty_shr T t' l α xπ.
  (** [Sync] is proper *)
  #[export] Instance Sync_proper {X} : Proper ((≡) ==> (↔)) (@Sync X).
  Proof.
    move=> ?? /ty_equiv[_[_ eqv]]. do 6 apply forall_proper=> ?.
    by rewrite !eqv.
  Qed.

  Context `{!rust_haltGS CON Σ, !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ)}.

  (** [Copy] *)
  Class Copy {X} (T : ty CON Σ X) : Prop := COPY {
    (** Persistence of the ownership formula *)
    copy_persistent {t d xπ vl δ} :: Persistent ⟦ ty_own T t d xπ vl ⟧ᶜ(δ);
    (** Access via the sharing formula *)
    copy_shr_acc {t d l α xπ q F} : shr_locsE l (ty_size T + 1) ⊆ F →
      q.[α] -∗ na_own t F -∗ ⟦ ty_shr T t d l α xπ ⟧ᶜ =[rust_halt_wsat]{⊤}=∗
        ∃ vl r, l ↦∗{r} vl ∗ na_own t (F ∖ shr_locsE l (ty_size T)) ∗
          ⟦ ty_own T t d xπ vl ⟧ᶜ ∗
          (l ↦∗{r} vl -∗ na_own t (F ∖ shr_locsE l (ty_size T))
            =[rust_halt_wsat]{⊤}=∗ q.[α] ∗ na_own t F);
  }.
  (** [Copy] is proper *)
  #[export] Instance Copy_proper {X} : Proper ((≡) ==> (↔)) (@Copy X).
  Proof.
    have pro: Proper ((≡) ==> impl) (@Copy X); last first.
    { move=> ???. split; by apply pro. }
    move=> ?? /ty_equiv[eqZ[eqvO eqvS]]. split=> *.
    - rewrite -(eqvO _ _ _ _). exact _.
    - rewrite -(eqvS _ _ _ _ _) -eqZ. setoid_rewrite <-(eqvO _ _ _ _).
      apply copy_shr_acc. by rewrite eqZ.
  Qed.

  Context `{!rust_haltC CON, !rust_haltJ CON JUDG Σ, !rust_haltCS CON JUDG Σ}.

  (** [Send] over [sty] entails [Sync] *)
  #[export] Instance sty_send_sync `{!Send (ty_sty (X:=X) T)} :
    Sync (ty_sty (X:=X) T).
  Proof.
    move=> >. move: Send0. rewrite ty_sty_unseal=>/= Send0.
    f_equiv=> ?. f_equiv. exact: Send0.
  Qed.

  (** [pty] is [Send] and [Sync] *)
  #[export] Instance pty_send {X T} : Send (ty_pty (X:=X) T).
  Proof. by rewrite /ty_pty ty_sty_unseal=>/= ?. Qed.
  #[export] Instance pty_sync {X T} : Sync (ty_pty (X:=X) T).
  Proof. exact _. Qed.

  (** [sty] is [Copy] *)
  #[export] Instance sty_copy `{!Sty (X:=X) T} : Copy (ty_sty (X:=X) T).
  Proof.
    rewrite ty_sty_unseal. split; [exact _|]=>/= *.
    iIntros "α F (% & >↦ & $)".
    iMod (spointsto_vec_acc with "α ↦") as (?) "[$ cl]".
    iDestruct (na_own_acc with "F") as "[$ →F]"; [set_solver|].
    iIntros "!> ↦s F∖". iMod ("cl" with "↦s") as "$". iModIntro. by iApply "→F".
  Qed.
End classes.
Hint Mode Send - - - ! : typeclass_instances.
Hint Mode Sync - - - ! : typeclass_instances.
Hint Mode Copy - - - - - - - ! : typeclass_instances.

(** ** Resolution over a type *)

Section resol.
  Context `{!rust_haltGS CON Σ, !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ)}.

  (** [ResolAt]: Resolution over a type at a depth *)
  Class ResolAt {X} (T : ty CON Σ X) (κ : lft) (post : X → Prop) (d : nat)
    : Prop := RESOL_AT {
    resol {t xπ vl q} :
      q.[κ] -∗ na_own t ⊤ -∗ ⟦ ty_own T t d xπ vl ⟧ᶜ =[rust_halt_wsat]{⊤}=∗
        q.[κ] ∗ na_own t ⊤ ∗ ⟨π, post (xπ π)⟩;
  }.

  (** [ResolAt] is monotone *)
  #[export] Instance ResolAt_mono {X} :
    Proper ((≡) ==> (⊑) --> pointwise_relation _ impl ==> (=) ==> impl)
      (@ResolAt X).
  Proof.
    move=> ?? /ty_equiv[_[eqv _]] κ κ' /= ??? to ??<-?.
    have ? : LftIncl κ' κ by done. split=>/= >. iIntros "κ' t T".
    iDestruct (lft_incl'_live_acc (α:=κ) with "κ'") as (?) "[κ →κ']".
    rewrite -(eqv _ _ _ _). iMod (resol with "κ t T") as "(κ & $ & post)".
    iDestruct ("→κ'" with "κ") as "$". iModIntro.
    iApply (proph_obs_impl with "post")=> ?. apply to.
  Qed.
  #[export] Instance ResolAt_flip_mono {X} :
    Proper ((≡) ==> (⊑) ==> pointwise_relation _ (flip impl) ==> (=) ==>
      flip impl) (@ResolAt X).
  Proof.
    move=> ?*?*?? to ?? <-. eapply ResolAt_mono; [done..|exact to|done].
  Qed.
  #[export] Instance ResolAt_proper {X} :
    Proper ((≡) ==> (=) ==> pointwise_relation _ (↔) ==> (=) ==> (↔))
      (@ResolAt X).
  Proof.
    move=> ?*?? <- ?? iff ?? <-.
    split; apply ResolAt_mono=>//= ??; by apply iff.
  Qed.

  (** Trivial resolution *)
  #[export] Instance resol_true {X T κ d} : @ResolAt X T κ (λ _, True) d | 100.
  Proof. split=> >. iIntros "$ $ _ !>". by iApply proph_obs_true. Qed.

  (** [ResolLt]: Resolution over a type below a depth *)
  Class ResolLt {X} (T : ty CON Σ X) (κ : lft) (post : X → Prop) (d : nat)
    : Prop :=
    resol_lt' : ∀ {d'}, d' < d → ResolAt T κ post d'.

  (** [ResolLt] is monotone *)
  #[export] Instance ResolLt_mono {X} :
    Proper ((≡) ==> (⊑) --> pointwise_relation _ impl ==> (≤) --> impl)
      (@ResolLt X).
  Proof.
    move=> ?*?*?*?? /= ????. eapply ResolAt_mono=>//. apply resol_lt'. lia.
  Qed.
  #[export] Instance ResolLt_flip_mono {X} :
    Proper ((≡) ==> (⊑) ==> pointwise_relation _ (flip impl) ==> (≤) ==>
      flip impl) (@ResolLt X).
  Proof. move=> ?*?*?*?*. exact: ResolLt_mono. Qed.
  #[export] Instance ResolLt_proper {X} :
    Proper ((≡) ==> (=) ==> pointwise_relation _ (↔) ==> (=) ==> (↔))
      (@ResolLt X).
  Proof.
    move=> ?*?? <- ?? iff ?? <-.
    split; eapply ResolLt_mono=>//= ??; by apply iff.
  Qed.

  (** [resol] under [ResolLt] *)
  Lemma resol_lt `{!@ResolLt X T κ post d} {d' t xπ vl q} : d' < d →
    q.[κ] -∗ na_own t ⊤ -∗ ⟦ ty_own T t d' xπ vl ⟧ᶜ =[rust_halt_wsat]{⊤}=∗
      q.[κ] ∗ na_own t ⊤ ∗ ⟨π, post (xπ π)⟩.
  Proof. move=> ?. by apply @resol, resol_lt'. Qed.
End resol.
(** [Resol]: Resolution over a type *)
Notation Resol T κ post := (∀ d, ResolAt T κ post d).
Notation Resol' X T κ post := (∀ d, ResolAt (X:=X) T κ post d) (only parsing).

(** ** Taking the real, or non-prophetic, part out of types *)

Section real.
  Context `{!rust_haltGS CON Σ, !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ),
    !rust_haltC CON, !rust_haltJ CON JUDG Σ, !rust_haltCS CON JUDG Σ}.

  (** [RealAt]: Taking the real part out of a type at a depth *)
  Class RealAt {X A} (T : ty CON Σ X) (κ : lft) (get : X → A) (d : nat)
    : Prop := REAL_AT {
    real_own {t xπ vl q} :
      q.[κ] -∗ na_own t ⊤ -∗ ⟦ ty_own T t d xπ vl ⟧ᶜ =[rust_halt_wsat]{⊤}=∗
        ⌜∃ y, ∀ π, get (xπ π) = y⌝ ∧
        q.[κ] ∗ na_own t ⊤ ∗ ⟦ ty_own T t d xπ vl ⟧ᶜ;
    real_shr {t l α xπ q} :
      q.[κ] -∗ na_own t ⊤ -∗ ⟦ ty_shr T t d l α xπ ⟧ᶜ =[rust_halt_wsat]{⊤}=∗
        ⌜∃ y, ∀ π, get (xπ π) = y⌝ ∧ q.[κ] ∗ na_own t ⊤;
  }.

  (** [RealAt] is monotone *)
  #[export] Instance RealAt_mono {X A} :
    Proper ((≡) ==> (⊑) --> (=) ==> (=) ==> impl) (@RealAt X A).
  Proof.
    move=> ?? /ty_equiv[_[eqvO eqvS]] κ κ' /= ???<-??<-?.
    have ? : LftIncl κ' κ by done.
    split=>/= >; iIntros "κ' t T";
      iDestruct (lft_incl'_live_acc (α:=κ) with "κ'") as (?) "[κ →κ']";
      [rewrite -(eqvO _ _ _ _);
        iMod (real_own with "κ t T") as "($ & κ & $)"|
        rewrite -(eqvS _ _ _ _ _);
          iMod (real_shr with "κ t T") as "($ & κ & $)"];
      by iDestruct ("→κ'" with "κ") as "$".
  Qed.
  #[export] Instance RealAt_flip_mono {X A} :
    Proper ((≡) ==> (⊑) ==> (=) ==> (=) ==> flip impl) (@RealAt X A).
  Proof. move=> ?*?*??<-??<-. exact: RealAt_mono. Qed.
  #[export] Instance RealAt_proper {X A} :
    Proper ((≡) ==> (=) ==> (=) ==> (=) ==> (↔)) (@RealAt X A).
  Proof.
    move=> ?*??<-??<-??<-. split; apply RealAt_mono=>//= ??; by apply iff.
  Qed.
  (** Update the getter function of [RealAt] *)
  Lemma real_at_fun `(@RealAt X A T κ get d) {B} f :
    @RealAt _ B T κ (f ∘ get) d.
  Proof.
    split=> >; iIntros "κ t T";
      [iMod (real_own with "κ t T") as ([? eq]) "$"|
        iMod (real_shr with "κ t T") as ([? eq]) "$"];
      iPureIntro; eexists _=>/= ?; by rewrite eq.
  Qed.

  (** Trivial real part *)
  #[export] Instance real_unit {X T κ d} : @RealAt X _ T κ (λ _, ()) d | 100.
  Proof. split=> >; iIntros "$ $ ? !>"; iFrame; by iExists (). Qed.

  (** [RealAt] over a simple type *)
  Lemma sty_real `{!Sty (X:=X) T} {A κ get d} :
    (∀ t xπ vl q,
      q.[κ] -∗ na_own t ⊤ -∗ ⟦ sty_own T t d xπ vl ⟧ᶜ =[rust_halt_wsat]{⊤}=∗
        ⌜∃ y, ∀ π, get (xπ π) = y⌝ ∧ q.[κ] ∗ na_own t ⊤) →
    @RealAt X A (ty_sty T) κ get d.
  Proof.
    rewrite ty_sty_unseal=> real. split=>/= >.
    - iIntros "κ t #T". by iMod (real with "κ t T") as "($ & $ & $)".
    - iIntros "κ t (% & _ & T)". by iMod (real with "κ t T") as "($ & $ & $)".
  Qed.
  (** [RealAt] over a plain type *)
  #[export] Instance pty_real `{!Pty (X:=X) T} {κ d} :
    @RealAt X _ (ty_pty T) κ id d.
  Proof. apply: sty_real=>/= >. iIntros "$ $ (% & % & _) !%". by eexists _. Qed.

  (** [RealLt]: Taking the real part out of a type below a depth *)
  Class RealLt {X A} (T : ty CON Σ X) (κ : lft) (get : X → A) (d : nat)
    : Prop :=
    real_lt : ∀ {d'}, d' < d → RealAt T κ get d'.

  (** [RealLt] is monotone *)
  #[export] Instance RealLt_mono {X A} :
    Proper ((≡) ==> (⊑) --> (=) ==> (≤) --> impl) (@RealLt X A).
  Proof.
    move=> ?*?*?*?? /= ????. eapply RealAt_mono=>//. apply real_lt. lia.
  Qed.
  #[export] Instance RealLt_flip_mono {X A} :
    Proper ((≡) ==> (⊑) ==> (=) ==> (≤) ==> flip impl) (@RealLt X A).
  Proof. move=> ?*?*?*?*. by eapply RealLt_mono. Qed.
  #[export] Instance RealLt_proper {X A} :
    Proper ((≡) ==> (=) ==> (=) ==> (=) ==> (↔)) (@RealLt X A).
  Proof. move=> ?*??<-??<-??<-.  split; by eapply RealLt_mono. Qed.

  (** [real_own] and [real_shr] under [RealLt] *)
  Lemma real_own_lt `{!@RealLt X A T κ get d} {d' t xπ vl q} : d' < d →
    q.[κ] -∗ na_own t ⊤ -∗ ⟦ ty_own T t d' xπ vl ⟧ᶜ =[rust_halt_wsat]{⊤}=∗
      ⌜∃ y, ∀ π, get (xπ π) = y⌝ ∧
      q.[κ] ∗ na_own t ⊤ ∗ ⟦ ty_own T t d' xπ vl ⟧ᶜ.
  Proof. move=> ?. by apply @real_own, real_lt. Qed.
  Lemma real_shr_lt `{!@RealLt X A T κ get d} {d' t l α xπ q} : d' < d →
    q.[κ] -∗ na_own t ⊤ -∗ ⟦ ty_shr T t d' l α xπ ⟧ᶜ =[rust_halt_wsat]{⊤}=∗
      ⌜∃ y, ∀ π, get (xπ π) = y⌝ ∧ q.[κ] ∗ na_own t ⊤.
  Proof. move=> ?. by apply @real_shr, real_lt. Qed.
End real.
(** [Real]: Taking the real part out of a type at a depth *)
Notation Real T κ get := (∀ d, RealAt T κ get d).
Notation Real' X A T κ get := (∀ d, RealAt (X:=X) (A:=A) T κ get d)
  (only parsing).

(** ** Subtyping *)

Section subty.
  Context `{!rust_haltGS CON Σ, !Csem CON JUDG Σ}.
  Implicit Type δ : JUDG -n> iProp Σ.

  (** [subty]: Subtyping *)
  Definition subty_def δ {X Y} (T : ty CON Σ X) (U : ty CON Σ Y) (f : X → Y)
    : iProp Σ :=
    (* Size equality *) ⌜ty_size T = ty_size U⌝ ∧
    (* Ownership formula conversion *) □ (∀ t d xπ vl,
      ⟦ ty_own T t d xπ vl ⟧ᶜ(δ) -∗ ⟦ ty_own U t d (λ π, f (xπ π)) vl ⟧ᶜ(δ)) ∧
    (* Sharing formula conversion *) □ (∀ t d l α xπ,
      ⟦ ty_shr T t d l α xπ ⟧ᶜ(δ) -∗ ⟦ ty_shr U t d l α (λ π, f (xπ π)) ⟧ᶜ(δ)).
  Lemma subty_aux : @subty_def.(seal). Proof. by eexists. Qed.
  Definition subty δ {X Y} := subty_aux.(unseal) δ X Y.
  Lemma subty_unseal : @subty = @subty_def. Proof. exact: seal_eq. Qed.

  (** [subty] is persistent *)
  #[export] Instance subty_persistent {δ X Y T U f} :
    Persistent (@subty δ X Y T U f).
  Proof. rewrite subty_unseal. exact _. Qed.
  (** [subty] is proper *)
  #[export] Instance subty_proper {δ X Y} :
    Proper ((≡) ==> (≡) ==> (=) ==> (⊣⊢)) (@subty δ X Y).
  Proof.
    rewrite subty_unseal /subty_def=> ?? /ty_equiv[->[eqvO eqvS]].
    move=> ?? /ty_equiv[->[eqvO' eqvS']]??<-. f_equiv.
    do 12 f_equiv; [exact (eqvO _ _ _ _)|exact (eqvO' _ _ _ _)|].
    do 2 f_equiv; [exact (eqvS _ _ _ _ _)|exact (eqvS' _ _ _ _ _)].
  Qed.
  (** [subty] is proper over the clairvoyant value under [Ty] *)
  #[export] Instance subty_proper_clair {δ X T Y} `{!Ty U} :
    Proper (pointwise_relation _ (=) ==> (⊣⊢)) (@subty δ X Y T U).
  Proof.
    have pro : Proper (pointwise_relation _ (=) ==> (⊢)) (@subty δ X Y T U);
      last first.
    { move=> ?*. apply bi.equiv_entails. split; by apply pro. }
    rewrite subty_unseal /subty_def=> ?*. do 12 f_equiv; [exact: ty_own_clair|].
    do 2 f_equiv. exact: ty_shr_clair.
  Qed.
  (** [subty] is reflexive *)
  Lemma subty_refl {δ X T} : ⊢ @subty δ X _ T T id.
  Proof.
    rewrite subty_unseal. iSplit=>//. iSplit; iModIntro; iIntros; iFrame.
  Qed.
  (** [subty] is transitive *)
  Lemma subty_trans {δ X Y Z T U V f g} :
    @subty δ X Y T U f -∗ @subty δ _ Z U V g -∗ @subty δ X Z T V (g ∘ f).
  Proof.
    rewrite subty_unseal. iIntros "[%TUz[#TUo #TUs]][%[#UVo #UVs]]".
    iSplit; [by rewrite TUz|]. iSplit; iModIntro.
    - iIntros (????) "T". iApply "UVo". by iApply "TUo".
    - iIntros (?????) "T". iApply "UVs". by iApply "TUs".
  Qed.

  Context `{!rust_haltC CON, !rust_haltJ CON JUDG Σ, !rust_haltCS CON JUDG Σ}.

  (** [subty] over [sty] *)
  Lemma subty_sty {δ X Y f} T U :
    sty_size T = sty_size U →
    □ (∀ t d xπ vl, ⟦ sty_own T t d xπ vl ⟧ᶜ(δ) -∗
        ⟦ sty_own U t d (λ π, f (xπ π)) vl ⟧ᶜ(δ)) -∗
      @subty δ X Y (ty_sty T) (ty_sty U) f.
  Proof.
    rewrite subty_unseal ty_sty_unseal. iIntros (eq) "#sub". iSplit=>//.
    iSplit=>//=. iIntros (?????) "!> (% & $ & ?)". by iApply "sub".
  Qed.
  (** [subty] over [pty] *)
  Lemma subty_pty {δ X Y f} T U :
    pty_size T = pty_size U →
    □ (∀ x vl, ⟦ pty_own T x vl ⟧ᶜ(δ) -∗ ⟦ pty_own U (f x) vl ⟧ᶜ(δ)) -∗
      @subty δ X Y (ty_pty T) (ty_pty U) f.
  Proof.
    iIntros (?) "#sub". iApply subty_sty=>//=.
    iIntros (????) "!> (% & %eq & ?)". iExists _. iSplit; [|by iApply "sub"].
    iPureIntro=> ?. by rewrite eq.
  Qed.
End subty.

(** Subtyping under [der] *)
Notation subtyd := (subty der).
Notation subtyd' X Y := (subty (X:=X) (Y:=Y) der) (only parsing).

(** ** Path *)

Definition path := expr.
Bind Scope expr_scope with path.

(** Evaluate a path to an optional value *)
Fixpoint of_path (p : path) : option val :=
  match p with
  | BinOp OffsetOp e (#(LitInt n))%E => match of_path e with
      Some #(LitLoc l) => Some #(l +ₗ n) | _ => None end
  | e => to_val e
  end.

(** [of_path] over a value *)
Lemma of_path_val {v : val} : of_path v = Some v.
Proof. case v; [done|]=>/= >. by rewrite (decide_True_pi _). Qed.

(** The path is closed if [of_path] is defined *)
Lemma of_path_closed {p v} : of_path p = Some v → Closed [] p.
Proof.
  move: v. elim p=>//.
  - move=> >. rewrite /of_path=> /of_to_val <-. apply is_closed_of_val.
  - case=>// e IH. case=>//. case=>//= ? _. move: IH. case (of_path e)=>//.
    case=>//. case=>// ? IH ? _. move: (IH _ eq_refl). apply _.
Qed.

(** A path purely evaluates to the value of [of_path] *)
Lemma of_path_pure_exec {p v} : of_path p = Some v → ∃ n, PureExec True n p v.
Proof.
  move: v. elim: p=>//.
  - move=> > [= <-]. exists 0=>/= _. exact: nsteps_O.
  - move=> > _ ? /of_to_val <-. exists 0=> _. exact: nsteps_O.
  - case=>// e IH. case=>//. case=>//= k. move: IH. case (of_path e)=>//.
    case=>//. case=>// l IH _ _ [= <-]. case: (IH (#l) eq_refl)=> n tol.
    exists (S n)=> _. apply: nsteps_r; [|by apply nsteps_once_inv, pure_offset].
    move: (tol I). apply (nsteps_congruence (λ e, e +ₗ #k)%E)=> ??.
    apply: (pure_step_ctx (fill_item (BinOpLCtx _ _))).
Qed.

Section twp.
  Context `{!lrustGS_gen hlc Σ}.

  (** A path evaluates to the value of [of_path] *)
  Lemma twp_path_bind K p {W E v Φ} :
    of_path p = Some v →
    WP[W] fill K (of_val v) @ E [{ Φ }] ⊢ WP[W] fill K p @ E [{ Φ }].
  Proof.
    move=> /of_path_pure_exec[??]. iIntros "?". iApply twp_bind. by wp_pure _.
  Qed.
End twp.
(** Tactics for applying [twp_path_bind] *)
Ltac wp_path p :=
  lazymatch goal with
  | |- envs_entails _ (twp _ _ ?eglob _) =>
        reshape_expr eglob ltac:(fun K e => unify e p;
          iApply (twp_path_bind K p)=>//=)
  end.

(** ** Type context *)

(** Type context element *)
Variant etcx CON Σ : xty → Type :=
| Owned {X} (p : path) (T : ty CON Σ X) : etcx CON Σ X
| Frozen {X} (α : lft) (p : path) (T : ty CON Σ X) : etcx CON Σ X
| Lft (α : lft) : etcx CON Σ unitₓ.
Arguments Owned {_ _ _}. Arguments Frozen {_ _ _}. Arguments Lft {_ _}.
Notation "p ◁ T" := (Owned p T) (at level 55, format "p  ◁  T").
Notation "p ◁[† α ] T" := (Frozen α p T) (at level 55, format "p  ◁[† α ]  T").
Notation "^[ α ]" := (Lft α) (format "^[ α ]").

(** Type context *)
Notation tcx CON Σ := (plist (etcx CON Σ)).

Section tcx.
  Context `{!rust_haltGS CON Σ, !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ)}.

  (** Semantics of a type context element *)
  Definition sem_etcx {X} t (E : etcx CON Σ X) : clair X → iProp Σ :=
    match E with
    | p ◁ T => λ xπ, ∃ v d, ⌜Some v = of_path p⌝ ∧ ⟦ ty_own T t d xπ [v] ⟧ᶜ
    | p ◁[†α] T => λ xπ, ∃ v, ⌜Some v = of_path p⌝ ∧
        ([†α] =[rust_halt_wsat]{⊤}=∗ ∃ d xπ',
          proph_eqz xπ xπ' ∗ ⟦ ty_own T t d xπ' [v] ⟧ᶜ)
    | ^[α] => λ _, ⌜α ≠ ⊤⌝ ∧ 1.[α]
    end%I.

  (** Semantics of a type context *)
  Fixpoint sem_tcx t {Xl} : tcx CON Σ Xl → clair (xlist Xl) → iProp Σ :=
    match Xl with [] => λ _ _, True | _ :: _ => λ '(eΓ, Γ)' xlπ,
      sem_etcx t eΓ (λ π, (xlπ π).1') ∗ sem_tcx t Γ (λ π, (xlπ π).2') end%I.

  (** [sem_tcx] over [ᵖ++] *)
  Lemma sem_tcx_app {t Xl Yl Γ Γ' xlπ ylπ} :
    @sem_tcx t Xl Γ xlπ ∗ @sem_tcx t Yl Γ' ylπ ⊣⊢
      sem_tcx t (Γ ᵖ++ Γ') (λ π, xlπ π ᵖ++ ylπ π).
  Proof.
    move: Γ xlπ. elim: Xl=>/=. { move=> ??. by rewrite left_id. }
    move=> ?? IH ??. by rewrite -IH assoc.
  Qed.
End tcx.

(** ** Type context inclusion and expression typing *)
Section type.
  Context `{!rust_haltGS CON Σ, !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ)}.

  (** [sub]: Inclusion between type contexts *)
  Definition sub_def {Xl Yl} (κ : lft) (Γi : tcx CON Σ Xl) (Γo : tcx CON Σ Yl)
    (pre : xpred Yl → xpred Xl) : iProp Σ :=
    □ ∀ q t postπ xlπ,
      q.[κ] -∗ na_own t ⊤ -∗ ⟨π, pre (postπ π) (xlπ π)⟩ -∗ sem_tcx t Γi xlπ
        =[rust_halt_wsat]{⊤}=∗ ∃ ylπ,
        q.[κ] ∗ na_own t ⊤ ∗ ⟨π, postπ π (ylπ π)⟩ ∗ sem_tcx t Γo ylπ.
  Lemma sub_aux : seal (@sub_def). Proof. by eexists. Qed.
  Definition sub {Xl Yl} := sub_aux.(unseal) Xl Yl.
  Lemma sub_unseal : @sub = @sub_def. Proof. exact: seal_eq. Qed.
  (** [sub] is persistent *)
  #[export] Instance sub_persistent {Xl Yl κ Γi Γo pre} :
    Persistent (@sub Xl Yl κ Γi Γo pre).
  Proof. rewrite sub_unseal. exact _. Qed.

  (** [type]: Expression typing, ensuring termination *)
  Definition type_def {Xl Yl} (κ : lft) (Γi : tcx CON Σ Xl) (e : expr)
    (Γo : val → tcx CON Σ Yl) (pre : xpred Yl → xpred Xl)
    : iProp Σ :=
    □ ∀ q t postπ xlπ,
      q.[κ] -∗ na_own t ⊤ -∗ ⟨π, pre (postπ π) (xlπ π)⟩ -∗ sem_tcx t Γi xlπ -∗
        WP[rust_halt_wsat] e [{ v, |=[rust_halt_wsat]{⊤}=> ∃ ylπ,
          q.[κ] ∗ na_own t ⊤ ∗ ⟨π, postπ π (ylπ π)⟩ ∗ sem_tcx t (Γo v) ylπ }].
  Lemma type_aux : seal (@type_def). Proof. by eexists. Qed.
  Definition type {Xl Yl} := type_aux.(unseal) Xl Yl.
  Lemma type_unseal : @type = @type_def. Proof. exact: seal_eq. Qed.
  (** [type] is persistent *)
  #[export] Instance type_persistent {Xl Yl κ Γi e Γo pre} :
    Persistent (@type Xl Yl κ Γi e Γo pre).
  Proof. rewrite type_unseal. exact _. Qed.

  Context `{!rust_haltC CON, !rust_haltJ CON JUDG Σ, !rust_haltCS CON JUDG Σ}.

  (** [sub] is reflexive and transitive *)
  Lemma sub_refl {Xl κ Γ} : ⊢ @sub Xl _ κ Γ Γ id.
  Proof. rewrite sub_unseal. iIntros (????) "!>/= $ $ ? $ //". Qed.
  Lemma sub_trans {Xl Yl Zl κ Γi Γm Γo pre pre'} :
    @sub Xl Yl κ Γi Γm pre -∗ @sub _ Zl κ Γm Γo pre' -∗
      sub κ Γi Γo (pre ∘ pre').
  Proof.
    rewrite sub_unseal. iIntros "#sub #sub' !>" (????) "κ t pre Γi".
    iMod ("sub" with "κ t pre Γi") as (?) "(κ & t & pre & Γm)".
    iApply ("sub'" with "κ t pre Γm").
  Qed.

  (** Modify the input type context of [type] *)
  Lemma type_in {Xl' Xl Yl κ Γi' Γi e Γo prei pre} :
    @sub Xl' _ κ Γi' Γi prei -∗ @type Xl Yl κ Γi e Γo pre -∗
      type κ Γi' e Γo (prei ∘ pre).
  Proof.
    rewrite sub_unseal type_unseal.
    iIntros "#sub #type !>" (????) "/= κ t pre Γi'".
    iMod ("sub" with "κ t pre Γi'") as (?) "(κ & t & pre & Γi)".
    iApply ("type" with "κ t pre Γi").
  Qed.
  (** Modify the output type context of [type] *)
  Lemma type_out {Xl Yl Yl' κ Γi e Γo Γo' pre preo} :
    @type Xl Yl κ Γi e Γo pre -∗ (∀ v, @sub Yl Yl' κ (Γo v) (Γo' v) preo) -∗
      type κ Γi e Γo' (pre ∘ preo).
  Proof.
    rewrite sub_unseal type_unseal.
    iIntros "#type #sub !>" (????) "/= κ t pre Γi".
    iDestruct ("type" with "κ t pre Γi") as "twp". iApply (twp_wand with "twp").
    iIntros (?) ">(% & κ & t & pre & Γo)". iApply ("sub" with "κ t pre Γo").
  Qed.

  (** Modify the predicate transformer of [sub] *)
  Lemma sub_pre {Xl Yl κ Γi Γo pre pre'} :
    (∀ post xl, pre' post xl → pre post xl) →
    @sub Xl Yl κ Γi Γo pre ⊢ @sub Xl Yl κ Γi Γo pre'.
  Proof.
    rewrite sub_unseal=> to. iIntros "#sub !>" (????) "κ t #pre Γi".
    iApply ("sub" with "κ t [] Γi"). iApply (proph_obs_impl with "pre")=> ?.
    apply to.
  Qed.
  (** Modify the predicate transformer of [type] *)
  Lemma type_pre {Xl Yl κ Γi e Γo pre pre'} :
    (∀ post xl, pre' post xl → pre post xl) →
    @type Xl Yl κ Γi e Γo pre ⊢ @type Xl Yl κ Γi e Γo pre'.
  Proof.
    rewrite type_unseal=> to. iIntros "#type !>" (????) "κ t #pre Γi".
    iApply ("type" with "κ t [] Γi"). iApply (proph_obs_impl with "pre")=> ?.
    apply to.
  Qed.

  (** [sub] with an unsatisfiable predicate transformer *)
  Lemma sub_false {Xl Yl κ Γi Γo pre} :
    (∀ post xl, ¬ pre post xl) → ⊢ @sub Xl Yl κ Γi Γo pre.
  Proof.
    rewrite sub_unseal=> ?. iIntros (????) "!> _ _ ?".
    by rewrite proph_obs_false.
  Qed.
  (** [type] with an unsatisfiable predicate transformer *)
  Lemma type_false {Xl Yl κ Γi e Γo pre} :
    (∀ post xl, ¬ pre post xl) → ⊢ @type Xl Yl κ Γi e Γo pre.
  Proof.
    rewrite type_unseal=> ?. iIntros (????) "!> _ _ ?".
    by rewrite proph_obs_false.
  Qed.

  (** Modify the lifetime of [sub] *)
  Lemma sub_lft {Xl Yl κ κ' Γi Γo pre} :
    κ' ⊑□ κ -∗ @sub Xl Yl κ Γi Γo pre -∗ sub κ' Γi Γo pre.
  Proof.
    rewrite sub_unseal. iIntros "#⊑ #ty !>" (????) "κ' t pre Γi".
    iMod (lft_sincl_live_acc with "⊑ κ'") as (?) "[κ →κ']".
    iMod ("ty" with "κ t pre Γi") as (?) "[κ $]". iModIntro. by iApply "→κ'".
  Qed.
  (** Modify the lifetime of [type] *)
  Lemma type_lft {Xl Yl κ κ' Γi e Γo pre} :
    κ' ⊑□ κ -∗ @type Xl Yl κ Γi e Γo pre -∗ @type Xl Yl κ' Γi e Γo pre.
  Proof.
    rewrite type_unseal. iIntros "#⊑ #type !>" (????) "κ' t pre Γi".
    iMod (lft_sincl_live_acc with "⊑ κ'") as (?) "[κ →κ']".
    iDestruct ("type" with "κ t pre Γi") as "twp". iApply (twp_wand with "twp").
    iIntros (?) ">(% & κ & $) !>". by iApply "→κ'".
  Qed.

  (** Frame the head in [sub] *)
  Lemma sub_frame_hd {X Yl Zl κ E Γi Γo pre} :
    @sub Yl Zl κ Γi Γo pre ⊢ @sub (X :: _) _ κ (E ᵖ:: Γi) (E ᵖ:: Γo)
      (λ post '(x, yl)', pre (λ zl, post (x, zl)') yl).
  Proof.
    rewrite sub_unseal. iIntros "#sub !>" (????) "/= κ t pre [E Γi]".
    by iMod ("sub" with "κ t pre Γi") as (?) "($ & $ & $ & $)".
  Qed.
  (** Frame the head in [type] *)
  Lemma type_frame_hd {X Yl Zl κ E Γi e Γo pre} :
    @type Yl Zl κ Γi e Γo pre ⊢
      @type (X :: _) _ κ (E ᵖ:: Γi) e (λ v, E ᵖ:: Γo v)
        (λ post '(x, yl)', pre (λ zl, post (x, zl)') yl).
  Proof.
    rewrite type_unseal. iIntros "#type !>" (????) "/= κ t pre [E Γi]".
    iDestruct ("type" with "κ t pre Γi") as "twp". iApply (twp_wand with "twp").
    by iIntros (?) ">(% & $ & $ & $ & $) !>".
  Qed.

  (** [sub] is monotone *)
  #[export] Instance sub_mono {Xl Yl} :
    Proper ((⊑) --> (=) ==> (=) ==>
      pointwise_relation _ (pointwise_relation _ (flip impl)) ==> (⊢))
      (@sub Xl Yl).
  Proof.
    move=>/= ?????<-??<-?? to. rewrite sub_pre; [|exact to].
    iApply sub_lft. by iApply lft_incl_sincl.
  Qed.
  #[export] Instance sub_flip_mono {Xl Yl} :
    Proper ((⊑) ==> (=) ==> (=) ==>
      pointwise_relation _ (pointwise_relation _ impl) ==> flip (⊢))
      (@sub Xl Yl).
  Proof. solve_proper. Qed.
  #[export] Instance sub_proper {Xl Yl κ Γi Γo} :
    Proper (pointwise_relation _ (pointwise_relation _ (↔)) ==> (⊣⊢))
      (@sub Xl Yl κ Γi Γo).
  Proof.
    move=> ?? to. apply bi.equiv_entails.
    split; apply sub_mono=>//= ???; by apply to.
  Qed.

  (** [type] is monotone *)
  #[export] Instance type_mono {Xl Yl} :
    Proper ((⊑) --> (=) ==> (=) ==> (=) ==>
      pointwise_relation _ (pointwise_relation _ (flip impl)) ==> (⊢))
      (@type Xl Yl).
  Proof.
    move=>/= ?????<-??<-??<-?? to. rewrite type_pre; [|exact to].
    iApply type_lft. by iApply lft_incl_sincl.
  Qed.
  #[export] Instance type_flip_mono {Xl Yl} :
    Proper ((⊑) ==> (=) ==> (=) ==> (=) ==>
      pointwise_relation _ (pointwise_relation _ impl) ==> flip (⊢))
      (@type Xl Yl).
  Proof. solve_proper. Qed.
  #[export] Instance type_proper {Xl Yl κ Γi e Γo} :
    Proper (pointwise_relation _ (pointwise_relation _ (↔)) ==> (⊣⊢))
      (@type Xl Yl κ Γi e Γo).
  Proof.
    move=> ?? to. apply bi.equiv_entails.
    split; apply type_mono=>//= ???; by apply to.
  Qed.
End type.
Arguments type {_ _ _ _ _ _ _ _} _ _ _%_E _ _.

(** ** Extraction from a type context *)

Section tcx_extract.
  Context `{!rust_haltGS CON Σ, !Csem CON JUDG Σ,
    !Jsem JUDG (iProp Σ)}.

  (** Extract a type context element *)
  Class EtcxExtract {X Yl Zl} (E : etcx CON Σ X) (Γ : tcx CON Σ Yl)
    (Γr : tcx CON Σ Zl) (get : xlist Yl → X) (getr : xlist Yl → xlist Zl)
    := ETCX_EXTRACT {
    etcx_extract : ∀ t ylπ, sem_tcx t Γ ylπ ⊢
      sem_etcx t E (λ π, get (ylπ π)) ∗ sem_tcx t Γr (λ π, getr (ylπ π))
  }.

  (** Extract from the head *)
  #[export] Instance etcx_extract_hd {X Yl E Γ} :
    @EtcxExtract X _ Yl E (E ᵖ:: Γ) Γ fst' snd' | 5.
  Proof. by split. Qed.
  (** Extract from the copyable head *)
  #[export] Instance etcx_extract_hd_copy {X Yl Γ p} `{!Copy T} :
    @EtcxExtract X (_ :: Yl) _ (p ◁ T) (p ◁ T ᵖ:: Γ) (p ◁ T ᵖ:: Γ)
      fst' (λ yyl, yyl) | 2.
  Proof. split=> ??. iIntros "[#T $]". iFrame "T". Qed.
  (** Extract from the tail *)
  #[export] Instance etcx_extract_tl {X Y Yl Zl E'}
    `(!EtcxExtract E Γ Γ' get getr) :
    @EtcxExtract X (Y :: Yl) (_ :: Zl) E (E' ᵖ:: Γ) (E' ᵖ:: Γ')
      (λ yyl, get yyl.2') (λ yyl, yyl.1' ᵖ:: getr yyl.2') | 10.
  Proof. split=>/= ??. rewrite etcx_extract. iIntros "[$ $]". Qed.

  (** Extract a type context *)
  Class TcxExtract {Xl Yl Zl} (Γ : tcx CON Σ Xl) (Γg : tcx CON Σ Yl)
    (Γr : tcx CON Σ Zl) (get : xlist Yl → xlist Xl) (getr : xlist Yl → xlist Zl)
    := TCX_EXTRACT {
    tcx_extract : ∀ t xlπ, sem_tcx t Γg xlπ ⊢
      sem_tcx t Γ (λ π, get (xlπ π)) ∗ sem_tcx t Γr (λ π, getr (xlπ π))
  }.

  (** Extract a nil *)
  #[export] Instance tcx_extract_nil {Xl Γ} :
    @TcxExtract _ Xl _ ᵖ[] Γ Γ (λ _, ()) (λ xl, xl) | 10.
  Proof. split=> ??. by iIntros "$". Qed.
  (** Extract a cons *)
  #[export] Instance tcx_extract_cons
    `{!@EtcxExtract X Yl Yl' E Γg Γm get getr,
      !@TcxExtract Xl _ Zl Γ Γm Γr get' getr'} :
    TcxExtract (E ᵖ:: Γ) Γg Γr
      (λ yl, get yl ᵖ:: get' (getr yl)) (λ yl, getr' (getr yl)) | 20.
  Proof. split=> ??. rewrite etcx_extract tcx_extract. iIntros "[$ $]". Qed.

  (** Type context inclusion by [EtcxExtract] *)
  Lemma sub_etcx_extract `{!@EtcxExtract X Yl Zl E Γ Γr get getr} {κ} :
    ⊢ sub κ Γ (E ᵖ:: Γr) (λ post yl, post (get yl, getr yl)').
  Proof.
    rewrite sub_unseal. iIntros (????) "!>/= $ $ ?? !>". rewrite etcx_extract.
    iExists (λ _, (_,_)'). iFrame.
  Qed.
  (** Type context inclusion by [TcxExtract] *)
  Lemma sub_tcx_extract `{!@TcxExtract Xl Yl Zl Γ Γg Γr get getr} {κ} :
    ⊢ sub κ Γg (Γ ᵖ++ Γr) (λ post yl, post (get yl ᵖ++ getr yl)).
  Proof.
    rewrite sub_unseal. iIntros (????) "!>/= $ $ pre Γ !>". iExists (λ _, _).
    iFrame "pre". by rewrite tcx_extract sem_tcx_app.
  Qed.
End tcx_extract.

(** ** Resolution over a type context *)

Section resol_tcx.
  Context `{!rust_haltGS CON Σ, !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ)}.

  (** [ResolTcx]: Resolution over a type context *)
  Class ResolTcx {Xl} (Γ : tcx CON Σ Xl) (κ : lft) (post : xpred Xl) : Prop :=
    RESOL_TCX {
    resol_tcx {t xlπ q} :
      q.[κ] -∗ na_own t ⊤ -∗ sem_tcx t Γ xlπ =[rust_halt_wsat]{⊤}=∗
        q.[κ] ∗ na_own t ⊤ ∗ ⟨π, post (xlπ π)⟩;
  }.

  (** [ResolTcx] over nil *)
  #[export] Instance resol_tcx_nil {κ} : ResolTcx ᵖ[] κ (λ _, True).
  Proof. split=> >. iIntros "$ $ _ !>". by iApply proph_obs_true. Qed.
  (** [ResolTcx] over cons *)
  #[export] Instance resol_tcx_cons_owned {X}
    `(!Resol T κ post, !@ResolTcx Yl Γ κ post') {p} :
    ResolTcx (Xl:=X::_) (p ◁ T ᵖ:: Γ) κ (λ '(x, yl)', post x ∧ post' yl).
  Proof.
    split=> > /=. iIntros "κ t [(% & % & % & T) Γ]".
    iMod (resol with "κ t T") as "(κ & t & post)".
    iMod (resol_tcx with "κ t Γ") as "($ & $ & post')". iModIntro.
    iCombine "post post'" as "$".
  Qed.
  Lemma resol_tcx_cons `(!@ResolTcx Yl Γ κ post) {X E} :
    ResolTcx (Xl:=X::_) (E ᵖ:: Γ) κ (λ '(_, yl)', post yl).
  Proof.
    split=> > /=. iIntros "κ t [_ Γ]". iApply (resol_tcx with "κ t Γ").
  Qed.
  #[export] Instance resol_tcx_cons_frozen `(!@ResolTcx Yl Γ κ post) {X p α T} :
    ResolTcx (Xl:=X::_) (p ◁[†α] T ᵖ:: Γ) κ (λ '(_, yl)', post yl).
  Proof. exact: resol_tcx_cons. Qed.
  #[export] Instance resol_tcx_cons_lft `(!@ResolTcx Yl Γ κ post) {α} :
    ResolTcx (^[α] ᵖ:: Γ) κ (λ '(_, yl)', post yl).
  Proof. exact: resol_tcx_cons. Qed.
End resol_tcx.
