(** * Type model *)

From nola.examples.rust_halt Require Export base.

Implicit Type (CON : cifcon) (Σ : gFunctors) (X : xty).

(** ** Type model *)

(** Ownership formula *)
Definition ownty CON Σ X : prost :=
  thread_id -pr> nat -pr> clair X -pr> list val -pr> cif CON Σ.
(** Sharing formula *)
Definition shrty CON Σ X : prost :=
  thread_id -pr> nat -pr> loc -pr> lft -pr> clair X -pr> cif CON Σ.
(** Type model *)
Definition ty CON Σ X : prost := (ownty CON Σ X * shrty CON Σ X)%type.

(** Simple type, with the sharing formula defined from the ownership formula *)
Definition sty := ownty.
Definition ty_sty `{!rust_haltGS CON Σ, !rust_haltC CON}
  {X} (T : ownty CON Σ X) : ty CON Σ X :=
  (T, λ t d l α xπ, ∃ vl, l ↦∗ˢ[α] vl ∗ T t d xπ vl)%cif.
(** Plain type, with the ownership formula ignoring the thread id, the depth,
  and the prophecy assignment *)
Definition pty CON Σ X := X -d> list val -d> cif CON Σ.
Definition sty_pty {CON Σ X} (T : pty CON Σ X) : sty CON Σ X :=
  λ _ _ xπ vl, (∃ x, ⌜∀ π, xπ π = x⌝ ∗ T x vl)%cif.
Definition ty_pty `{!rust_haltGS CON Σ, !rust_haltC CON} {X} (T : pty CON Σ X)
  : ty CON Σ X :=
  ty_sty (sty_pty T).

Section ty.
  Context `{!rust_haltGS CON Σ, !rust_haltC CON}.

  (** [ty_sty] is size-preserving *)
  #[export] Instance ty_sty_perserv {X} : Preserv (ty_sty (X:=X)).
  Proof.
    move=> ??? eq. unfold ty_sty. f_equiv=>// >. f_equiv=> ?. f_equiv.
    apply eq.
  Qed.
  (** [sty_pty] is size-preserving *)
  #[export] Instance sty_pty_perserv {X} : Preserv (@sty_pty CON Σ X).
  Proof. move=> ??? eq. unfold sty_pty=> >. f_equiv=> ?. f_equiv. apply eq. Qed.
  (** [ty_pty] is size-preserving *)
  #[export] Instance ty_pty_perserv {X} : Preserv (ty_pty (X:=X)).
  Proof. solve_proper. Qed.

  (** Simplify [proeq] over [ty] *)
  Lemma ty_proeq {X T U k} :
    T ≡[k]@{ty CON Σ X}≡ U ↔
      (∀ t d xπ vl, T.1 t d xπ vl ≡[k]≡ U.1 t d xπ vl) ∧
      (∀ t d l α xπ, T.2 t d l α xπ ≡[k]≡ U.2 t d l α xπ).
  Proof. done. Qed.
  (** Simplify [proeq_later] over [ty] *)
  Lemma ty_proeq_later {X T U k} :
    T ≡[<k]@{ty CON Σ X}≡ U ↔
      (∀ t d xπ vl, T.1 t d xπ vl ≡[<k]≡ U.1 t d xπ vl) ∧
      (∀ t d l α xπ, T.2 t d l α xπ ≡[<k]≡ U.2 t d l α xπ).
  Proof. by case k. Qed.
End ty.

(** ** Basic properties of a type *)

Section ty.
  Context `{!Csem CON JUDG Σ}.

  (** Basic properties of a type *)
  Class Ty {X} (T : ty CON Σ X) (sz : nat) : Prop := TY {
    (** The sharing predicate is persistent *)
    ty_shr_persistent {t d l α xπ δ} :: Persistent ⟦ T.2 t d l α xπ ⟧ᶜ(δ);
    (** The ownership predicate entails the size constraint *)
    ty_own_size {t d xπ vl δ} : ⟦ T.1 t d xπ vl ⟧ᶜ(δ) ⊢ ⌜length vl = sz⌝;
    (** The depth of the ownership and sharing predicates can be bumped up *)
    ty_own_depth {t d d' xπ vl δ} :
      d ≤ d' → ⟦ T.1 t d xπ vl ⟧ᶜ(δ) ⊢ ⟦ T.1 t d' xπ vl ⟧ᶜ(δ);
    ty_shr_depth {t d d' l α xπ δ} :
      d ≤ d' → ⟦ T.2 t d l α xπ ⟧ᶜ(δ) ⊢ ⟦ T.2 t d' l α xπ ⟧ᶜ(δ);
    (** The ownership and sharing predicates are proper over the clairvoyant
      value *)
    ty_own_clair {t d xπ xπ' vl δ} :
      (∀ π, xπ π = xπ' π) → ⟦ T.1 t d xπ vl ⟧ᶜ(δ) ⊢ ⟦ T.1 t d xπ' vl ⟧ᶜ(δ);
    ty_shr_clair {t d l α xπ xπ' δ} :
      (∀ π, xπ π = xπ' π) → ⟦ T.2 t d l α xπ ⟧ᶜ(δ) ⊢ ⟦ T.2 t d l α xπ' ⟧ᶜ(δ);
  }.

  (** Basic properties of a simple type *)
  Class Sty {X} (T : sty CON Σ X) (sz : nat) : Prop := STY {
    (** The ownership predicate is persistent *)
    sty_persistent {t d xπ vl δ} :: Persistent ⟦ T t d xπ vl ⟧ᶜ(δ);
    (** The ownership predicate entails the size constraint *)
    sty_size {t d xπ vl δ} : ⟦ T t d xπ vl ⟧ᶜ(δ) ⊢ ⌜length vl = sz⌝;
    (** The depth of the ownership predicate can be bumped up *)
    sty_depth {t d d' xπ vl δ} :
      d ≤ d' → ⟦ T t d xπ vl ⟧ᶜ(δ) ⊢ ⟦ T t d' xπ vl ⟧ᶜ(δ);
    (** The ownership predicates is proper over the clairvoyant value *)
    sty_clair {t d xπ xπ' vl δ} :
      (∀ π, xπ π = xπ' π) → ⟦ T t d xπ vl ⟧ᶜ(δ) ⊢ ⟦ T t d xπ' vl ⟧ᶜ(δ);
  }.

  (** Basic properties of a plain type *)
  Class Pty {X} (T : pty CON Σ X) (sz : nat) : Prop := PTY {
    (** The ownership predicate is persistent *)
    pty_persistent {x vl δ} :: Persistent ⟦ T x vl ⟧ᶜ(δ);
    (** The ownership predicate entails the size constraint *)
    pty_size {x vl δ} : ⟦ T x vl ⟧ᶜ(δ) ⊢ ⌜length vl = sz⌝;
  }.

  (** [Ty], [Sty], [Pty] are proper *)
  #[export] Instance Ty_proper {X} : Proper ((≡) ==> (=) ==> (↔)) (@Ty X).
  Proof.
    have pro : Proper ((≡) ==> (=) ==> (→)) (@Ty X); last first.
    { move=> ?*?? <-. split; by apply pro. }
    move=> [??][??][/=eqvO eqvS]??<-[/=?? depO depS claO claS]. split=>/= >.
    { by rewrite -(eqvS _ _ _ _ _). } { by rewrite -(eqvO _ _ _ _). }
    { rewrite -!(eqvO _ _ _ _). apply depO. }
    { rewrite -!(eqvS _ _ _ _ _). apply depS. }
    { rewrite -!(eqvO _ _ _ _). apply claO. }
    { rewrite -!(eqvS _ _ _ _ _). apply claS. }
  Qed.
  #[export] Instance Sty_proper {X} : Proper ((≡) ==> (=) ==> (↔)) (@Sty X).
  Proof.
    have pro : Proper ((≡) ==> (=) ==> (→)) (@Sty X); last first.
    { move=> ?*??<-. split; by apply pro. }
    move=> ?? eqv ??<-[?? dep cla].
    split=> >; rewrite -!(eqv _ _ _ _) //; [apply dep|apply cla].
  Qed.
  #[export] Instance Pty_proper {X} : Proper ((≡) ==> (=) ==> (↔)) (@Pty X).
  Proof.
    have pro : Proper ((≡) ==> (=) ==> (→)) (@Pty X); last first.
    { move=> ?*??<-. split; by apply pro. }
    move=> ?? eqv ??<-[??]. split=> >; by rewrite -(eqv _ _).
  Qed.

  Context `{!rust_haltGS CON Σ, !rust_haltC CON, !rust_haltJ CON JUDG Σ,
    !rust_haltCS CON JUDG Σ}.

  (** [Sty] entails [Ty] *)
  #[export] Instance Ty_Sty `{!@Sty X T sz} : Ty (ty_sty T) sz.
  Proof.
    split=>/= >. { exact _. } { exact sty_size. } { exact sty_depth. }
    { move=> ?. do 3 f_equiv. by apply sty_depth. } { exact sty_clair. }
    { move=> ?. do 3 f_equiv. by apply sty_clair. }
  Qed.

  (** [Pty] entails [Sty] *)
  #[export] Instance Sty_Pty `{!@Pty X T sz} : Sty (sty_pty T) sz.
  Proof.
    split=> > /=; [exact _| |done|].
    - iIntros "[%[% ?]]". iStopProof. exact pty_size.
    - move=> eq. f_equiv=> ?. do 2 f_equiv. move=> ??. by rewrite -eq.
  Qed.
End ty.
Hint Mode Ty - - - - - ! - : typeclass_instances.
Hint Mode Sty - - - - - ! - : typeclass_instances.
Hint Mode Pty - - - - - ! - : typeclass_instances.

(** ** Basic operations on a type *)

Section ty_op.
  Context `{!rust_haltGS CON Σ, !rust_haltJ CON JUDG Σ, !Csem CON JUDG Σ,
    !Jsem JUDG (iProp Σ)}.

  (** [TyOpAt]: Basic operations on a type at a depth *)
  Class TyOpAt {X} (T : ty CON Σ X) (α : lft) (d : nat) : Prop := TY_OP_AT {
    (** Take out prophecy tokens from ownership and sharing formulas *)
    ty_own_proph {t xπ vl q} :
      q.[α] -∗ ⟦ T.1 t d xπ vl ⟧ᶜ =[rust_halt_wsat]{⊤}=∗ ∃ ξl r,
        ⌜proph_dep xπ ξl⌝ ∗ r:∗[ξl] ∗
        (r:∗[ξl] =[rust_halt_wsat]{⊤}=∗ q.[α] ∗ ⟦ T.1 t d xπ vl ⟧ᶜ);
    ty_shr_proph {t l β xπ q} :
      q.[α ⊓ β] -∗ ⟦ T.2 t d l β xπ ⟧ᶜ =[rust_halt_wsat]{⊤}=∗ ∃ ξl r,
        ⌜proph_dep xπ ξl⌝ ∗ r:∗[ξl] ∗
        (r:∗[ξl] =[rust_halt_wsat]{⊤}=∗ q.[α ⊓ β] ∗ ⟦ T.2 t d l β xπ ⟧ᶜ);
    (** A borrow over the ownership formula can turn into the sharing formula *)
    ty_share {t l β xπ q} :
      q.[α ⊓ β] -∗ bord β (∃ vl, ▷ l ↦∗ vl ∗ T.1 t d xπ vl)%cif
        =[rust_halt_wsat]{⊤}=∗ q.[α ⊓ β] ∗ ⟦ T.2 t d l β xπ ⟧ᶜ;
  }.

  (** [TyOpAt] is monotone *)
  #[export] Instance TyOpAt_mono {X} :
    Proper ((≡) ==> (⊑) --> (=) ==> (→)) (@TyOpAt X).
  Proof.
    move=> T T' [eqvO eqvS] α α' /= inc ?? <- ?. split.
    - move=> >. setoid_rewrite <-(eqvO _ _ _ _). iIntros "α' T".
      iDestruct (lft_incl_live_acc with "α'") as (?) "[α →α']"; [done|].
      iMod (ty_own_proph with "α T") as (??) "($ & $ & →T)". iModIntro.
      iIntros "ξl". iMod ("→T" with "ξl") as "[α $]". iModIntro.
      by iApply "→α'".
    - move=> ?? β ??. setoid_rewrite <-(eqvS _ _ _ _ _). iIntros "αβ' T".
      iDestruct (lft_incl_live_acc (β:=α ⊓ β) with "αβ'") as (?) "[αβ →αβ']".
      { apply lft_incl_meet_intro; [|exact lft_incl_meet_r].
        by etrans; [exact lft_incl_meet_l|]. }
      iMod (ty_shr_proph with "αβ T") as (??) "($ & $ & →T)". iModIntro.
      iIntros "ξl". iMod ("→T" with "ξl") as "[β $]". iModIntro.
      by iApply "→αβ'".
    - move=> ?? β ??. rewrite -(eqvS _ _ _ _ _). iIntros "αβ' b".
      iDestruct (lft_incl_live_acc (β:=α ⊓ β) with "αβ'") as (?) "[αβ →αβ']".
      { apply lft_incl_meet_intro; [|exact lft_incl_meet_r].
        by etrans; [exact lft_incl_meet_l|]. }
      iMod (ty_share with "αβ [b]") as "[αβ $]"; last first.
      { iModIntro. by iApply "→αβ'". }
      iStopProof. apply bi.equiv_entails. (do 2 f_equiv)=> ?.
      by rewrite (eqvO _ _ _ _).
  Qed.
  #[export] Instance TyOpAt_flip_mono {X} :
    Proper ((≡) ==> (⊑) ==> (=) ==> flip (→)) (@TyOpAt X).
  Proof. move=> ?*?*??<- /=. by apply TyOpAt_mono. Qed.
  #[export] Instance TyOpAt_proper {X} :
    Proper ((≡) ==> (=) --> (=) ==> (↔)) (@TyOpAt X).
  Proof. move=> ?*??<-??<-. split; by apply TyOpAt_mono. Qed.

  (** [TyOpLt]: Basic operations on a type below a depth *)
  Class TyOpLt {X} (T : ty CON Σ X) (α : lft) (d : nat) : Prop :=
    ty_op_lt : ∀ {d'}, d' < d → TyOpAt T α d'.

  (** [TyOpLt] is monotone *)
  #[export] Instance TyOpLt_mono {X} :
    Proper ((≡) ==> (⊑) --> (≤) --> (→)) (@TyOpLt X).
  Proof.
    move=> ?*?* d d' /= ? wl d'' ?. have lt : d'' < d by lia. move: (wl _ lt).
    by apply TyOpAt_mono.
  Qed.
  #[export] Instance TyOpLt_flip_mono {X} :
    Proper ((≡) ==> (⊑) ==> (≤) ==> flip (→)) (@TyOpLt X).
  Proof. move=> ?*?*?* /=. by apply TyOpLt_mono. Qed.
  #[export] Instance TyOpLt_proper {X} :
    Proper ((≡) ==> (=) --> (=) ==> (↔)) (@TyOpLt X).
  Proof. move=> ?*?? <- ?? <-. split; by apply TyOpLt_mono. Qed.

  (** Lemmas under [TyOpLt] *)
  Section ty_op_lt.
    Context `(!@TyOpLt X T α d0).
    Lemma ty_own_proph_lt {t d xπ vl q} : d < d0 →
      q.[α] -∗ ⟦ T.1 t d xπ vl ⟧ᶜ =[rust_halt_wsat]{⊤}=∗ ∃ ξl r,
        ⌜proph_dep xπ ξl⌝ ∗ r:∗[ξl] ∗
        (r:∗[ξl] =[rust_halt_wsat]{⊤}=∗ q.[α] ∗ ⟦ T.1 t d xπ vl ⟧ᶜ).
    Proof. move=> ?. by apply ty_op_lt. Qed.
    Lemma ty_shr_proph_lt {t d l β xπ q} : d < d0 →
      q.[α ⊓ β] -∗ ⟦ T.2 t d l β xπ ⟧ᶜ =[rust_halt_wsat]{⊤}=∗ ∃ ξl r,
        ⌜proph_dep xπ ξl⌝ ∗ r:∗[ξl] ∗
        (r:∗[ξl] =[rust_halt_wsat]{⊤}=∗ q.[α ⊓ β] ∗ ⟦ T.2 t d l β xπ ⟧ᶜ).
    Proof. move=> ?. by apply ty_op_lt. Qed.
    Lemma ty_share_lt {t d l β xπ q} : d < d0 →
      q.[α ⊓ β] -∗ bord β (∃ vl, ▷ l ↦∗ vl ∗ T.1 t d xπ vl)%cif
        =[rust_halt_wsat]{⊤}=∗ q.[α ⊓ β] ∗ ⟦ T.2 t d l β xπ ⟧ᶜ.
    Proof. move=> ?. by apply ty_op_lt. Qed.
  End ty_op_lt.

  Context `{!rust_haltC CON, !rust_haltCS CON JUDG Σ, !rust_haltJS CON JUDG Σ}.

  (** Basic operations on a simple type at a depth *)
  Lemma sty_op_at `{!Sty (X:=X) T sz} {d} α :
    (∀ t xπ vl q,
      q.[α] -∗ ⟦ T t d xπ vl ⟧ᶜ =[rust_halt_wsat]{⊤}=∗ ∃ ξl r,
        ⌜proph_dep xπ ξl⌝ ∗ r:∗[ξl] ∗
        (r:∗[ξl] =[rust_halt_wsat]{⊤}=∗ q.[α] ∗ ⟦ T t d xπ vl ⟧ᶜ)) →
    TyOpAt (ty_sty T) α d.
  Proof.
    move=> sty_proph. split=>/= >; [done| |].
    - iIntros "[α $] (%vl & ↦ & T)".
      iMod (sty_proph with "α T") as (??) "($ & $ & cl)". iIntros "!> ξl".
      iFrame "↦". by iApply "cl".
    - iIntros "[$ β] b".
      iMod (bord_open (M:=borrowM) with "β b") as "/=[o (% & >↦ & #T)]".
      iFrame "T".
      iMod (obord_subdiv (FML:=cifOF _) (M:=borrowM) [▷ _]%cif
        with "[] o [$↦ //] []") as "(β & _ & [b _])"=>/=.
      { iApply lft_sincl_refl. } { by iIntros "_ [$ _]". }
      rewrite sem_cif_spointsto_vec.
      by iMod (spointsto_vec_alloc with "β b") as "$".
  Qed.

  (** Basic operations on a plain type at a depth *)
  #[export] Instance pty_op_at `{!Pty (X:=X) T sz} {α d} :
    TyOpAt (ty_pty T) α d.
  Proof.
    apply sty_op_at=>/= ????. iIntros "$ (% & % & ?) !>". iExists [], 1%Qp.
    iSplit. { iPureIntro. by apply: proph_dep_const. }
    iSplit=>//. iIntros "_ !>". iExists _. by iSplit.
  Qed.
End ty_op.
Hint Mode TyOpAt - - - - - - - - ! - - : typeclass_instances.
Hint Mode TyOpLt - - - - - - - - ! - - : typeclass_instances.

(** [TyOpAt]: Basic operations on a type *)
Notation TyOp T α := (∀ d, TyOpAt T α d).

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
    send : ∀ {t t'}, T.1 t ≡ T.1 t'.
  (** [Send] is proper *)
  #[export] Instance Send_proper {X} : Proper ((≡) ==> (↔)) (@Send X).
  Proof.
    move=> ??[eqv _]. apply forall_proper=> t. apply forall_proper=> t'.
    by rewrite (eqv t) (eqv t').
  Qed.

  (** [Sync]: the sharing formula does not depend on the thread id *)
  Class Sync {X} (T : ty CON Σ X) : Prop :=
    sync : ∀ {t t'}, T.2 t ≡ T.2 t'.
  (** [Sync] is proper *)
  #[export] Instance Sync_proper {X} : Proper ((≡) ==> (↔)) (@Sync X).
  Proof.
    move=> ??[_ eqv]. apply forall_proper=> t. apply forall_proper=> t'.
    by rewrite (eqv t) (eqv t').
  Qed.

  Context `{!rust_haltGS CON Σ, !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ)}.

  (** [Copy] *)
  Class Copy {X} (T : ty CON Σ X) sz : Prop := COPY {
    (** Persistence of the ownership formula *)
    copy_persistent {t d xπ vl δ} :: Persistent ⟦ T.1 t d xπ vl ⟧ᶜ(δ);
    (** Access via the sharing formula *)
    copy_shr_acc {t d l α xπ q F} : shr_locsE l (S sz) ⊆ F →
      q.[α] -∗ na_own t F -∗ ⟦ T.2 t d l α xπ ⟧ᶜ =[rust_halt_wsat]{⊤}=∗ ∃ r vl,
        l ↦∗{r} vl ∗ na_own t (F ∖ shr_locsE l sz) ∗ ⟦ T.1 t d xπ vl ⟧ᶜ ∗
        (l ↦∗{r} vl -∗ na_own t (F ∖ shr_locsE l sz) =[rust_halt_wsat]{⊤}=∗
          q.[α] ∗ na_own t F);
  }.
  (** [Copy] is proper *)
  #[export] Instance Copy_proper {X} : Proper ((≡) ==> (=) ==> (↔)) (@Copy X).
  Proof.
    have pro: Proper ((≡) ==> (=) ==> (→)) (@Copy X); last first.
    { move=> ???. split; by apply pro. }
    move=> ??[eqvO eqvS]??<-. split=> *; [rewrite -(eqvO _ _ _ _); exact _|].
    rewrite -(eqvS _ _ _ _ _). setoid_rewrite <-(eqvO _ _ _ _).
    by apply copy_shr_acc.
  Qed.

  Context `{!rust_haltC CON, !rust_haltJ CON JUDG Σ, !rust_haltCS CON JUDG Σ}.

  (** [Send] over [sty] entails [Sync] *)
  #[export] Instance sty_send_sync `{!Send (ty_sty (X:=X) T)} :
    Sync (ty_sty (X:=X) T).
  Proof. move=> > /=. f_equiv=> ?. f_equiv. apply: Send0. Qed.

  (** [pty] is [Send] and [Sync] *)
  #[export] Instance pty_send {X T} : Send (ty_pty (X:=X) T).
  Proof. by move. Qed.
  #[export] Instance pty_sync {X T} : Sync (ty_pty (X:=X) T).
  Proof. exact _. Qed.

  (** [sty] is [Copy] *)
  #[export] Instance sty_copy `{!Sty (X:=X) T sz} : Copy (ty_sty (X:=X) T) sz.
  Proof.
    split; [exact _|]=>/= ????????. iIntros "α F (% & ↦ & $)".
    rewrite sem_cif_spointsto_vec.
    iMod (spointsto_vec_acc with "α ↦") as (?) "[$ cl]".
    iDestruct (na_own_acc with "F") as "[$ →F]"; [set_solver|].
    iIntros "!> ↦s F∖". iMod ("cl" with "↦s") as "$". iModIntro. by iApply "→F".
  Qed.
End classes.
Hint Mode Send - - - ! : typeclass_instances.
Hint Mode Sync - - - ! : typeclass_instances.
Hint Mode Copy - - - - - - - ! - : typeclass_instances.

(** ** Subtyping *)

Section subty.
  Context `{!rust_haltGS CON Σ, !Csem CON JUDG Σ}.
  Implicit Type δ : JUDG -n> iProp Σ.

  (** [subty]: Subtyping *)
  Definition subty_def δ {X Y} (T : ty CON Σ X) (U : ty CON Σ Y) (f : X → Y)
    : iProp Σ :=
    (* Ownership formula conversion *) □ (∀ t d xπ vl,
      ⟦ T.1 t d xπ vl ⟧ᶜ(δ) -∗ ⟦ U.1 t d (λ π, f (xπ π)) vl ⟧ᶜ(δ)) ∧
    (* Sharing formula conversion *) □ (∀ t d l α xπ,
      ⟦ T.2 t d l α xπ ⟧ᶜ(δ) -∗ ⟦ U.2 t d l α (λ π, f (xπ π)) ⟧ᶜ(δ)).
  Lemma subty_aux : @subty_def.(seal). Proof. by eexists _. Qed.
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
    rewrite subty_unseal /subty_def=> ??[eqvO eqvS]??[eqvO' eqvS']??<-.
    repeat f_equiv; [exact (eqvO _ _ _ _)|exact (eqvO' _ _ _ _)|
      exact (eqvS _ _ _ _ _)|exact (eqvS' _ _ _ _ _)].
  Qed.
  (** [subty] is reflexive *)
  Lemma subty_refl {δ X T} : ⊢ @subty δ X _ T T id.
  Proof. rewrite subty_unseal. iSplit; iModIntro; iIntros; iFrame. Qed.
  (** [subty] is transitive *)
  Lemma subty_trans {δ X Y Z T U V f g} :
    @subty δ X Y T U f -∗ @subty δ _ Z U V g -∗ @subty δ X Z T V (g ∘ f).
  Proof.
    rewrite subty_unseal. iIntros "[#TUo #TUs][#UVo #UVs]". iSplit; iModIntro.
    - iIntros (????) "T". iApply "UVo". by iApply "TUo".
    - iIntros (?????) "T". iApply "UVs". by iApply "TUs".
  Qed.

  Context `{!rust_haltC CON, !rust_haltJ CON JUDG Σ, !rust_haltCS CON JUDG Σ}.

  (** [subty] over [sty] *)
  Lemma subty_sty {δ X Y f} T U :
    □ (∀ t d xπ vl, ⟦ T t d xπ vl ⟧ᶜ(δ) -∗ ⟦ U t d (λ π, f (xπ π)) vl ⟧ᶜ(δ)) ⊢
      @subty δ X Y (ty_sty T) (ty_sty U) f.
  Proof.
    rewrite subty_unseal. iIntros "#sub". iSplit; [done|]=>/=.
    iIntros (?????) "!> (% & $ & ?)". by iApply "sub".
  Qed.
  (** [subty] over [pty] *)
  Lemma subty_pty {δ X Y f} T U :
    □ (∀ x vl, ⟦ T x vl ⟧ᶜ(δ) -∗ ⟦ U (f x) vl ⟧ᶜ(δ)) ⊢
      @subty δ X Y (ty_pty T) (ty_pty U) f.
  Proof.
    iIntros "#sub". iApply subty_sty=>/=. iIntros (????) "!> (% & %eq & ?)".
    iExists _. iSplit; [|by iApply "sub"]. iPureIntro=> ?. by rewrite eq.
  Qed.
End subty.

Notation subtyd := (subty der).

(** ** Type context *)

(** Type context element *)
Variant etcx CON Σ : xty → Type :=
| Owned {X} (v : val) (T : ty CON Σ X) : etcx CON Σ X
| Frozen {X} (α : lft) (v : val) (T : ty CON Σ X) : etcx CON Σ X
| Lft (α : lft) : etcx CON Σ unitₓ.
Arguments Owned {_ _ _}. Arguments Frozen {_ _ _}. Arguments Lft {_ _}.
Infix "◁" := Owned (at level 55).
Notation "v ◁[† α ] T" := (Frozen α v T) (at level 55, format "v  ◁[† α ]  T").
Notation "^[ α ]" := (Lft α) (format "^[ α ]").

(** Type context *)
Notation tcx CON Σ := (plist (etcx CON Σ)).

Section tcx.
  Context `{!rust_haltGS CON Σ, !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ)}.

  (** Semantics of a type context element *)
  Definition sem_etcx {X} t (E : etcx CON Σ X) : clair X → iProp Σ :=
    match E with
    | v ◁ T => λ xπ, ∃ d, ⟦ T.1 t d xπ [v] ⟧ᶜ
    | v ◁[†α] T => λ xπ, [†α] =[rust_halt_wsat]{⊤}=∗
        ∃ d xπ', proph_eqz xπ xπ' ∗ ⟦ T.1 t d xπ' [v] ⟧ᶜ
    | ^[α] => λ _, ⌜α ≠ ⊤⌝ ∧ 1.[α]
    end%I.

  (** Semantics of a type context *)
  Fixpoint sem_tcx t {Xl} : tcx CON Σ Xl → clair (xlist Xl) → iProp Σ :=
    match Xl with [] => λ _ _, True | _ :: _ => λ '(eΓ, Γ)' xlπ,
      sem_etcx t eΓ (λ π, (xlπ π).1') ∗ sem_tcx t Γ (λ π, (xlπ π).2') end%I.

  (** [sem_tcx] over [plist_app] *)
  Lemma sem_tcx_app {t Xl Yl Γ Γ' xlπ ylπ} :
    @sem_tcx t Xl Γ xlπ ∗ @sem_tcx t Yl Γ' ylπ ⊣⊢
      sem_tcx t (plist_app Γ Γ') (λ π, plist_app (xlπ π) (ylπ π)).
  Proof.
    move: Γ xlπ. elim: Xl=>/=. { move=> ??. by rewrite left_id. }
    move=> ?? IH ??. by rewrite -IH assoc.
  Qed.
End tcx.

(** ** Type context inclusion and expression typing *)
Section type.
  Context `{!rust_haltGS CON Σ, !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ)}.

  (** [sub]: Inclusion between type contexts *)
  Definition sub_def {Xl Yl} (α : lft) (Γi : tcx CON Σ Xl) (Γo : tcx CON Σ Yl)
    (pre : xpred Yl → xpred Xl) : iProp Σ :=
    □ ∀ q t postπ xlπ,
      q.[α] -∗ na_own t ⊤ -∗ ⟨π, pre (postπ π) (xlπ π)⟩ -∗ sem_tcx t Γi xlπ
        =[rust_halt_wsat]{⊤}=∗ ∃ ylπ,
        q.[α] ∗ na_own t ⊤ ∗ ⟨π, postπ π (ylπ π)⟩ ∗ sem_tcx t Γo ylπ.
  Lemma sub_aux : seal (@sub_def). Proof. by eexists. Qed.
  Definition sub {Xl Yl} := sub_aux.(unseal) Xl Yl.
  Lemma sub_unseal : @sub = @sub_def. Proof. exact: seal_eq. Qed.
  (** [sub] is persistent *)
  #[export] Instance sub_persistent {Xl Yl α Γi Γo pre} :
    Persistent (@sub Xl Yl α Γi Γo pre).
  Proof. rewrite sub_unseal. exact _. Qed.

  (** [type]: Expression typing, ensuring termination *)
  Definition type_def {Xl Yl} (α : lft) (Γi : tcx CON Σ Xl) (e : expr)
    (Γo : val → tcx CON Σ Yl) (pre : xpred Yl → xpred Xl)
    : iProp Σ :=
    □ ∀ q t postπ xlπ,
      q.[α] -∗ na_own t ⊤ -∗ ⟨π, pre (postπ π) (xlπ π)⟩ -∗ sem_tcx t Γi xlπ -∗
        WP[rust_halt_wsat] e [{ v, |=[rust_halt_wsat]{⊤}=> ∃ ylπ,
          q.[α] ∗ na_own t ⊤ ∗ ⟨π, postπ π (ylπ π)⟩ ∗ sem_tcx t (Γo v) ylπ }].
  Lemma type_aux : seal (@type_def). Proof. by eexists. Qed.
  Definition type {Xl Yl} := type_aux.(unseal) Xl Yl.
  Lemma type_unseal : @type = @type_def. Proof. exact: seal_eq. Qed.
  (** [type] is persistent *)
  #[export] Instance type_persistent {Xl Yl α Γi e Γo pre} :
    Persistent (@type Xl Yl α Γi e Γo pre).
  Proof. rewrite type_unseal. exact _. Qed.

  Context `{!rust_haltC CON, !rust_haltJ CON JUDG Σ, !rust_haltCS CON JUDG Σ}.

  (** [sub] is reflexive and transitive *)
  Lemma sub_refl {Xl α Γ} : ⊢ @sub Xl _ α Γ Γ id.
  Proof. rewrite sub_unseal. iIntros (????) "!>/= $ $ ? $ //". Qed.
  Lemma sub_trans {Xl Yl Zl α Γ Γ' Γ'' pre pre'} :
    @sub Xl Yl α Γ Γ' pre -∗ @sub _ Zl α Γ' Γ'' pre' -∗
      sub α Γ Γ'' (pre ∘ pre').
  Proof.
    rewrite sub_unseal. iIntros "#sub #sub' !>" (????) "α t pre Γ".
    iMod ("sub" with "α t pre Γ") as (?) "(α & t & pre & Γ')".
    iApply ("sub'" with "α t pre Γ'").
  Qed.
  (** Modify the predicate transformer of [sub] *)
  Lemma sub_pre {Xl Yl α Γi Γo pre pre'} :
    (∀ post xl, pre' post xl → pre post xl) →
    @sub Xl Yl α Γi Γo pre ⊢ @sub Xl Yl α Γi Γo pre'.
  Proof.
    rewrite sub_unseal=> to. iIntros "#sub !>" (????) "α t #pre Γ".
    iApply ("sub" with "α t [] Γ"). iApply (proph_obs_impl with "pre")=> ?.
    apply to.
  Qed.
  (** [sub] with an unsatisfiable predicate transformer *)
  Lemma sub_false {Xl Yl α Γi Γo pre} :
    (∀ post xl, ¬ pre post xl) → ⊢ @sub Xl Yl α Γi Γo pre.
  Proof.
    rewrite sub_unseal=> ?. iIntros (????) "!> _ _ ?".
    by rewrite proph_obs_false.
  Qed.
  (** Modify the lifetime of [sub] *)
  Lemma sub_lft {Xl Yl α β Γi Γo pre} :
    β ⊑□ α -∗ @sub Xl Yl α Γi Γo pre -∗ sub β Γi Γo pre.
  Proof.
    rewrite sub_unseal. iIntros "#⊑ #ty !>" (????) "β t pre Γi".
    iMod (lft_sincl_live_acc with "⊑ β") as (?) "[α →β]".
    iMod ("ty" with "α t pre Γi") as (?) "[α $]". iModIntro. by iApply "→β".
  Qed.
  (** Frame the head in [sub] *)
  Lemma sub_frame_hd {X Yl Zl α E Γi Γo pre} :
    @sub Yl Zl α Γi Γo pre ⊢ @sub (X :: _) _ α (E ᵖ:: Γi) (E ᵖ:: Γo)
      (λ post '(x, yl)', pre (λ zl, post (x, zl)') yl).
  Proof.
    rewrite sub_unseal. iIntros "#sub !>" (????) "/= α t pre [E Γi]".
    by iMod ("sub" with "α t pre Γi") as (?) "($ & $ & $ & $)".
  Qed.
  (** [sub] is monotone *)
  #[export] Instance sub_mono {Xl Yl} :
    Proper ((⊑) --> (=) ==> (=) ==>
      pointwise_relation _ (pointwise_relation _ impl) --> (⊢)) (@sub Xl Yl).
  Proof.
    move=>/= ?????<-??<-?? impl. rewrite sub_pre; [|exact impl].
    iApply sub_lft. by iApply lft_incl_sincl.
  Qed.
  #[export] Instance sub_proper {Xl Yl α Γi Γo} :
    Proper (pointwise_relation _ (pointwise_relation _ (↔)) --> (⊣⊢))
      (@sub Xl Yl α Γi Γo).
  Proof.
    move=> ?? impl. apply bi.equiv_entails.
    split; apply sub_mono=>//= ???; by apply impl.
  Qed.

  (** Modify the input type context of [type] *)
  Lemma type_in {Xl' Xl Yl α Γi' Γi e Γo prei pre} :
    @sub Xl' _ α Γi' Γi prei -∗ @type Xl Yl α Γi e Γo pre -∗
      type α Γi' e Γo (prei ∘ pre).
  Proof.
    rewrite sub_unseal type_unseal.
    iIntros "#sub #type !>" (????) "/= α t pre Γi'".
    iMod ("sub" with "α t pre Γi'") as (?) "(α & t & pre & Γi)".
    iApply ("type" with "α t pre Γi").
  Qed.
  (** Modify the output type context of [type] *)
  Lemma type_out {Xl Yl Yl' α Γi e Γo Γo' pre preo} :
    @type Xl Yl α Γi e Γo pre -∗ (∀ v, @sub Yl Yl' α (Γo v) (Γo' v) preo) -∗
      type α Γi e Γo' (pre ∘ preo).
  Proof.
    rewrite sub_unseal type_unseal.
    iIntros "#type #sub !>" (????) "/= α t pre Γi".
    iDestruct ("type" with "α t pre Γi") as "twp". iApply (twp_wand with "twp").
    iIntros (?) ">(% & α & t & pre & Γo)". iApply ("sub" with "α t pre Γo").
  Qed.
  (** Modify the predicate transformer of [type] *)
  Lemma type_pre {Xl Yl α Γi e Γo pre pre'} :
    (∀ post xl, pre' post xl → pre post xl) →
    @type Xl Yl α Γi e Γo pre ⊢ @type Xl Yl α Γi e Γo pre'.
  Proof.
    rewrite type_unseal=> to. iIntros "#type !>" (????) "α t #pre Γi".
    iApply ("type" with "α t [] Γi"). iApply (proph_obs_impl with "pre")=> ?.
    apply to.
  Qed.
  (** [type] with an unsatisfiable predicate transformer *)
  Lemma type_false {Xl Yl α Γi e Γo pre} :
    (∀ post xl, ¬ pre post xl) → ⊢ @type Xl Yl α Γi e Γo pre.
  Proof.
    rewrite type_unseal=> ?. iIntros (????) "!> _ _ ?".
    by rewrite proph_obs_false.
  Qed.
  (** Modify the lifetime of [type] *)
  Lemma type_lft {Xl Yl α β Γi e Γo pre} :
    β ⊑□ α -∗ @type Xl Yl α Γi e Γo pre -∗ @type Xl Yl β Γi e Γo pre.
  Proof.
    rewrite type_unseal. iIntros "#⊑ #type !>" (????) "β t pre Γi".
    iMod (lft_sincl_live_acc with "⊑ β") as (?) "[α →β]".
    iDestruct ("type" with "α t pre Γi") as "twp". iApply (twp_wand with "twp").
    iIntros (?) ">(% & α & $) !>". by iApply "→β".
  Qed.
  (** Frame the head in [type] *)
  Lemma type_frame_hd {X Yl Zl α E Γi e Γo pre} :
    @type Yl Zl α Γi e Γo pre ⊢
      @type (X :: _) _ α (E ᵖ:: Γi) e (λ v, E ᵖ:: Γo v)
        (λ post '(x, yl)', pre (λ zl, post (x, zl)') yl).
  Proof.
    rewrite type_unseal. iIntros "#type !>" (????) "/= α t pre [E Γi]".
    iDestruct ("type" with "α t pre Γi") as "twp". iApply (twp_wand with "twp").
    by iIntros (?) ">(% & $ & $ & $ & $) !>".
  Qed.
  (** [type] is monotone *)
  #[export] Instance type_mono {Xl Yl} :
    Proper ((⊑) --> (=) ==> (=) ==> (=) ==>
      pointwise_relation _ (pointwise_relation _ impl) --> (⊢)) (@type Xl Yl).
  Proof.
    move=>/= ?????<-??<-??<-?? impl. rewrite type_pre; [|exact impl].
    iApply type_lft. by iApply lft_incl_sincl.
  Qed.
  #[export] Instance type_proper {Xl Yl α Γi e Γo} :
    Proper (pointwise_relation _ (pointwise_relation _ (↔)) --> (⊣⊢))
      (@type Xl Yl α Γi e Γo).
  Proof.
    move=> ?? impl. apply bi.equiv_entails.
    split; apply type_mono=>//= ???; by apply impl.
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
  #[export] Instance etcx_extract_hd_copy {X Yl Γ v} `{!Copy T sz} :
    @EtcxExtract X (_ :: Yl) _ (v ◁ T) (v ◁ T ᵖ:: Γ) (v ◁ T ᵖ:: Γ)
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
  Lemma sub_etcx_extract `{!@EtcxExtract X Yl Zl E Γ Γr get getr} {α} :
    ⊢ sub α Γ (E ᵖ:: Γr) (λ post yl, post (get yl, getr yl)').
  Proof.
    rewrite sub_unseal. iIntros (????) "!>/= $ $ ?? !>". rewrite etcx_extract.
    iExists (λ _, (_,_)'). iFrame.
  Qed.
  (** Type context inclusion by [TcxExtract] *)
  Lemma sub_tcx_extract `{!@TcxExtract Xl Yl Zl Γ Γg Γr get getr} {α} :
    ⊢ sub α Γg (plist_app Γ Γr)
      (λ post yl, post (plist_app (get yl) (getr yl))).
  Proof.
    rewrite sub_unseal. iIntros (????) "!>/= $ $ pre Γ !>". iExists (λ _, _).
    iFrame "pre". by rewrite tcx_extract sem_tcx_app.
  Qed.
End tcx_extract.
