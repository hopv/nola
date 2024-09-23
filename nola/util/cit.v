(** * [cit]: Coinductive-inductive set of trees *)

From nola.util Require Export eq order productive.
From iris.algebra Require Export ofe.
Import EqNotations FunPRNotation.

Implicit Type SEL : Type.

(** ** [citg]: Generator of [cit] *)

(** [citg]: Generator of [cit] *)
Section citg.
  Context {SEL} (I C : SEL → Type) (D : SEL → ofe) (CIT : ofe).
  Inductive citg := Citg {
    (** Selector *) citg_sel : SEL;
    (** Inductive children *) citg_ikids : I citg_sel → citg;
    (** Coinductive children *) citg_ckids : C citg_sel → CIT;
    (** Data *) citg_data : D citg_sel;
  }.
End citg.
Add Printing Constructor citg.
Arguments Citg {_ _ _ _ _}. Arguments citg_sel {_ _ _ _ _}.
Arguments citg_ikids {_ _ _ _ _}. Arguments citg_ckids {_ _ _ _ _}.
Arguments citg_data {_ _ _ _ _}.

(** ** [citg_Forall2]: Universal relation between [citg]s *)

(** [citg_Forall2]: Universal relation between [citg]s *)
Section citg_Forall2.
  Context {SEL} {I C : SEL → Type} {D D' : SEL → ofe} {CIT CIT' : ofe}.
  Context (R : ∀ s, D s → D' s → Prop) (CITF : CIT → CIT' → Prop).
  Inductive citg_Forall2
    (t : citg I C D CIT) (t' : citg I C D' CIT') : Prop := Citgf2 {
    citgf2_sel : t.(citg_sel) = t'.(citg_sel);
    citgf2_ikids : ∀ i, citg_Forall2
      (t.(citg_ikids) i) (t'.(citg_ikids) (rew citgf2_sel in i));
    citgf2_ckids : ∀ c, CITF
      (t.(citg_ckids) c) (t'.(citg_ckids) (rew citgf2_sel in c));
    citgf2_data : R t.(citg_sel)
      t.(citg_data) (rew[D'] eq_sym citgf2_sel in t'.(citg_data));
  }.
End citg_Forall2.
Arguments Citgf2 {_ _ _ _ _ _ _ _ _ _ _}.
Arguments citgf2_sel {_ _ _ _ _ _ _ _ _ _ _}.
Arguments citgf2_ikids {_ _ _ _ _ _ _ _ _ _ _}.
Arguments citgf2_ckids {_ _ _ _ _ _ _ _ _ _ _}.
Arguments citgf2_data {_ _ _ _ _ _ _ _ _ _ _}.

Section citg_Forall2.
  Context {SEL} {I C : SEL → Type}.
  Implicit Type D : SEL → ofe.

  (** Introduce [citg_Forall2] for [citg]s with the same [citg_sel] *)
  Lemma citg_Forall2_eq {D D' CIT CIT' R CITF s ti ti' tc tc' d d'} :
    (∀ i, @citg_Forall2 _ I C D D' CIT CIT' R CITF (ti i) (ti' i)) →
    (∀ c, CITF (tc c) (tc' c)) → R s d d' →
    citg_Forall2 R CITF (Citg s ti tc d) (Citg s ti' tc' d').
  Proof.
    move=> ???.
    by apply (Citgf2 (t:=Citg s _ _ _) (t':=Citg s _ _ _) (eq_refl (x:=s))).
  Qed.

  (** [citg_Forall2] is monotone *)
  #[export] Instance citg_Forall2_mono {D D' CIT CIT'} :
    Mono2 (@citg_Forall2 _ I C D D' CIT CIT').
  Proof.
    move=>/= ?? to ?? to' ??. elim=> ?? eq ? IH ??.
    apply (Citgf2 eq); [done|..]=> *; by [apply to'|apply to].
  Qed.
  #[export] Instance citg_Forall2_mono' {D D' CIT CIT' R} :
    Mono (@citg_Forall2 _ I C D D' CIT CIT' R).
  Proof. exact mono2_mono_2. Qed.

  (** [citg_Forall2] preserves reflexivity *)
  #[export] Instance citg_Forall2_refl {CIT}
    `{!∀ s, @Reflexive (D s) (R s), !Reflexive CITF} :
    Reflexive (@citg_Forall2 _ I C _ _ CIT _ R CITF).
  Proof. move=> t. elim: t=> *. by apply citg_Forall2_eq. Qed.

  (** Flip [citg_Forall2] *)
  Lemma citg_Forall2_flip {D D' CIT CIT' R CITF t t'} :
    citg_Forall2 (λ s, flip (R s)) (flip CITF) t' t →
      @citg_Forall2 _ I C D D' CIT CIT' R CITF t t'.
  Proof. elim. move=> [????][????]/=?????. subst. by apply citg_Forall2_eq. Qed.
  (** [citg_Forall2] preserves symmetricity *)
  #[export] Instance citg_Forall2_sym {CIT}
    `{!∀ s, @Symmetric (D s) (R s), !Symmetric CITF} :
    Symmetric (@citg_Forall2 _ I C _ _ CIT _ R CITF).
  Proof.
    move=> ?? F. apply citg_Forall2_flip. move: F. apply citg_Forall2_mono.
    { move=> ????. by symmetry. } { move=> ???. by symmetry. }
  Qed.

  (** Compose [citg_Forall2]s *)
  Lemma citg_Forall2_compose
    {D D' D'' CIT CIT' CIT'' R R' R'' CITF CITF' CITF'' t t' t''} :
    (∀ s d d' d'', R s d d' → R' s d' d'' → R'' s d d'') →
    (∀ ct ct' ct'', CITF ct ct' → CITF' ct' ct'' → CITF'' ct ct'') →
    @citg_Forall2 _ I C D D' CIT CIT' R CITF t t' →
    citg_Forall2 (D':=D'') (CIT':=CIT'') R' CITF' t' t'' →
      citg_Forall2 R'' CITF'' t t''.
  Proof.
    move=> comp comp' F. move: t''. elim: F.
    move=> [????][????]/=?? IH ??[????][/=????].
    subst=>/=. simpl in *. apply citg_Forall2_eq. { move=> ?. by apply IH. }
    { move=> ?. by eapply comp'. } { by eapply comp. }
  Qed.
  (** [citg_Forall2] preserves transitivity *)
  #[export] Instance citg_Forall2_trans {CIT}
    `{!∀ s, @Transitive (D s) (R s), !Transitive CITF} :
    Transitive (@citg_Forall2 _ I C _ _ CIT _ R CITF).
  Proof. move=> ?????. by eapply citg_Forall2_compose. Qed.

  (** [citg_Forall2] preserves equivalence-ness *)
  #[export] Instance citg_Forall2_equivalence {CIT}
    `{!∀ s, @Equivalence (D s) (R s), !Equivalence CITF} :
    Equivalence (@citg_Forall2 _ I C _ _ CIT _ R CITF).
  Proof. split; exact _. Qed.

  (** Convert universally quantified [citg_Forall2], under UIP over [SEL] *)
  Lemma citg_Forall2_forall `{!Uip SEL, !Inhabited A}
    {D D' CIT CIT' R CITF t t'} :
    (∀ a : A, @citg_Forall2 _ I C D D' CIT CIT' (R a) (CITF a) t t') →
      citg_Forall2 (λ _ d d', ∀ a, R a _ d d') (λ t t', ∀ a, CITF a t t') t t'.
  Proof.
    move=> Fs. have F := Fs inhabitant. elim: F Fs.
    move=> [????][????]/=?? IH ?? Fs. subst. simpl in *.
    have eq: ∀ a, (Fs a).(citgf2_sel) = eq_refl by move=> ?; exact: proof_irrel.
    apply citg_Forall2_eq.
    - move=> i. apply IH=> a. have /=+ := (Fs a).(citgf2_ikids) i.
      by rewrite eq.
    - move=> c a. have /=+ := (Fs a).(citgf2_ckids) c. by rewrite eq.
    - move=> a. have /=+ := (Fs a).(citgf2_data). by rewrite eq.
  Qed.
End citg_Forall2.

(** ** [citgO]: OFE structure over [citg] *)
Section citg.
  Context {SEL} {I C : SEL → Type} {D : SEL → ofe} {CIT : ofe}.

  (** Distance for [citg] *)
  Local Instance citg_dist : Dist (citg I C D CIT) :=
    λ n, citg_Forall2 (λ _, (≡{n}≡)) (≡{n}≡).

  (** Equivalence for [citg] *)
  Local Instance citg_equiv : Equiv (citg I C D CIT) :=
    λ t t', ∀ n, citg_dist n t t' (** Trick to avoid UIP *).

  (** OFE mixin of [citg] *)
  Lemma citg_ofe_mixin : OfeMixin (citg I C D CIT).
  Proof.
    split; [done|exact _|]=> ???? F ?. move: F. apply citg_Forall2_mono.
    { move=> ????. by eapply dist_lt. } { move=> ???. by eapply dist_lt. }
  Qed.
  (** OFE of [citg] *)
  Canonical citgO : ofe := Ofe (citg I C D CIT) citg_ofe_mixin.
End citg.
Arguments citgO {_} _ _ _.

(** ** [citg_map]: Map over [citg] *)

(** [citg_map]: Map over [citg] *)
Section citg_map.
  Context {SEL} {I C : SEL → Type} {D D' : SEL → ofe} {CIT CIT' : ofe}.
  Context (f : ∀ s, D s → D' s) (g : CIT → CIT').
  Fixpoint citg_map (t : citg I C D CIT) : citg I C D' CIT' :=
    Citg t.(citg_sel) (λ i, citg_map (t.(citg_ikids) i))
      (λ c, g (t.(citg_ckids) c)) (f _ t.(citg_data)).
End citg_map.

Section citg_map.
  Context {SEL} {I C : SEL → Type}.

  (** [citg_sel] over [citg_map] *)
  Definition citg_sel_map {D D' CIT CIT' f g} {t : citg I C D CIT} :
    (@citg_map _ I C D D' CIT CIT' f g t).(citg_sel) = t.(citg_sel) :=
    let: Citg _ _ _ _ := t in eq_refl.

  (** [citg_map] is non-expansive *)
  #[export] Instance citg_map_ne_gen {D D' CIT CIT' n} :
    Proper (forall_relation (λ _, (≡{n}≡) ==> (≡{n}≡)) ==> ((≡{n}≡) ==> (≡{n}≡))
      ==> (≡{n}≡) ==> (≡{n}≡)) (@citg_map _ I C D D' CIT CIT').
  Proof.
    move=> ?? to ?? to' ??. elim. move=> [????][????]/=?. subst=>/= ? IH ??.
    apply citg_Forall2_eq=>//. { move=> ?. by apply to'. } { by apply to. }
  Qed.

  (** [citg_map] over an identity function *)
  Lemma citg_map_id {D CIT f g t} :
    (∀ s d, f s d ≡ d) → (∀ ct, g ct ≡ ct) →
      @citg_map _ I C D _ CIT _ f g t ≡ t.
  Proof.
    move=> eq eq' ?. elim: t=>/= ?? IH ??.
    apply citg_Forall2_eq=>// >; by apply equiv_dist.
  Qed.

  (** [citg_map] over [∘] *)
  Lemma citg_map_compose {D D' D'' CIT CIT' CIT'' f f' g g' t}
    `{!∀ s, Reflexive (R s), !Reflexive CITF} :
    citg_Forall2 R CITF
      (citg_map f' g' (@citg_map _ I C D D' CIT CIT' f g t))
      (citg_map (D':=D'') (CIT':=CIT'') (λ s, f' s ∘ f s) (g' ∘ g) t).
  Proof. elim: t=>/= *. by apply citg_Forall2_eq. Qed.
End citg_map.

(** ** [citg_fold]: Fold [citg] *)
Section citg_fold.
  Context {SEL} {I C : SEL → Type} {D : SEL → ofe} {CIT A : ofe}.
  Context (f : ∀ s, (I s -d> A) → (C s -d> CIT) → D s → A).
  Fixpoint citg_fold (t : citg I C D CIT) : A :=
    f t.(citg_sel) (λ i, citg_fold (t.(citg_ikids) i)) t.(citg_ckids)
      t.(citg_data).
End citg_fold.

Section citg_fold.
  Context {SEL} {I C : SEL → Type} {D : SEL → ofe} {CIT A : ofe}.

  (** [citg_fold] is non-expansive *)
  #[export] Instance citg_fold_ne_gen {n} :
    Proper (forall_relation (λ _,
      (≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡)) ==>
      (≡{n}≡) ==> (≡{n}≡)) (@citg_fold _ I C D CIT A).
  Proof.
    move=> ?? to ??. elim=>/=. move=> [????][????]/= ?. subst=>/= ????.
    by apply to.
  Qed.
  #[export] Instance citg_fold_ne {n}
    `{!∀ s, Proper ((≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡)) (f s)} :
    Proper ((≡{n}≡) ==> (≡{n}≡)) (@citg_fold _ I C D CIT A f).
  Proof. apply citg_fold_ne_gen. solve_proper. Qed.
End citg_fold.

(** ** [citi]: Iteration of [citg] *)
Definition citiO {SEL} (I C : SEL → Type) (D : SEL → ofe) (k : nat) : ofe :=
  Nat.iter k (@citgO SEL I C D) unitO.
Definition citi {SEL} (I C : SEL → Type) (D : SEL → ofe) (k : nat) : Type :=
  citiO I C D k.

(** ** [citi_Forall2]: Universal relation between [citi]s *)
Section citi_Forall2.
  Context {SEL} {I C : SEL → Type} {D D' : SEL → ofe}.
  Context (R : ∀ s, D s → D' s → Prop).
  Fixpoint citi_Forall2 {k k'} : citi I C D k → citi I C D' k' → Prop :=
    match k, k' with
    | S _, S _ => citg_Forall2 R citi_Forall2
    | _, _ => λ _ _, True
    end.
End citi_Forall2.

Section citi_Forall2.
  Context {SEL} {I C : SEL → Type}.
  Implicit Type D : SEL → ofe.

  (** [citi_Forall2] is monotone *)
  Lemma citi_Forall2_mono {D D' k k' R R'} :
    (∀ s, R s ⊑ R' s) → @citi_Forall2 _ I C D D' R k k' ⊑ citi_Forall2 R'.
  Proof.
    move=> to. move: k'. elim: k; [done|]=>/= k IH. case; [done|]=> ?.
    apply citg_Forall2_mono; [done|]. apply IH.
  Qed.
  (** Turn [citi_Forall2 (λ _, (≡))] to [citi_Forall2 (λ _, (≡{n}≡))] *)
  Lemma citi_Forall2_equiv_dist {D k k' n} :
    @citi_Forall2 _ I C D _ (λ _, (≡)) k k' ⊑ citi_Forall2 (λ _, (≡{n}≡)).
  Proof. by apply citi_Forall2_mono=> ??? /equiv_dist. Qed.

  (** Unfold [≡{_}≡] over [citi] *)
  Lemma citi_dist_Forall2 {D k n t t'} :
    t ≡{n}≡ t' ↔ @citi_Forall2 _ I C D _ (λ _, (≡{n}≡)) k _ t t'.
  Proof.
    move: t t'. elim: k; [done|]=>/= ? IH ??.
    split; apply citg_Forall2_mono'=> ???; by apply IH.
  Qed.
  (** Unfold [≡] over [citi] *)
  Lemma citi_equiv_Forall2 {D k t t'} :
    t ≡ t' ↔ ∀ n, @citi_Forall2 _ I C D _ (λ _, (≡{n}≡)) k _ t t'.
  Proof. rewrite equiv_dist. split=> ??; by apply citi_dist_Forall2. Qed.

  (** [citi_Forall2] preserves reflexivity *)
  #[export] Instance citi_Forall2_refl `{!∀ s, @Reflexive (D s) (R s)} {k} :
    Reflexive (@citi_Forall2 _ I C _ _ R k _).
  Proof. elim: k; [done|]=>/= ??. exact _. Qed.

  (** Flip [citi_Forall2] *)
  Lemma citi_Forall2_flip {D D' R k k' t t'} :
    citi_Forall2 (λ s, flip (R s)) t' t → @citi_Forall2 _ I C D D' R k k' t t'.
  Proof.
    move: k' t t'. elim: k; [done|]=> ? IH. case; [done|]=>/= ??? all.
    apply citg_Forall2_flip. move: all. apply citg_Forall2_mono'=> ???.
    by apply IH.
  Qed.
  (** [citi_Forall2] preserves symmetricity *)
  Lemma citi_Forall2_sym `{!∀ s, @Symmetric (D s) (R s)}
    {k k' t t'} :
    @citi_Forall2 _ I C _ _ R k k' t t' → citi_Forall2 R t' t.
  Proof.
    move=> F. apply citi_Forall2_flip. move: F. by apply citi_Forall2_mono.
  Qed.
  #[export] Instance citi_Forall2_sym' `{!∀ s, @Symmetric (D s) (R s)} {k'} :
    Symmetric (@citi_Forall2 _ I C _ _ R k' _).
  Proof. move=> ??. apply citi_Forall2_sym. Qed.

  (** Compose [citi_Forall2]s *)
  Lemma citi_Forall2_compose {D D' D'' R R' R'' k k' k'' t t' t''} :
    (∀ s d d' d'', R s d d' → R' s d' d'' → R'' s d d'') →
    min k k'' ≤ k' → @citi_Forall2 _ I C D D' R k k' t t' →
      citi_Forall2 (D':=D'') (k':=k'') R' t' t'' → citi_Forall2 R'' t t''.
  Proof.
    move=> tr. move: k'' k' t t' t''. elim: k; [done|]=> k IH.
    case; [done|]=> k''. case; [lia|]=>/= k' ??????.
    eapply citg_Forall2_compose=>//= ???. apply IH. lia.
  Qed.
  (** [citi_Forall2] preserves transitivity *)
  Lemma citi_Forall2_trans `{!∀ s, @Transitive (D s) (R s)}
    {k k' k'' t t' t''} :
    min k k'' ≤ k' → @citi_Forall2 _ I C D _ R k k' t t' →
      citi_Forall2 (k':=k'') R t' t'' → citi_Forall2 R t t''.
  Proof. by apply citi_Forall2_compose. Qed.
  #[export] Instance citi_Forall2_trans' `{!∀ s, @Transitive (D s) (R s)} {k} :
    Transitive (@citi_Forall2 _ I C _ _ R k _).
  Proof. move=> ???. apply citi_Forall2_trans. lia. Qed.

  (** [citi_Forall2] preserves equivalence-ness *)
  #[export] Instance citi_Forall2_equivalence
    `{!∀ s, @Equivalence (D s) (R s)} {k} :
    Equivalence (@citi_Forall2 _ I C _ _ R k _).
  Proof. split; exact _. Qed.

  (** Convert universally quantified [citg_Forall2], under UIP over [SEL] *)
  Lemma citi_Forall2_forall `{!Uip SEL, !Inhabited A} {D D' R k k' t t'} :
    (∀ a : A, @citi_Forall2 _ I C D D' (R a) k k' t t') →
      citi_Forall2 (λ _ d d', ∀ a, R a _ d d') t t'.
  Proof.
    move: k' t t'. elim: k; [done|]=> ? IH. case; [done|]=>/= ???.
    move /citg_Forall2_forall. apply citg_Forall2_mono'=> ?? +. apply IH.
  Qed.

  (** Unfold [≡] over [citi], under UIP over [SEL] *)
  Lemma citi_equiv_Forall2' {D k t t'} `{!Uip SEL} :
    t ≡ t' ↔ @citi_Forall2 _ I C D _ (λ _, (≡)) k _ t t'.
  Proof.
    rewrite citi_equiv_Forall2. split.
    - move=> /citi_Forall2_forall. by apply citi_Forall2_mono=> ??? /equiv_dist.
    - move=> + ?. apply citi_Forall2_equiv_dist.
  Qed.
End citi_Forall2.

(** ** [citi_map]: Map over [citi] *)

Section citi_map.
  Context {SEL} {I C : SEL → Type} {D D' : SEL → ofe}.
  Context (f : ∀ s, D s → D' s).
  (** [citi_map]: Map over [citi] *)
  Fixpoint citi_map {k} : citi I C D k → citi I C D' k :=
    match k with S _ => citg_map f citi_map | 0 => id end.
End citi_map.

Section citi_map.
  Context {SEL} {I C : SEL → Type}.

  (** [citi_map] is non-expansive *)
  #[export] Instance citi_map_ne_gen {D D' n} :
    Proper (forall_relation (λ _, (≡{n}≡) ==> (≡{n}≡)) ==>
      forall_relation (λ _, (≡{n}≡) ==> (≡{n}≡)))
      (@citi_map _ I C D D').
  Proof. move=> ???. elim; solve_proper. Qed.

  (** [citi_map] over an identity function *)
  Lemma citi_map_id {D f k t} :
    (∀ s d, f s d ≡ d) → @citi_map _ I C D _ f k t ≡ t.
  Proof.
    move=> ?. move: t. elim: k; [done|]=>/= ???. by apply citg_map_id.
  Qed.

  (** [citi_map] over [∘] *)
  Lemma citi_map_compose {D D' D'' f g k t} :
    citi_map g (@citi_map _ I C D D' f k t) ≡
      citi_map (D':=D'') (λ s, g s ∘ f s) t.
  Proof.
    apply equiv_dist=> ?. move: t. elim: k; [done|]=>/= ??. elim=>/= *.
    by apply citg_Forall2_eq.
  Qed.
End citi_map.

(** ** [wfcit]: Approximation sequence of [citi] is well-formed *)
Section wfcit.
  Context {SEL} {I C : SEL → Type} {D : SEL → ofe}.
  CoInductive wfcit
    (* Head *) (t : citi I C D 1)
    (* Tail *) (tl : ∀ k, citi I C D (S (S k))) : Prop := Wfcit {
    (** Selector equality *)
    wfc_sel : ∀ k, t.(citg_sel) = (tl k).(citg_sel);
    (** On inductive children *)
    wfc_ikids : ∀ i, wfcit (t.(citg_ikids) i)
      (λ k, (tl k).(citg_ikids) (rew wfc_sel k in i));
    (** On coinductive children *)
    wfc_ckids : ∀ c, wfcit ((tl 0).(citg_ckids) (rew wfc_sel 0 in c))
      (λ k, (tl (S k)).(citg_ckids) (rew wfc_sel (S k) in c));
    (** Data equality *)
    wfc_data : ∀ k,
      t.(citg_data) ≡ rew[D] eq_sym (wfc_sel k) in (tl k).(citg_data);
  }.
End wfcit.
Add Printing Constructor wfcit.
Arguments Wfcit {_ _ _ _ _ _}. Arguments wfc_sel {_ _ _ _ _ _}.
Arguments wfc_ikids {_ _ _ _ _ _}. Arguments wfc_ckids {_ _ _ _ _ _}.
Arguments wfc_data {_ _ _ _ _ _}.

Section wfcit.
  Context {SEL} {I C : SEL → Type} {D : SEL → ofe}.

  (** [wfcit] into equivalence between the head and an element in the tail *)
  Lemma wfcit_equiv_ht {t tl} k :
    @wfcit _ I C D t tl → citi_Forall2 (λ _, (≡)) t (tl k).
  Proof.
    move: tl. elim: t=>/= s ti IH tc d tl[/=sel ?? deq].
    apply (Citgf2 (t:=Citg s _ _ _) (sel k)); [|done..]=>/= i.
    by apply (IH i (λ k, _)).
  Qed.
  (** [wfcit] into equivalence between elements in the tail *)
  Lemma wfcit_equiv_tt {t tl k k'} :
    @wfcit _ I C D t tl → citi_Forall2 (λ _, (≡)) (tl k) (tl k').
  Proof.
    move=> wf. wlog: k k' / k < k'.
    { move=> goal. have : k < k' ∨ k = k' ∨ k > k' by lia.
      case=> [?|[?|gt]]; [by apply goal|by subst|]. apply citi_Forall2_flip.
      move: (goal _ _ gt). by apply citi_Forall2_mono=> ????. }
    case: k'; [lia|]=> k' lt /=. move: k k' lt t tl wf. fix FIX 1=> k k' lt.
    elim=>/= s ti IH tc d tl [/=sel wfi wfc deq].
    apply (Citgf2 (eq_trans (eq_sym (sel k)) (sel (S k')))).
    - move=> i. rewrite -rew_compose -{1}(rew_sym_r (sel k) i).
      by apply (IH (rew eq_sym (sel k) in i) (λ _, _)).
    - move=> c. have := wfc (rew eq_sym (sel k) in c). rewrite -rew_compose.
      rewrite -{3}(rew_sym_r (sel k) c). destruct k as [|k].
      { apply (wfcit_equiv_ht (tl:=λ _, _)). }
      destruct k' as [|k']; [lia|]. apply FIX. lia.
    - move: (sel k) (sel (S k')) (deq k) (deq (S k'))=> ?. subst=>/= ? <- ->.
      by rewrite eq_trans_refl_l.
  Qed.

  (** [wfcit] from universal equivalence, under UIP over [SEL] *)
  Lemma equiv_wfcit `{!Uip SEL} {t tl} :
    (∀ k, citi_Forall2 (λ _, (≡)) t (tl k)) →
    (∀ k k', k < k' → citi_Forall2 (λ _, (≡)) (tl k) (tl k')) →
      @wfcit _ I C D t tl.
  Proof.
    move: t tl. cofix FIX. move=> [????]?/= hteq tteq.
    apply (Wfcit (λ k, (hteq k).(citgf2_sel)))=>/=.
    - move=> i. apply FIX. { move=> k. apply hteq. }
      move=> k k' lt. case: (tteq k k' lt)=> sel F _ _.
      move: (F (rew (hteq k).(citgf2_sel) in i)). rewrite rew_compose.
      by rewrite (proof_irrel (eq_trans _ _) (hteq _).(citgf2_sel)).
    - move=> c. apply FIX.
      { move=> k. have lt : 0 < S k by lia. case: (tteq 0 (S k) lt)=> ? _ F _.
        move: (F (rew (hteq 0).(citgf2_sel) in c)). rewrite rew_compose.
        by rewrite (proof_irrel (eq_trans _ _) (hteq _).(citgf2_sel)). }
      move=> k k' lt. have lt' : S k < S k' by lia.
      case: (tteq (S k) (S k') lt')=> ? _ F _.
      move: (F (rew (hteq (S k)).(citgf2_sel) in c)).
      by rewrite rew_compose (proof_irrel (eq_trans _ _) (hteq _).(citgf2_sel)).
    - move=> ?. apply hteq.
  Qed.
  Lemma equiv_wfcit' `{!Uip SEL} {ts} :
    (∀ k k', k < k' → citi_Forall2 (λ _, (≡)) (ts k) (ts k')) →
      @wfcit _ I C D (ts 0) (λ k, ts (S k)).
  Proof. move=> F. apply equiv_wfcit=> *; apply F; lia. Qed.
End wfcit.

(** ** [cita]: Coinductive-inductive tree by approximation *)
Section cita.
  Context {SEL} (I C : SEL → Type) (D : SEL → ofe).
  #[projections(primitive)]
  Record cita := Cita {
    cita_head : citi I C D 1;
    cita_tail : ∀ k, citi I C D (S (S k));
    cita_wf : wfcit cita_head cita_tail;
  }.
End cita.
Add Printing Constructor cita.
Arguments Cita {_ _ _ _}. Arguments cita_head {_ _ _ _}.
Arguments cita_tail {_ _ _ _}. Arguments cita_wf {_ _ _ _}.

(** Whole sequence of [cita] *)
Definition cita_seq {SEL I C D} (ta : @cita SEL I C D) (k : nat)
  : citi I C D (S k) :=
  match k with 0 => ta.(cita_head) | S k' => ta.(cita_tail) k' end.
Coercion cita_seq : cita >-> Funclass.

Section cita.
  Context {SEL} {I C : SEL → Type} {D : SEL → ofe}.

  (** Elements of [cita] are equivalent *)
  Lemma cita_seq_equiv {ta : cita I C D} {k k'} :
    citi_Forall2 (λ _, (≡)) (ta k) (ta k').
  Proof.
    case: k=> [|k]; case: k'=> [|k']//.
    - simpl. apply wfcit_equiv_ht, cita_wf.
    - apply citi_Forall2_sym=>/=. apply wfcit_equiv_ht, cita_wf.
    - simpl. eapply wfcit_equiv_tt, cita_wf.
  Qed.
  Lemma cita_seq_dist {ta : cita I C D} {n k k'} :
    citi_Forall2 (λ _, (≡{n}≡)) (ta k) (ta k').
  Proof. apply citi_Forall2_equiv_dist, cita_seq_equiv. Qed.
End cita.

(** Universal relation over [cita] *)
Definition cita_rel {SEL I C D D'}
  (R : ∀ k, @citi SEL I C D k → citi I C D' k → Prop)
  (ta : cita I C D) (ta' : cita I C D') : Prop :=
  ∀ k, R _ (ta k) (ta' k).

(** ** OFE for [cita] *)
Section citaO.
  Context {SEL} {I C : SEL → Type} {D : SEL → ofe}.

  (** Distance for [cita] *)
  Local Instance cita_dist : Dist (cita I C D) :=
    λ n, cita_rel (λ _, (≡{n}≡)).

  (** Equivalence for [cita] *)
  Local Instance cita_equiv : Equiv (cita I C D) :=
    cita_rel (λ _, (≡)).

  (** OFE mixin of [cita] *)
  Lemma cita_ofe_mixin : OfeMixin (cita I C D).
  Proof.
    split.
    - move=> ??. split. { move=> eq ??. apply equiv_dist. by apply eq. }
      { move=> eq ?. apply equiv_dist=> ?. apply eq. }
    - move=> ?. split. { by move=> ??. } { move=> ????. by symmetry. }
      { move=> ??? eq ??. by etrans; [by apply eq|]. }
    - move=> ???? eq ??. eapply dist_lt; [|done]. apply eq.
  Qed.
  (** OFE of [cita] *)
  Canonical citaO : ofe := Ofe (cita I C D) cita_ofe_mixin.
End citaO.
Arguments citaO {_} _ _ _.

(** ** [cit]: Coinductive-inductive tree *)
Definition citO {SEL} (I C : SEL → Type) (D : SEL → ofe) : ofe :=
  citgO I C D (citaO I C D).
Definition cit {SEL} (I C : SEL → Type) (D : SEL → ofe) : Type :=
  citO I C D.

Section citO.
  Context {SEL} {I C : SEL → Type} {D : SEL → ofe}.

  (** [citgO I C D CIT] is discrete if [D] and [CIT] are discrete *)
  #[export] Instance citgO_discrete {CIT}
    `{!∀ s, OfeDiscrete (D s), !OfeDiscrete CIT} :
    OfeDiscrete (citgO I C D CIT).
  Proof.
    move=> ?? + ?.
    by apply citg_Forall2_mono; [move=> ?|]=> ?? /discrete_0/equiv_dist.
  Qed.
  (** [citiO I C D k] is discrete if [D] is discrete *)
  #[export] Instance citiO_discrete `{!∀ s, OfeDiscrete (D s)} {k} :
    OfeDiscrete (citiO I C D k).
  Proof. elim: k; exact _. Qed.

  (** [citaO I C D] is discrete if [D] is discrete *)
  #[export] Instance cita_discrete `{!∀ s, OfeDiscrete (D s)} :
    OfeDiscrete (citaO I C D).
  Proof. move=> ?? E ?. apply discrete_0; [exact _|]. apply E. Qed.

  (** [Citg] is non-expansive *)
  #[export] Instance Citg_ne {CIT s n} :
    Proper (pointwise_relation _ (≡{n}≡) ==> pointwise_relation _ (≡{n}≡) ==>
      (≡{n}≡) ==> (≡{n}≡)) (@Citg _ I C D CIT s).
  Proof. move=> ?????????. by apply citg_Forall2_eq. Qed.
  #[export] Instance Citg_proper {CIT s} :
    Proper (pointwise_relation _ (≡) ==> pointwise_relation _ (≡) ==>
      (≡) ==> (≡)) (@Citg _ I C D CIT s).
  Proof.
    move=> ?? eqi ???????. apply citg_Forall2_eq=>/= >.
    { apply eqi. } { by apply equiv_dist. } { by apply equiv_dist. }
  Qed.

  (** [Citg] preserves discreteness *)
  #[export] Instance Citg_discrete {CIT s ti tc d}
    `{!∀ i, Discrete (ti i), !∀ c, Discrete (tc c), !Discrete d} :
    Discrete (@Citg _ I C D CIT s ti tc d).
  Proof.
    move=> [????][/=?]. subst=>/= Ei Ec deq n. apply citg_Forall2_eq.
    - move=> i. move: (Ei i)=>/(discrete_0 (ti i)) Ei'. apply Ei'.
    - move=> c. by move: (Ec c)=>/discrete_0/equiv_dist.
    - by move: deq=> /discrete_0/equiv_dist.
  Qed.

  (** [citg_sel] is non-expansive *)
  Definition cit_sel_ne {CIT n} {t t' : citg I C D CIT}
    (eqv : t ≡{n}≡ t') : t.(citg_sel) = t'.(citg_sel) := eqv.(citgf2_sel).
  (** [citg_ikids] is non-expansive *)
  Lemma citg_ikids_ne {CIT n} {t t' : citg I C D CIT} {i} (eqv : t ≡{n}≡ t') :
    t.(citg_ikids) i ≡{n}≡ t'.(citg_ikids) (rew cit_sel_ne eqv in i).
  Proof. apply eqv. Qed.
  (** [citg_ckids] is non-expansive *)
  Lemma citg_ckids_ne {CIT n} {t t' : citg I C D CIT} {c} (eqv : t ≡{n}≡ t') :
    t.(citg_ckids) c ≡{n}≡ t'.(citg_ckids) (rew cit_sel_ne eqv in c).
  Proof. apply eqv. Qed.
  (** [citg_data] is non-expansive *)
  Lemma cit_data_ne {CIT n} {t t' : citg I C D CIT} (eqv : t ≡{n}≡ t') :
    t.(citg_data) ≡{n}≡ rew[D] eq_sym (cit_sel_ne eqv) in t'.(citg_data).
  Proof. apply eqv. Qed.
End citO.

(** ** Conversion between [cit] and [cita] *)
Section of_cit.
  Context {SEL} {I C : SEL → Type} {D : SEL → ofe}.

  (** [of_cit]: Convert [cit] into [cita] *)
  Program CoFixpoint wf_of_cit (t : cit I C D) :
    wfcit (citg_map (λ _, id) (λ _, ()) t)
      (λ k, citg_map (λ _, id) (λ ta, cita_seq ta k) t) :=
    let: Citg s ti tc d := t in
    Wfcit (λ _, eq_refl) (λ i, wf_of_cit (ti i))
      (λ c, (tc c).(cita_wf)) (λ _, reflexivity _).
  Definition of_cit_def (t : cit I C D) : cita I C D :=
    Cita (citg_map (λ _, id) (λ _, ()) t)
      (λ k, citg_map (λ _, id) (λ ta, cita_seq ta k) t) (wf_of_cit t).
  Lemma of_cit_aux : seal of_cit_def. Proof. by eexists _. Qed.
  Definition of_cit := of_cit_aux.(unseal).
  Lemma of_cit_unseal : of_cit = of_cit_def. Proof. by exact: seal_eq. Qed.

  (** [to_cit]: Convert [cita] into [cit] *)
  Fixpoint to_cit' (t : citi I C D 1) (tl : ∀ k, citi I C D (S (S k)))
    (wf : wfcit t tl) : cit I C D :=
    Citg t.(citg_sel)
      (λ i, to_cit' (t.(citg_ikids) i)
        (λ k, (tl k).(citg_ikids) (rew wf.(wfc_sel) k in i)) (wf.(wfc_ikids) i))
      (λ c, Cita ((tl 0).(citg_ckids) (rew wf.(wfc_sel) 0 in c))
        (λ k, (tl (S k)).(citg_ckids) (rew wf.(wfc_sel) (S k) in c))
        (wf.(wfc_ckids) c))
      t.(citg_data).
  Definition to_cit_def (ta : cita I C D) : cit I C D :=
    to_cit' ta.(cita_head) ta.(cita_tail) ta.(cita_wf).
  Lemma to_cit_aux : seal to_cit_def. Proof. by eexists _. Qed.
  Definition to_cit := to_cit_aux.(unseal).
  Lemma to_cit_unseal : to_cit = to_cit_def. Proof. by exact: seal_eq. Qed.

  (** Simplify [to_cit] over [of_cit] *)
  Lemma to_of_cit {t} : to_cit (of_cit t) ≡ t.
  Proof.
    rewrite to_cit_unseal of_cit_unseal. move=> ?. elim: t=>/= ?????.
    by apply citg_Forall2_eq.
  Qed.

  (** Simplify [of_cit] over [to_cit] *)
  Lemma of_to_cit {ta} : of_cit (to_cit ta) ≡ ta.
  Proof.
    rewrite of_cit_unseal to_cit_unseal. move=> n k. move: ta=> [t tl wf]/=.
    case: n=>/=.
    { elim: t tl wf=> ?? IH tc ???/=. apply citg_Forall2_eq=>// i. apply IH. }
    move=> n. elim: t tl wf=> ?? IH ???[/=sel ?? deq] /=.
    apply (Citgf2 (t:=Citg _ _ _ _) (sel n))=>/=. { move=> ?. apply IH. }
    { by destruct n. } { by rewrite (deq n). }
  Qed.

  (** [of_cit] is non-expansive *)
  #[export] Instance of_cit_ne : NonExpansive of_cit.
  Proof.
    rewrite of_cit_unseal=> ???. elim. move=> [s ti tc d][? ti' tc' d']/=?.
    subst=>/= Fi IH Fc dR. case=>/=.
    { apply citg_Forall2_eq=>// i. apply (IH i 0). }
    move=> k. apply citg_Forall2_eq=>//. { move=> i. apply (IH i (S _)). }
    move=> ?. apply Fc.
  Qed.
  #[export] Instance of_cit_proper : Proper ((≡) ==> (≡)) of_cit.
  Proof. apply ne_proper, _. Qed.

  (** [to_cit] is proper, under UIP over [SEL] *)
  #[export] Instance to_cit_ne `{!Uip SEL} : NonExpansive to_cit.
  Proof.
    rewrite to_cit_unseal=> n ta ta'. move: ta ta'=> [+ + +][+ + +].
    elim=> ? ti IH tc d tl [/=sel ???] [s ti' tc' d'] tl' [/=sel' ???] F.
    case: (F 0)=>/= ?. subst=>/= ???. apply citg_Forall2_eq=>//=.
    - move=> i. apply IH=>//=. move=> k. apply citi_dist_Forall2=>//=.
      case: k=>/=; [done|]=> k. case: (F (S k))=>/= ? Fi _ _.
      have := (Fi (rew sel k in i)). rewrite rew_compose /=.
      rewrite (proof_irrel (eq_trans _ _) (sel' _)). apply citg_Forall2_mono'.
      move=>/= ???. by apply (citi_dist_Forall2 (k:=S k)).
    - move=> c k. case: (F (S k))=>/= ? _ Fc _. move: (Fc (rew sel _ in c)).
      destruct k as [|?]=>/=;
        by rewrite rew_compose (proof_irrel (eq_trans _ _) (sel' _)).
  Qed.
  #[export] Instance to_cit_proper `{!Uip SEL} : Proper ((≡) ==> (≡)) to_cit.
  Proof. apply ne_proper, _. Qed.

  (** [of_cit] preserves discreteness, under UIP over [SEL] *)
  #[export] Instance of_cit_discrete `{!Uip SEL, !Discrete t} :
    Discrete (of_cit t).
  Proof.
    move=> ta eq. rewrite -(@of_to_cit ta). f_equiv.
    apply discrete_0; [exact _|]. by rewrite -eq to_of_cit.
  Qed.
End of_cit.

(** ** Map over [cit] and [cita] *)

Section cit_map.
  Context {SEL} {I C : SEL → Type} {D D' : SEL → ofe}.

  (** [wfcit] over [citi_map] *)
  Local Lemma wfcit_map' `{!∀ s, NonExpansive (f s)} {t tl tl'} :
    (∀ k, tl' k = citi_map f (tl k)) → wfcit t tl →
      wfcit (@citi_map _ I C D D' f _ t) tl'.
  Proof.
    move: t tl tl'. cofix FIX. move=> [s ti tc d] tl tl' eq [/=sel wfi wfc deq].
    apply (Wfcit (t:=Citg s _ _ _)
      (λ k, rew [λ t, s = t.(citg_sel)]
        eq_sym (eq k) in eq_trans (sel k) (eq_sym citg_sel_map)))=>/=.
    - move=> i. move: (wfi i). apply FIX=> k.
      move: (tl k) (tl' k) (eq k) (sel k)=> [????]???. by subst.
    - move=> c. move: (wfc c). move: (tl 0) (tl' 0) (eq 0) (sel 0)=> [????]??.
      subst=>/= ?. apply FIX=> k.
      move: (tl (S k)) (tl' (S k)) (eq (S k)) (sel (S k))=> [????]???.
      by subst=>/=.
    - move=> k. move: (tl k) (tl' k) (eq k) (sel k) (deq k)=> [????]???.
      subst=>/= deq'. apply equiv_dist=> ?. f_equiv. by apply equiv_dist.
  Qed.
  Lemma wfcit_map `{!∀ s, NonExpansive (f s)} {t tl} :
    wfcit t tl → wfcit (@citi_map _ I C D D' f _ t) (λ k, citi_map f (tl k)).
  Proof. by apply wfcit_map'. Qed.

  (** [cita_map]: Map over [cita] *)
  Definition cita_map
    (f : ∀ s, D s -n> D' s)
    (ta : cita I C D) : cita I C D' :=
    Cita (citi_map f ta.(cita_head)) (λ k, citi_map f (ta.(cita_tail) k))
      (wfcit_map ta.(cita_wf)).

  (** [cit_map]: Map over [cit] *)
  Definition cit_map (f : ∀ s, D s -n> D' s) (t : cit I C D) : cit I C D' :=
    citg_map f (cita_map f) t.
End cit_map.

Section cit_map.
  Context {SEL} {I C : SEL → Type}.

  (** [cita_seq] over [cita_map] *)
  Lemma cita_seq_map {D D' f ta k} :
    @cita_map _ I C D D' f ta k = citi_map f (ta k).
  Proof. by case: k. Qed.

  (** [cita_map] is non-expansive *)
  #[export] Instance cita_map_ne_gen {D D' n} :
    Proper (forall_relation (λ _, (≡{n}≡)) ==> (≡{n}≡) ==> (≡{n}≡))
      (@cita_map _ I C D D').
  Proof.
    move=> ?? eq ????. rewrite !cita_seq_map. apply citi_map_ne_gen; [|done].
    move=> ???<-. apply eq.
  Qed.

  (** [cita_map] over an identity function *)
  Lemma cita_map_id {D ta} {f : ∀ s, D s -n> _} :
    (∀ s d, f s d ≡ d) → @cita_map _ I C D _ f ta ≡ ta.
  Proof. move=> ??. by rewrite cita_seq_map citi_map_id. Qed.

  (** [cita_map] over [∘] *)
  Lemma cita_map_compose {D D' D'' f g ta} :
    cita_map g (@cita_map _ I C D D' f ta) ≡
      cita_map (D':=D'') (λ s, g s ◎ f s) ta.
  Proof. move=> ?. rewrite !cita_seq_map. apply citi_map_compose. Qed.

  (** [cit_map] is non-expansive *)
  #[export] Instance cit_map_ne_gen {D D' n} :
    Proper (forall_relation (λ _, (≡{n}≡)) ==> (≡{n}≡) ==> (≡{n}≡))
      (@cit_map _ I C D D').
  Proof.
    move=> ?? to ???. apply citg_map_ne_gen; [..|done].
    { move=> ???<-. apply to. }
    move=> ???. by apply cita_map_ne_gen.
  Qed.
  #[export] Instance cit_map_ne {D D' f} :
    NonExpansive (@cit_map _ I C D D' f).
  Proof. move=> ?. apply cit_map_ne_gen. solve_proper. Qed.

  (** [cit_map] over an identity function *)
  Lemma cit_map_id {D t} {f : ∀ s, D s -n> _} :
    (∀ s d, f s d ≡ d) → @cit_map _ I C D _ f t ≡ t.
  Proof. move=> ?. apply citg_map_id; [done|]=> ?. by apply cita_map_id. Qed.

  (** [cit_map] over [∘] *)
  Lemma cit_map_compose {D D' D'' f g t} :
    cit_map g (@cit_map _ I C D D' f t) ≡ cit_map (D':=D'') (λ s, g s ◎ f s) t.
  Proof.
    move=> ?. elim: t=> ?? IH ??. apply citg_Forall2_eq=>// ?.
    apply equiv_dist, cita_map_compose.
  Qed.

  (** [of_cit] over [cit_map] *)
  Lemma of_cit_map {D D' f t} :
    of_cit (@cit_map _ I C D D' f t) ≡ cita_map f (of_cit t).
  Proof.
    rewrite !of_cit_unseal=> k. apply citi_equiv_Forall2=> n. case: k=>/=.
    { etrans; [apply citg_map_compose|].
      by etrans; [|symmetry; apply citg_map_compose]. }
    move=> k. etrans; [apply citg_map_compose|].
    etrans; [|symmetry; apply citg_map_compose]. elim: t=>/= ?????.
    apply citg_Forall2_eq=>//. move=> ?. by rewrite cita_seq_map.
  Qed.
End cit_map.

(** ** [cit_fold]: Fold [cit] *)
Definition cit_fold {SEL} {I C : SEL → Type} {D : SEL → ofe} {A : ofe}
  (f : ∀ s, (I s -d> A) → (C s -d> citO I C D) → D s → A) : citO I C D → A :=
  citg_fold (λ s ri tc d, f s ri (λ c, to_cit (tc c)) d).

Section cit_fold.
  Context {SEL} {I C : SEL → Type}.
  Implicit Type (D : SEL → ofe) (CIT A : ofe).

  (** [cit_fold] is non-expansive, under UIP over [SEL] *)
  #[export] Instance cit_fold_ne_gen `{!Uip SEL} {D A n} :
    Proper (forall_relation (λ _,
      (≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡)) ==>
      (≡{n}≡) ==> (≡{n}≡)) (@cit_fold _ I C D A).
  Proof.
    move=> ?? to ???. apply citg_fold_ne_gen; [|done]=> ??????????.
    apply to=>// ?. by do 2 f_equiv.
  Qed.
  #[export] Instance cit_fold_ne `{!Uip SEL} {D A n}
    `{∀ s, Proper (pointwise_relation _ (≡{n}≡) ==>
        pointwise_relation _ (≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡)) (f s)} :
    Proper ((≡{n}≡) ==> (≡{n}≡)) (@cit_fold _ I C D A f).
  Proof. apply cit_fold_ne_gen. solve_proper. Qed.
  #[export] Instance cit_fold_equiv `{!Uip SEL} {D A}
    `{!∀ n s, Proper (pointwise_relation _ (≡{n}≡) ==>
        pointwise_relation _ (≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡)) (f s)} :
    Proper ((≡) ==> (≡)) (@cit_fold _ I C D A f).
  Proof. apply ne_proper, _. Qed.
End cit_fold.

(** ** Productivity structure for [cita] and [cit] *)

(** [citaPR]: Productivity structure for [cita] *)
Program Canonical citaPR {SEL} I C D :=
  Prost (@citaO SEL I C D) (λ k ta ta', ta k ≡ ta' k) _ _ _.
Next Obligation.
  split. { by move=> ?. } { move=> ???. by symmetry. }
  { move=> ?????. by etrans. }
Qed.
Next Obligation.
  move=> ???? k k' ta ta' ? /equiv_dist F. apply equiv_dist=> ?.
  apply citi_dist_Forall2.
  eapply citi_Forall2_trans; [|exact (cita_seq_dist (k':=k))|]; [lia|].
  eapply citi_Forall2_trans; [| |exact (cita_seq_dist (k:=k))]; [lia|].
  by apply citi_dist_Forall2.
Qed.
Next Obligation. move=> ??????. split; [done|]=> eq ?. apply eq. Qed.

(** [citPR]: Productivity structure for [cit], under UIP over [SEL] *)
Program Canonical citPR {SEL} `{!Uip SEL} I C D :=
  Prost (@citO SEL I C D) (λ k t t', proeq k (of_cit t) (of_cit t')) _ _ _.
Next Obligation.
  split. { by move=> ?. } { move=> ???. by symmetry. }
  { move=> ?????. by etrans. }
Qed.
Next Obligation. move=> *. by eapply proeq_anti. Qed.
Next Obligation.
  move=> ????? t t'. split. { move=> eq ?. by rewrite eq. }
  move=> ?. rewrite -(to_of_cit (t:=t)) -(to_of_cit (t:=t')). by f_equiv.
Qed.

Section citPR.
  Context {SEL} {I C : SEL → Type} {D : SEL → ofe}.

  (** Unfold [proeq] over [cita] and [cit] *)
  Lemma cita_proeq : @proeq (citaPR I C D) = λ k ta ta', ta k ≡ ta' k.
  Proof. done. Qed.
  Lemma cit_proeq `{!Uip SEL} :
    @proeq (citPR I C D) = λ k t t', proeq k (of_cit t) (of_cit t').
  Proof. done. Qed.

  (** [Citg] is size-preserving over the inductive arguments
    and [Productive] over the coinductive arguments *)
  #[export] Instance Citg_preserv_productive `{!Uip SEL} {s k} :
    Proper (@proeq (funPR (λ _, citPR I C D)) k ==>
      @proeq_later (_ -pr> _) k ==> (≡) ==> @proeq (citPR I C D) k) (Citg s).
  Proof.
    move=> ?? eq ?? eq' ??<-. rewrite /proeq /= cit_proeq of_cit_unseal in eq.
    apply equiv_dist=> n. apply citi_dist_Forall2.
    rewrite !of_cit_unseal. destruct k as [|k]=>/=; apply citg_Forall2_eq=>//.
    - move=> i. apply (citi_equiv_Forall2 (k:=1)), eq.
    - move=> i. apply (citi_equiv_Forall2 (k:=S (S k))), eq.
    - move=> c. apply (citi_equiv_Forall2 (k:=S k)). apply eq'.
  Qed.

  (** [of_cit] is size-preserving *)
  #[export] Instance of_cit_preserv `{!Uip SEL} : Preserv (@of_cit _ I C D).
  Proof. by move=> ??. Qed.
End citPR.

(** ** Completeness of [cita] and [cit] *)

Section cit_cprost.
  Context {SEL} {I C : SEL → Type} {D : SEL → ofe} `{!Uip SEL}.

  (** Limit over [cita] *)
  Program Definition cita_prolimit (c : prochain (citaPR I C D))
    : citaPR I C D :=
    Cita (c 0).(cita_head) (λ k, (c (S k)).(cita_tail) k) _.
  Next Obligation.
    move=> c. apply (equiv_wfcit' (ts:=λ k, (c k) k))=> k k' ?.
    eapply citi_Forall2_trans; [| |apply (cita_seq_equiv (k:=k))]; [lia|].
    apply citi_equiv_Forall2', (prochain_eq (c:=c)). lia.
  Qed.
  (** Simplify [cita_seq] over [cita_prolimit] *)
  Lemma cita_seq_limit {c k} : cita_prolimit c k = c k k.
  Proof. by case: k. Qed.
  (** [cita] is complete *)
  #[export] Program Instance cita_cprost : Cprost (citaPR I C D) :=
    CPROST cita_prolimit _ _.
  Next Obligation. move=> ?. by case=>/= >. Qed.
  Next Obligation.
    move=> ??? eq k. rewrite !cita_seq_limit. apply (eq k k).
  Qed.

  (** Limit over [cit] *)
  Definition cit_prolimit (c : prochain (citPR I C D)) : citPR I C D :=
    to_cit (prolimit
      (Prochain (λ k, of_cit (c k)) (λ _ _, c.(prochain_eq)))).
  (** [cit] is complete *)
  #[export] Program Instance cit_cprost : Cprost (citPR I C D) :=
    CPROST cit_prolimit _ _.
  Next Obligation.
    move=> c k. by rewrite cit_proeq of_to_cit cita_proeq cita_seq_limit.
  Qed.
  Next Obligation.
    move=> ????. unfold cit_prolimit. (do 2 f_equiv)=>/= ?. by f_equiv.
  Qed.
End cit_cprost.

(** ** [citOF]: [oFunctor] for [cit] *)
Program Definition citOF {SEL} I C (D : SEL → oFunctor) : oFunctor := {|
  oFunctor_car A _ B _ := citO I C (λ s, (D s).(oFunctor_car) A B);
  oFunctor_map _ _ _ _ _ _ _ _ fg :=
    OfeMor (cit_map (λ s, oFunctor_map (D s) fg));
|}.
Next Obligation.
  move=> > [[??][??]][[??][??]][/=??]?/=. f_equiv. solve_proper.
Qed.
Next Obligation. move=>/= *. apply cit_map_id=> >. apply oFunctor_map_id. Qed.
Next Obligation.
  move=>/= *. rewrite cit_map_compose. apply equiv_dist=> ?. f_equiv=> ??.
  apply equiv_dist, oFunctor_map_compose.
Qed.

(** [citOF I C D] is contractive when [D] is contractive *)
#[export] Instance citOF_contractive {SEL I C}
  `{!∀ s, oFunctorContractive (D s)} :
  oFunctorContractive (citOF (SEL:=SEL) I C D).
Proof.
  move=> > ? * ? /=. apply cit_map_ne_gen; [|done]=> ??.
  by apply oFunctor_map_contractive.
Qed.
