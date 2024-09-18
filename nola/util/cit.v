(** * [cit]: Coinductive-inductive set of trees *)

From nola.util Require Export eq order productive.
From iris.algebra Require Export ofe.
Import EqNotations.

Implicit Type SEL : Type.

(** ** [citg]: Generator of [cit] *)

(** [citg]: Generator of [cit] *)
Section citg.
  Context {SEL} (I C D : SEL → Type) (CIT : Type).
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
  Context {SEL} {I C D D' : SEL → Type} {CIT CIT' : Type}.
  Context (R : ∀ s, D s → D' s → Prop) (CITF : CIT → CIT' → Prop).
  Inductive citg_Forall2
    (t : citg I C D CIT) (t' : citg I C D' CIT') : Prop := Citgf2 {
    citgf2_sel : t.(citg_sel) = t'.(citg_sel);
    citgf2_ikids : ∀ i, citg_Forall2
      (t.(citg_ikids) i) (t'.(citg_ikids) (rew citgf2_sel in i));
    citgf2_ckids : ∀ c, CITF
      (t.(citg_ckids) c) (t'.(citg_ckids) (rew citgf2_sel in c));
    citgf2_data :
      R t.(citg_sel) t.(citg_data) (rew eq_sym citgf2_sel in t'.(citg_data));
  }.
End citg_Forall2.
Arguments Citgf2 {_ _ _ _ _ _ _ _ _ _ _}.
Arguments citgf2_sel {_ _ _ _ _ _ _ _ _ _ _}.
Arguments citgf2_ikids {_ _ _ _ _ _ _ _ _ _ _}.
Arguments citgf2_ckids {_ _ _ _ _ _ _ _ _ _ _}.
Arguments citgf2_data {_ _ _ _ _ _ _ _ _ _ _}.

Section citg_Forall2.
  Context {SEL} {I C : SEL → Type}.
  Implicit Type D : SEL → Type.

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

(** ** [citg_map]: Map over [citg] *)

(** [citg_map]: Map over [citg] *)
Section citg_map.
  Context {SEL} {I C D D' : SEL → Type} {CIT CIT' : Type}.
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

  (** [citg_map] is proper *)
  Lemma citg_map_proper
    {D1 D1' D2 D2' CIT1 CIT1' CIT2 CIT2' R R' CITF CITF' f f' g g' t t'} :
    (∀ s d d', R s d d' → R' s (f s d) (f' s d')) →
    (∀ ct ct', CITF ct ct' → CITF' (g ct) (g' ct')) →
    citg_Forall2 R CITF t t' →
      citg_Forall2 R' CITF' (@citg_map _ I C D1 D1' CIT1 CIT1' f g t)
        (@citg_map _ _ _ D2 D2' CIT2 CIT2' f' g' t').
  Proof.
    move=> to to'. elim. move=> [????][????]/=?. subst=>/= ? IH ??.
    apply citg_Forall2_eq=>//. { move=> c. by apply to'. } { by apply to. }
  Qed.
  #[export] Instance citg_map_proper' {D D' CIT CIT' R R' CITF CITF'} :
    Proper (forall_relation (λ s, (R s ==> R' s)) ==> (CITF ==> CITF') ==>
      citg_Forall2 R CITF ==> citg_Forall2 R' CITF')
      (@citg_map _ I C D D' CIT CIT').
  Proof. move=> ????????. by apply citg_map_proper. Qed.

  (** [citg_map] over an identity function *)
  Lemma citg_map_id {D D' CIT CIT' R CITF f g t} :
    (∀ s d, R _ (f s d) d) → (∀ ct, CITF (g ct) ct) →
    citg_Forall2 R CITF (@citg_map _ I C D D' CIT CIT' f g t) t.
  Proof.
    elim: t=> ?? IH *. apply citg_Forall2_eq=>//. move=> ?. by apply IH.
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
  Context {SEL} {I C D : SEL → Type} {CIT A : Type}.
  Context (f : ∀ s, (I s → A) → (C s → CIT) → D s → A).
  Fixpoint citg_fold (t : citg I C D CIT) : A :=
    f t.(citg_sel) (λ i, citg_fold (t.(citg_ikids) i)) t.(citg_ckids)
      t.(citg_data).
End citg_fold.

(** ** [citi]: Iteration of [citg] *)
Section citi.
  Context {SEL} (I C D : SEL → Type).
  Fixpoint citi (n : nat) : Type :=
    match n with 0 => () | S n' => citg I C D (citi n') end.
End citi.

(** ** [citi_Forall2]: Universal relation between [citi]s *)
Section citi_Forall2.
  Context {SEL} {I C D D' : SEL → Type} (R : ∀ s, D s → D' s → Prop).
  Fixpoint citi_Forall2 {m n} : citi I C D m → citi I C D' n → Prop :=
    match m, n with
    | S _, S _ => citg_Forall2 R citi_Forall2
    | _, _ => λ _ _, True
    end.
End citi_Forall2.

Section citi_Forall2.
  Context {SEL} {I C : SEL → Type}.
  Implicit Type D : SEL → Type.

  (** [citi_Forall2] is monotone *)
  Lemma citi_Forall2_mono {D D' m n R R'} :
    (∀ s, R s ⊑ R' s) → @citi_Forall2 _ I C D D' R m n ⊑ citi_Forall2 R'.
  Proof.
    move=> to. move: n. elim: m; [done|]=>/= m IH. case; [done|]=> ?.
    apply citg_Forall2_mono; [done|]. apply IH.
  Qed.

  (** [citi_Forall2] preserves reflexivity *)
  #[export] Instance citi_Forall2_refl `{!∀ s, @Reflexive (D s) (R s)} {n} :
    Reflexive (@citi_Forall2 _ I C _ _ R n _).
  Proof. elim: n; [done|]=>/= ??. exact _. Qed.

  (** Flip [citi_Forall2] *)
  Lemma citi_Forall2_flip {D D' R m n t t'} :
    citi_Forall2 (λ s, flip (R s)) t' t → @citi_Forall2 _ I C D D' R m n t t'.
  Proof.
    move: n t t'. elim: m; [done|]=> ? IH. case; [done|]=>/= ??? all.
    apply citg_Forall2_flip. move: all. apply citg_Forall2_mono'=> ???.
    by apply IH.
  Qed.
  (** [citi_Forall2] preserves symmetricity *)
  #[export] Instance citi_Forall2_sym `{!∀ s, @Symmetric (D s) (R s)} {n} :
    Symmetric (@citi_Forall2 _ I C _ _ R n _).
  Proof. elim: n; [done|]=>/= ??. exact _. Qed.

  (** Compose [citi_Forall2]s *)
  Lemma citi_Forall2_compose {D D' D'' R R' R'' l m n t t' t''} :
    (∀ s d d' d'', R s d d' → R' s d' d'' → R'' s d d'') →
    min l n ≤ m → @citi_Forall2 _ I C D D' R l m t t' →
    citi_Forall2 (D':=D'') (n:=n) R' t' t'' → citi_Forall2 R'' t t''.
  Proof.
    move=> ?. move: n m t t' t''. elim: l; [done|]=> l IH. case; [done|]=> n.
    case; [lia|]=>/= m ??????. eapply citg_Forall2_compose=>//. move=> ???.
    apply IH. lia.
  Qed.
  (** [citi_Forall2] preserves transitivity *)
  #[export] Instance citi_Forall2_trans `{!∀ s, @Transitive (D s) (R s)} {n} :
    Transitive (@citi_Forall2 _ I C _ _ R n _).
  Proof. elim: n; [done|]=>/= ??. exact _. Qed.

  (** [citi_Forall2] preserves equivalence-ness *)
  #[export] Instance citi_Forall2_equivalence
    `{!∀ s, @Equivalence (D s) (R s)} {n} :
    Equivalence (@citi_Forall2 _ I C _ _ R n _).
  Proof. split; exact _. Qed.

  (** Convert universally quantified [citg_Forall2], under UIP over [SEL] *)
  Lemma citi_Forall2_forall `{!Uip SEL, !Inhabited A} {D D' R m n t t'} :
    (∀ a : A, @citi_Forall2 _ I C D D' (R a) m n t t') →
      citi_Forall2 (λ _ d d', ∀ a, R a _ d d') t t'.
  Proof.
    move: n t t'. elim: m; [done|]=> ? IH. case; [done|]=>/= ???.
    move /citg_Forall2_forall. apply citg_Forall2_mono'=> ?? +. apply IH.
  Qed.
End citi_Forall2.

(** ** [citi_map]: Map over [citi] *)

Section citi_map.
  Context {SEL} {I C D D' : SEL → Type}.
  Context (f : ∀ s, D s → D' s).
  (** [citi_map]: Map over [citi] *)
  Fixpoint citi_map {n} : citi I C D n → citi I C D' n :=
    match n with S _ => citg_map f citi_map | 0 => id end.
End citi_map.

Section citi_map.
  Context {SEL} {I C : SEL → Type}.

  (** [citi_map] is proper *)
  Lemma citi_map_proper {D1 D1' D2 D2' R R' f f' n t t'} :
    (∀ s d d', R s d d' → R' s (f s d) (f' s d')) →
    citi_Forall2 R t t' →
      citi_Forall2 R' (@citi_map _ I C D1 D1' f n t)
        (@citi_map _ _ _ D2 D2' f' n t').
  Proof.
    move=> ?. move: t t'. elim: n; [done|]=>/= ????. by apply citg_map_proper.
  Qed.
  #[export] Instance citi_map_proper' {D D' R R' n}
    `{!∀ s, Proper (R s ==> R' s) (f s)} :
    Proper (citi_Forall2 R ==> citi_Forall2 R') (@citi_map _ I C D D' f n).
  Proof. move=> ??. by apply citi_map_proper. Qed.

  (** [citi_map] over an identity function *)
  Lemma citi_map_id {D D' R f n t} :
    (∀ s d, R _ (f s d) d) → citi_Forall2 R (@citi_map _ I C D D' f n t) t.
  Proof. move=> ?. move: t. elim: n; [done|]=>/= ???. by apply citg_map_id. Qed.

  (** [citi_map] over [∘] *)
  Lemma citi_map_compose {D D' D'' f f' n t} `{!∀ s, Reflexive (R s)} :
    citi_Forall2 R (citi_map f' (@citi_map _ I C D D' f n t))
      (citi_map (D':=D'') (λ s, f' s ∘ f s) t).
  Proof.
    move: t. elim: n; [done|]=>/= ?? t. elim: t=>/= *. by apply citg_Forall2_eq.
  Qed.
End citi_map.

(** ** [wfcit]: Approximation sequence of [citi] is well-formed *)
Section wfcit.
  Context {SEL} {I C D : SEL → Type}.
  CoInductive wfcit
    (* Head *) (t : citi I C D 1)
    (* Tail *) (tl : ∀ n, citi I C D (S (S n))) : Prop := Wfcit {
    (** Selector equality *)
    wfc_sel : ∀ n, t.(citg_sel) = (tl n).(citg_sel);
    (** On inductive children *)
    wfc_ikids : ∀ i, wfcit (t.(citg_ikids) i)
      (λ n, (tl n).(citg_ikids) (rew wfc_sel n in i));
    (** On coinductive children *)
    wfc_ckids : ∀ c, wfcit ((tl 0).(citg_ckids) (rew wfc_sel 0 in c))
      (λ n, (tl (S n)).(citg_ckids) (rew wfc_sel (S n) in c));
    (** Data equality *)
    wfc_data : ∀ n,
      t.(citg_data) = rew eq_sym (wfc_sel n) in (tl n).(citg_data);
  }.
End wfcit.
Add Printing Constructor wfcit.
Arguments Wfcit {_ _ _ _ _ _}. Arguments wfc_sel {_ _ _ _ _ _}.
Arguments wfc_ikids {_ _ _ _ _ _}. Arguments wfc_ckids {_ _ _ _ _ _}.
Arguments wfc_data {_ _ _ _ _ _}.

Section wfcit.
  Context {SEL} {I C D : SEL → Type}.

  (** [wfcit] into equality between the head and an element in the tail *)
  Lemma wfcit_head_tail_eq {t tl} `{!∀ s, Reflexive (R s)} n :
    @wfcit _ I C D t tl → citi_Forall2 R t (tl n).
  Proof.
    move: tl. elim: t=>/= s ti IH tc d tl[/=sel ?? deq].
    apply (Citgf2 (t:=Citg s _ _ _) (sel n)); [|done|by rewrite (deq n)].
    move=>/= i. by apply (IH i (λ n, _)).
  Qed.
  (** [wfcit] into equality between elements in the tail *)
  Lemma wfcit_tail_tail_eq {t tl} `{!∀ s, Reflexive (R s)} m n :
    @wfcit _ I C D t tl → citi_Forall2 R (tl m) (tl n).
  Proof.
    move=> wf.
    suff: citi_Forall2 (λ _, (=)) (tl m) (tl n).
    { by apply citi_Forall2_mono=> ???->. }
    wlog: m n / m < n.
    { move=> goal. have : m < n ∨ m = n ∨ m > n by lia.
      case=> [?|[?|gt]]; [by apply goal|by subst|]. apply citi_Forall2_flip.
      move: (goal _ _ gt). by apply citi_Forall2_mono=> ????. }
    case: n; [lia|]=> n lt /=. move: m n lt t tl wf. fix FIX 1=> m n lt.
    elim=>/= s ti IH tc d tl [/=sel wfi wfc deq].
    apply (Citgf2 (eq_trans (eq_sym (sel m)) (sel (S n)))).
    - move=> i. rewrite -rew_compose -{1}(rew_sym_r (sel m) i).
      by apply (IH (rew eq_sym (sel m) in i) (λ _, _)).
    - move=> c. have := wfc (rew eq_sym (sel m) in c). rewrite -rew_compose.
      rewrite -{3}(rew_sym_r (sel m) c). destruct m as [|m'].
      { apply (wfcit_head_tail_eq (tl:=λ _, _)). }
      destruct n as [|n']; [lia|]. apply FIX. lia.
    - apply rew_swap. rewrite -rew_compose -(deq m) (deq (S n)).
      by rewrite rew_sym_r.
  Qed.

  (** [wfcit] from equalities, under UIP over [SEL] *)
  Lemma forall_eq_wfcit `{!Uip SEL} {t tl} :
    (∀ n, citi_Forall2 (λ _, (=)) t (tl n)) →
    (∀ m n, m < n → citi_Forall2 (λ _, (=)) (tl m) (tl n)) →
      @wfcit _ I C D t tl.
  Proof.
    move: t tl. cofix FIX. move=> [????]?/= hteq tteq.
    apply (Wfcit (λ n, (hteq n).(citgf2_sel)))=>/=.
    - move=> i. apply FIX. { move=> n. apply hteq. }
      move=> m n lt. case: (tteq m n lt)=> sel F _ _.
      move: (F (rew (hteq m).(citgf2_sel) in i)). rewrite rew_compose.
      by rewrite (proof_irrel (eq_trans _ _) (hteq _).(citgf2_sel)).
    - move=> c. apply FIX.
      { move=> n. have lt : 0 < S n by lia. case: (tteq 0 (S n) lt)=> ? _ F _.
        move: (F (rew (hteq 0).(citgf2_sel) in c)). rewrite rew_compose.
        by rewrite (proof_irrel (eq_trans _ _) (hteq _).(citgf2_sel)). }
      move=> m n lt. have lt' : S m < S n by lia. case: (tteq (S m) (S n) lt').
      move=> ? _ F _. move: (F (rew (hteq (S m)).(citgf2_sel) in c)).
      by rewrite rew_compose (proof_irrel (eq_trans _ _) (hteq _).(citgf2_sel)).
    - move=> ?. apply hteq.
  Qed.
  Lemma forall_eq_wfcit' `{!Uip SEL} {ts} :
    (∀ m n, m < n → citi_Forall2 (λ _, (=)) (ts m) (ts n)) →
      @wfcit _ I C D (ts 0) (λ n, ts (S n)).
  Proof. move=> F. apply forall_eq_wfcit=> *; apply F; lia. Qed.
End wfcit.

(** ** [cit]: Coinductive-inductive tree *)
Section cit.
  Context {SEL} (I C D : SEL → Type).
  (** [cita]: Coinductive-inductive tree by approximation *)
  #[projections(primitive)]
  Record cita := Cita {
    cita_head : citi I C D 1;
    cita_tail : ∀ n, citi I C D (S (S n));
    cita_wf : wfcit cita_head cita_tail;
  }.
  (** [cit]: Coinductive-inductive tree *)
  Definition cit := citg I C D cita.
End cit.
Add Printing Constructor cita.
Arguments Cita {_ _ _ _}. Arguments cita_head {_ _ _ _}.
Arguments cita_tail {_ _ _ _}. Arguments cita_wf {_ _ _ _}.

Section cit.
  Context {SEL} {I C D : SEL → Type}.

  (** Whole sequence of [cita] *)
  Definition cita_seq (ta : cita I C D) (n : nat) : citi I C D (S n) :=
    match n with 0 => ta.(cita_head) | S n' => ta.(cita_tail) n' end.

  (** Elements of [cita] are equal *)
  Lemma cita_seq_eq `{!∀ s, Reflexive (R s)} {ta : cita I C D} {m n} :
    citi_Forall2 R (cita_seq ta m) (cita_seq ta n).
  Proof.
    suff: citi_Forall2 (λ _, (=)) (cita_seq ta m) (cita_seq ta n).
    { by apply citi_Forall2_mono=> ???->. }
    case: m=> [|m]; case: n=> [|n]=>//.
    - simpl. apply wfcit_head_tail_eq, cita_wf.
    - apply citi_Forall2_flip=>/=. apply wfcit_head_tail_eq, cita_wf.
    - simpl. eapply wfcit_tail_tail_eq, cita_wf.
  Qed.
End cit.
Coercion cita_seq : cita >-> Funclass.

(** ** Relation between [cita]s and [cit]s *)
Section cita_rel.
  Context {SEL} {I C : SEL → Type}.
  Implicit Type D : SEL → Type.

  (** Universal relation between [cita]s *)
  Definition cita_Forall2 {D D'} (R : ∀ s, D s → D' s → Prop)
    (ta : cita I C D) (ta' : cita I C D') : Prop :=
    ∀ n, citi_Forall2 R (ta n) (ta' n).
  (** Universal relation between [cit]s *)
  Definition cit_Forall2 {D D'} (R : ∀ s, D s → D' s → Prop)
    : cit I C D → cit I C D' → Prop :=
    citg_Forall2 R (cita_Forall2 R).

  (** [cita_Forall2] is monotone *)
  #[export] Instance cita_Forall2_mono {D D'} : Mono (@cita_Forall2 D D').
  Proof. move=> ?? to ????. by apply (citi_Forall2_mono to). Qed.

  (** [cita_Forall2] preserves reflexivity *)
  #[export] Instance cita_Forall2_refl `{!∀ s, @Reflexive (D s) (R s)} :
    Reflexive (cita_Forall2 R).
  Proof. by move=> ??. Qed.

  (** Flip [cita_Forall2] *)
  Lemma cita_Forall2_flip {D D' R ta ta'} :
    cita_Forall2 (λ s, flip (R s)) ta' ta → @cita_Forall2 D D' R ta ta'.
  Proof. move=> ??. by apply citi_Forall2_flip. Qed.
  (** [cita_Forall2] preserves symmetricity *)
  #[export] Instance cita_Forall2_sym `{!∀ s, @Symmetric (D s) (R s)} :
    Symmetric (cita_Forall2 R).
  Proof. move=> ????. by symmetry. Qed.

  (** Compose [cita_Forall2]s *)
  Lemma cita_Forall2_compose {D D' D'' R R' R'' ta ta' ta''} :
    (∀ s d d' d'', R s d d' → R' s d' d'' → R'' s d d'') →
    @cita_Forall2 D D' R ta ta' → cita_Forall2 (D':=D'') R' ta' ta'' →
      cita_Forall2 R'' ta ta''.
  Proof.
    move=> ? F F' ?.
    eapply citi_Forall2_compose; [done| |by apply F|by apply F']. lia.
  Qed.
  (** [cita_Forall2] preserves transitivity *)
  #[export] Instance cita_Forall2_trans `{!∀ s, @Transitive (D s) (R s)} :
    Transitive (cita_Forall2 R).
  Proof. move=> ??????. by etrans. Qed.

  (** [cita_Forall2] preserves equivalence-ness *)
  #[export] Instance cita_Forall2_equivalence
    `{!∀ s, @Equivalence (D s) (R s)} : Equivalence (cita_Forall2 R).
  Proof. split; exact _. Qed.

  (** Convert universally quantified [citg_Forall2], under UIP over [SEL] *)
  Lemma cita_Forall2_forall `{!Uip SEL, !Inhabited A} {D D' R ta ta'} :
    (∀ a : A, @cita_Forall2 D D' (R a) ta ta') →
      cita_Forall2 (λ _ d d', ∀ a, R a _ d d') ta ta'.
  Proof. move=> F ?. apply citi_Forall2_forall=> ?. apply F. Qed.

  (** [cit_Forall2] is monotone *)
  #[export] Instance cit_Forall2_mono {D D'} : Mono (@cit_Forall2 D D').
  Proof. move=> ???. apply citg_Forall2_mono; [done|]. by apply mono. Qed.

  (** [cit_Forall2] preserves reflexivity *)
  #[export] Instance cit_Forall2_refl `{!∀ s, @Reflexive (D s) (R s)} :
    Reflexive (cit_Forall2 R).
  Proof. exact _. Qed.

  (** Flip [cit_Forall2] *)
  Lemma cit_Forall2_flip {D D' R t t'} :
    cit_Forall2 (λ s, flip (R s)) t' t → @cit_Forall2 D D' R t t'.
  Proof.
    move=> F. apply citg_Forall2_flip. move: F. apply citg_Forall2_mono'.
    move=> ?? +. exact cita_Forall2_flip.
  Qed.
  (** [cit_Forall2] preserves symmetricity *)
  #[export] Instance cit_Forall2_sym `{!∀ s, @Symmetric (D s) (R s)} :
    Symmetric (cit_Forall2 R).
  Proof. exact _. Qed.

  (** Compose [cit_Forall2]s *)
  Lemma cit_Forall2_compose {D D' D'' R R' R'' t t' t''} :
    (∀ s d d' d'', R s d d' → R' s d' d'' → R'' s d d'') →
    @cit_Forall2 D D' R t t' → cit_Forall2 (D':=D'') R' t' t'' →
      cit_Forall2 R'' t t''.
  Proof.
    move=> F F'. eapply citg_Forall2_compose=>// ???.
    by apply cita_Forall2_compose.
  Qed.
  (** [cit_Forall2] preserves transitivity *)
  #[export] Instance cit_Forall2_trans `{!∀ s, @Transitive (D s) (R s)} :
    Transitive (cit_Forall2 R).
  Proof. exact _. Qed.

  (** [cit_Forall2] preserves equivalence-ness *)
  #[export] Instance cit_Forall2_equivalence
    `{!∀ s, @Equivalence (D s) (R s)} : Equivalence (cit_Forall2 R).
  Proof. exact _. Qed.

  (** Convert universally quantified [citg_Forall2], under UIP over [SEL] *)
  Lemma cit_Forall2_forall `{!Uip SEL, !Inhabited A} {D D' R t t'} :
    (∀ a : A, @cit_Forall2 D D' (R a) t t') →
      cit_Forall2 (λ _ d d', ∀ a, R a _ d d') t t'.
  Proof.
    move=> /citg_Forall2_forall. apply citg_Forall2_mono'=> ?? +.
    apply cita_Forall2_forall.
  Qed.
End cita_rel.

(** ** Conversion between [cit] and [cita] *)
Section of_cit.
  Context {SEL} {I C D : SEL → Type}.

  (** [of_cit]: Convert [cit] into [cita] *)
  Program CoFixpoint wf_of_cit (t : cit I C D) :
    wfcit (citg_map (λ _, id) (λ _, ()) t)
      (λ n, citg_map (λ _, id) (λ ta, cita_seq ta n) t) :=
    let: Citg s ti tc d := t in
    Wfcit (λ _, eq_refl) (λ i, wf_of_cit (ti i))
      (λ c, (tc c).(cita_wf)) (λ _, eq_refl).
  Definition of_cit (t : cit I C D) : cita I C D :=
    Cita (citg_map (λ _, id) (λ _, ()) t)
      (λ n, citg_map (λ _, id) (λ ta, cita_seq ta n) t) (wf_of_cit t).

  (** [to_cit]: Convert [cita] into [cit] *)
  Fixpoint to_cit' (t : citi I C D 1) (tl : ∀ n, citi I C D (S (S n)))
    (wf : wfcit t tl) : cit I C D :=
    Citg t.(citg_sel)
      (λ i, to_cit' (t.(citg_ikids) i)
        (λ n, (tl n).(citg_ikids) (rew wf.(wfc_sel) n in i))
        (wf.(wfc_ikids) i))
      (λ c, Cita ((tl 0).(citg_ckids) (rew wf.(wfc_sel) 0 in c))
        (λ n, (tl (S n)).(citg_ckids) (rew wf.(wfc_sel) (S n) in c))
        (wf.(wfc_ckids) c))
      t.(citg_data).
  Definition to_cit (ta : cita I C D) : cit I C D :=
    to_cit' ta.(cita_head) ta.(cita_tail) ta.(cita_wf).

  (** Simplify [to_cit] over [of_cit] *)
  Lemma to_of_cit {t} `{!∀ s, Reflexive (R s), !Reflexive CITF} :
    citg_Forall2 R CITF (to_cit (of_cit t)) t.
  Proof. elim: t=>/= ?????. by apply citg_Forall2_eq. Qed.

  (** Simplify [of_cit] over [to_cit] *)
  Lemma of_to_cit {ta} `{!∀ s, Reflexive (R s), !∀ n, Reflexive (CITF n)} {n} :
    citg_Forall2 R (CITF n) (of_cit (to_cit ta) n) (ta n).
  Proof.
    move: ta=> [t tl wf]/=. case: n=>/=.
    { elim: t tl wf=> ?? IH tc ???/=. apply citg_Forall2_eq=>//.
      { move=> i. apply IH. } { move=> c. by case: (tc c). } }
    move=> n. elim: t tl wf=> ?? IH ???[/=sel ?? deq] /=.
    apply (Citgf2 (t:=Citg _ _ _ _) (sel n))=>/=. { move=> ?. apply IH. }
    { by destruct n. } { by rewrite (deq n). }
  Qed.
End of_cit.

Section of_cit.
  Context {SEL} {I C : SEL → Type}.

  (** [of_cit] is proper *)
  Lemma of_cit_proper {D D' R t t'} :
    @cit_Forall2 _ I C D D' R t t' → cita_Forall2 R (of_cit t) (of_cit t').
  Proof.
    unfold of_cit. elim. move=> [s ti tc d][? ti' tc' d']/=?. subst=>/=.
    move=> Fi IH Fc dR. case=>/=.
    { apply citg_Forall2_eq=>// i. apply (IH i 0). }
    move=> n. apply citg_Forall2_eq=>//. { move=> i. apply (IH i (S _)). }
    move=> ?. apply Fc.
  Qed.

  (** [to_cit] is proper, under UIP over [SEL] *)
  Lemma to_cit_proper {D D' R ta ta'} `{!Uip SEL} :
    @cita_Forall2 _ I C D D' R ta ta' →
    cit_Forall2 R (to_cit ta) (to_cit ta').
  Proof.
    unfold to_cit. move: ta ta'=> [+ + +][+ + +]+.
    elim=> ? ti IH tc d tl [/=sel ???] [s ti' tc' d'] tl' [/=sel' ???] F.
    case: (F 0)=>/= ?. subst=>/= ???. apply citg_Forall2_eq=>//=.
    { move=> i. apply IH=>//=. case=>//= n. case: (F (S n))=>/= ? Fi _ _.
      have := (Fi (rew sel n in i)). rewrite rew_compose.
      by rewrite (proof_irrel (eq_trans _ _) (sel' _)). }
    move=> c n. case: (F (S n))=>/= ? _ Fc _. move: (Fc (rew sel _ in c)).
    destruct n as [|?]=>/=;
      by rewrite rew_compose (proof_irrel (eq_trans _ _) (sel' _)).
  Qed.
End of_cit.

(** ** Map over [cit] and [cita] *)

Section cit_map.
  Context {SEL} {I C D D' : SEL → Type}.

  (** [wfcit] over [citi_map] *)
  Local Lemma wfcit_map' {f t tl tl'} :
    (∀ n, tl' n = citi_map f (tl n)) → wfcit t tl →
      wfcit (@citi_map _ I C D D' f _ t) tl'.
  Proof.
    move: t tl tl'. cofix FIX. move=> [s ti tc d] tl tl' eq [/=sel wfi wfc deq].
    apply (Wfcit (t:=Citg s _ _ _)
      (λ n, rew [λ t, s = t.(citg_sel)]
        eq_sym (eq n) in eq_trans (sel n) (eq_sym citg_sel_map)))=>/=.
    - move=> i. move: (wfi i). apply FIX=> n.
      move: (tl n) (tl' n) (eq n) (sel n)=> [????]???. by subst.
    - move=> c. move: (wfc c). move: (tl 0) (tl' 0) (eq 0) (sel 0)=> [????]???.
      subst=>/=. apply FIX=> n.
      move: (tl (S n)) (tl' (S n)) (eq (S n)) (sel (S n))=> [????]???.
      by subst=>/=.
    - move=> n. move: (tl n) (tl' n) (eq n) (sel n) (deq n)=> [????]????.
      by subst=>/=.
  Qed.
  Lemma wfcit_map {f t tl} :
    wfcit t tl → wfcit (@citi_map _ I C D D' f _ t) (λ n, citi_map f (tl n)).
  Proof. by apply wfcit_map'. Qed.

  (** [cita_map]: Map over [cita] *)
  Definition cita_map
    (f : ∀ s, D s → D' s) (ta : cita I C D) : cita I C D' :=
    Cita (citi_map f ta.(cita_head)) (λ n, citi_map f (ta.(cita_tail) n))
      (wfcit_map ta.(cita_wf)).

  (** [cit_map]: Map over [cit] *)
  Definition cit_map (f : ∀ s, D s → D' s) (t : cit I C D) : cit I C D' :=
    citg_map f (cita_map f) t.
End cit_map.

Section cit_map.
  Context {SEL} {I C : SEL → Type}.

  (** [cita_map] is proper *)
  Lemma cita_map_proper {D1 D1' D2 D2' R R' f f' ta ta'} :
    (∀ s d d', R s d d' → R' s (f s d) (f' s d')) →
    cita_Forall2 R ta ta' →
      cita_Forall2 R' (@cita_map _ I C D1 D1' f ta)
        (@cita_map _ _ _ D2 D2' f' ta').
  Proof. move=> ??. case=> >; by eapply citi_map_proper. Qed.
  #[export] Instance cita_map_proper' {D D' R R'} :
    Proper (forall_relation (λ s, R s ==> R' s) ==>
      cita_Forall2 R ==> cita_Forall2 R') (@cita_map _ I C D D').
  Proof. move=> ?????. by apply cita_map_proper. Qed.

  (** [cita_map] over an identity function *)
  Lemma cita_map_id {D D' R f ta} :
    (∀ s d, R _ (f s d) d) → cita_Forall2 R (@cita_map _ I C D D' f ta) ta.
  Proof. move=> ?. case=> >; by apply citi_map_id. Qed.

  (** [cita_map] over [∘] *)
  Lemma cita_map_compose {D D' D'' f f' ta} `{!∀ s, Reflexive (R s)} :
    cita_Forall2 R (cita_map f' (@cita_map _ I C D D' f ta))
      (cita_map (D':=D'') (λ s, f' s ∘ f s) ta).
  Proof. case=> >; apply citi_map_compose. Qed.

  (** [cita_seq] over [cita_map] *)
  Lemma cita_seq_map {D D' f ta n} :
    @cita_map _ I C D D' f ta n = citi_map f (ta n).
  Proof. by case: n. Qed.

  (** [cit_map] is proper *)
  Lemma cit_map_proper {D1 D1' D2 D2' R R' f f' t t'} :
    (∀ s d d', R s d d' → R' s (f s d) (f' s d')) →
    cit_Forall2 R t t' →
      cit_Forall2 R' (@cit_map _ I C D1 D1' f t)
        (@cit_map _ _ _ D2 D2' f' t').
  Proof.
    move=> ?. apply citg_map_proper; [done|]=> ??. by apply cita_map_proper.
  Qed.
  #[export] Instance cit_map_proper' {D D' R R'} :
    Proper (forall_relation (λ s, R s ==> R' s) ==>
      cit_Forall2 R ==> cit_Forall2 R') (@cit_map _ I C D D').
  Proof. move=> ?????. by apply cit_map_proper. Qed.

  (** [cit_map] over an identity function *)
  Lemma cit_map_id {D D' R f t} :
    (∀ s d, R _ (f s d) d) → cit_Forall2 R (@cit_map _ I C D D' f t) t.
  Proof. move=> ?. apply citg_map_id; [done|]=> ?. by apply cita_map_id. Qed.

  (** [cit_map] over [∘] *)
  Lemma cit_map_compose {D D' D'' f f' t} `{!∀ s, Reflexive (R s)} :
    cit_Forall2 R (cit_map f' (@cit_map _ I C D D' f t))
      (cit_map (D':=D'') (λ s, f' s ∘ f s) t).
  Proof.
    elim: t=>/= ?????. apply citg_Forall2_eq=>// ?. apply cita_map_compose.
  Qed.

  (** [of_cit] over [cit_map] *)
  Lemma of_cit_map {D D' f t} `{!∀ s, Reflexive (R s)} :
    cita_Forall2 R (of_cit (@cit_map _ I C D D' f t)) (cita_map f (of_cit t)).
  Proof.
    suff: cita_Forall2 (λ _, (=))
      (of_cit (@cit_map _ I C D D' f t)) (cita_map f (of_cit t)).
    { by apply cita_Forall2_mono=> ???->. }
    unfold of_cit. case=>/=.
    { etrans; [apply citg_map_compose|].
      by etrans; [|symmetry; apply citg_map_compose]. }
    move=> n. etrans; [apply citg_map_compose|].
    etrans; [|symmetry; apply citg_map_compose].
    eapply (citg_map_proper (R:=λ _, eq) (CITF:=eq))=>//=.
    { by move=>/= ???->. } { move=> ??->. by case: n=>/=. }
  Qed.
End cit_map.

(** ** [cit_fold]: Fold [cit] *)
Definition cit_fold {SEL} {I C D : SEL → Type} {A : Type}
  (f : ∀ s, (I s → A) → (C s → cit I C D) → D s → A) :=
  citg_fold (λ s ri tc d, f s ri (λ c, to_cit (tc c)) d).

(** ** Productivity structure for [cita] and [cit] *)

(** [citaPR]: Productivity structure for [cita] *)
Definition cita_proeq {SEL I C D}
  (n : nat) (ta ta' : @cita SEL I C D) : Prop :=
  citi_Forall2 (λ _, (=)) (ta n) (ta' n).
#[export] Instance cita_proeq_equivalence {SEL I C D n} :
  Equivalence (@cita_proeq SEL I C D n).
Proof.
  unfold cita_proeq. split. { by move=> ?. }
  { move=> ???. by symmetry. } { move=> ?????. by etrans. }
Qed.
Program Canonical citaPR {SEL} I C D :=
  Prost (@cita SEL I C D) cita_proeq _ _.
Next Obligation.
  move=> ???? m n ta ta' ? F.
  have F' : citi_Forall2 (λ _, (=)) (ta n) (ta m) by eapply cita_seq_eq.
  have F'' : citi_Forall2 (λ _, (=)) (ta' m) (ta' n) by eapply cita_seq_eq.
  eapply (citi_Forall2_compose (R':=λ _, (eq))); [| |exact F'|
    eapply citi_Forall2_compose; [| |exact F|exact F'']]; try lia; naive_solver.
Qed.

(** [citPR]: Productivity structure for [cit] *)
Definition cit_proeq {SEL I C D} (n : nat) (t t' : @cit SEL I C D) :=
  cita_proeq n (of_cit t) (of_cit t').
#[export] Instance cit_proeq_equivalence {SEL I C D n} :
  Equivalence (@cit_proeq SEL I C D n).
Proof.
  unfold cit_proeq. split. { by move=> ?. }
  { move=> ???. by symmetry. } { move=> ?????. by etrans. }
Qed.
Program Canonical citPR {SEL} I C D :=
  Prost (@cit SEL I C D) cit_proeq _ _.
Next Obligation. move=> *. by eapply proeq_anti. Qed.

Section citPR.
  Context {SEL} {I C : SEL → Type}.
  Implicit Type D : SEL → Type.

  (** [cita_proeq] is proper *)
  Lemma cita_proeq_proper' {D n} :
    Proper (cita_Forall2 (λ _, (=)) ==> cita_Forall2 (λ _, (=)) ==> (→))
      (@cita_proeq _ I C D n).
  Proof.
    move=> ?? eq ?? eq' ?. etrans; [symmetry; exact (eq n)|].
    by etrans; [|exact (eq' n)].
  Qed.
  #[export] Instance cita_proeq_proper {D n} :
    Proper (cita_Forall2 (λ _, (=)) ==> cita_Forall2 (λ _, (=)) ==> (↔))
      (@cita_proeq _ I C D n).
  Proof. move=> ??????. split; by apply cita_proeq_proper'. Qed.

  (** [cit_proeq] is proper *)
  Lemma cit_proeq_proper' {D n} :
    Proper (cit_Forall2 (λ _, (=)) ==> cit_Forall2 (λ _, (=)) ==> (→))
      (@cit_proeq SEL I C D n).
  Proof. move=> ??????. apply cita_proeq_proper'; by apply of_cit_proper. Qed.
  #[export] Instance cit_proeq_proper {D n} :
    Proper (cit_Forall2 (λ _, (=)) ==> cit_Forall2 (λ _, (=)) ==> (↔))
      (@cit_proeq SEL I C D n).
  Proof. move=> ??????. split; by apply cit_proeq_proper'. Qed.

  (** Simplify [proeqa] over [cita] *)
  Lemma cita_proeqa {D ta ta'} `{!∀ s, Reflexive (R s)} :
    proeqa ta ta' → @cita_Forall2 _ I C D _ R ta ta'.
  Proof. move=> E n. move: (E n). by apply citi_Forall2_mono=> ???->. Qed.

  (** Simplify [proeqa] over [cit], under UIP over [SEL] *)
  Lemma cit_proeqa {D t t'} `{!Uip SEL, !∀ s, Reflexive (R s)} :
    proeqa t t' → @cit_Forall2 _ I C D _ R t t'.
  Proof.
    move=> E.
    suff: cit_Forall2 (λ _, (=)) t t' by apply cit_Forall2_mono=> ???->.
    etrans; [symmetry; exact to_of_cit|]. etrans; [|exact to_of_cit].
    by apply to_cit_proper.
  Qed.

  (** [Citg] is [Preserv] over the inductive arguments
    and [Productive] over the coinductive arguments *)
  #[export] Instance Citg_preserv_productive {D s n} :
    Proper (@proeq (funPR (λ _, cit _ _ _)) n ==>
      proeq_later n ==> (=) ==> @proeq (cit I C D) n)
      (Citg s).
  Proof.
    move=> ????????<-. rewrite /= /cit_proeq /of_cit /cita_proeq /=.
    destruct n as [|?]=>/=; by apply citg_Forall2_eq.
  Qed.

  (** [of_cit] is [Preserv] *)
  #[export] Instance of_cit_preserv {D} : Preserv (@of_cit _ I C D).
  Proof. by move=> ??. Qed.

  (** [cit_map] is [Preserv] *)
  #[export] Instance cit_map_preserv {D D' f} :
    Preserv (@cit_map _ I C D D' f).
  Proof.
    move=> ???. rewrite /proeq /= /cit_proeq !of_cit_map.
    rewrite /cita_proeq !cita_seq_map. by apply citi_map_proper=> ???->.
  Qed.
End citPR.

(** ** Completeness of [cit], under UIP over [SEL] *)

Section cit_cprost.
  Context {SEL} {I C D : SEL → Type} `{!Uip SEL}.

  (** Limit over [cita] *)
  Program Definition cita_limit (c : prochain (cita I C D)) : cita I C D :=
    Cita (c 0).(cita_head) (λ n, (c (S n)).(cita_tail) n) _.
  Next Obligation.
    move=> c. apply (forall_eq_wfcit' (ts:=λ n, (c n) n))=> m n ?.
    have F : proeq m (c m) (c n) by apply prochain_eq; lia.
    have F' : citi_Forall2 (λ _, (=)) (c n m) (c n n) by apply cita_seq_eq.
    eapply citi_Forall2_compose; [| |exact F|exact F']; [naive_solver|lia].
  Qed.
  (** Simplify [cita_seq] over [cita_limit] *)
  Lemma cita_seq_limit {c n} : cita_limit c n = c n n.
  Proof. by case: n. Qed.
  (** [cita] is complete *)
  #[export] Program Instance cita_cprost : Cprost (cita I C D) :=
    CPROST cita_limit _.
  Next Obligation. move=> ??. by rewrite /= /cita_proeq cita_seq_limit. Qed.

  (** Limit over [cit] *)
  Definition cit_limit (c : prochain (cit I C D)) : cit I C D :=
    to_cit (cita_limit (Prochain (λ n, of_cit (c n)) c.(prochain_eq))).
  (** [cit] is complete *)
  #[export] Program Instance cit_cprost : Cprost (cit I C D) :=
    CPROST cit_limit _.
  Next Obligation.
    move=> c n. rewrite /= /cit_proeq /cita_proeq. etrans; [exact of_to_cit|].
    by rewrite cita_seq_limit.
  Qed.
End cit_cprost.

(** ** OFE for [cita] and [citg] *)

Section citgO.
  Context {SEL} {I C : SEL → Type} {D : SEL → ofe}.

  (** Distance for [cita] *)
  Local Instance cita_dist : Dist (cita I C D) :=
    λ n, cita_Forall2 (λ _, (≡{n}≡)).

  (** Equivalence for [cita] *)
  Local Instance cita_equiv : Equiv (cita I C D) :=
    λ t t', ∀ n, cita_dist n t t' (** Trick to avoid UIP *).

  (** OFE mixin of [cita] *)
  Lemma cita_ofe_mixin : OfeMixin (cita I C D).
  Proof.
    split; [done|exact _|]=> ???? F ?. move: F. apply cita_Forall2_mono.
    move=> ????. by eapply dist_lt.
  Qed.
  (** OFE of [cita] *)
  Canonical citaO : ofe := Ofe (cita I C D) cita_ofe_mixin.

  Context {CIT : ofe}.

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
End citgO.
Arguments citaO {_} _ _ _. Arguments citgO {_} _ _ _ _.

Section citgO.
  Context {SEL} {I C : SEL → Type}.
  Implicit Type (D : SEL → ofe) (CIT A : ofe).

  (** Rewrite [dist] and [equiv] over [cita] and [citg] *)
  Lemma cita_dist_eq {D n} {ta ta' : cita I C D} :
    (ta ≡{n}≡ ta') = cita_Forall2 (λ _, (≡{n}≡)) ta ta'.
  Proof. done. Qed.
  Lemma cita_equiv_eq {D} {ta ta' : cita I C D} :
    (ta ≡ ta') = ∀ n, cita_Forall2 (λ _, (≡{n}≡)) ta ta'.
  Proof. done. Qed.
  Lemma citg_dist_eq {D CIT n} {t t' : citg I C D CIT} :
    (t ≡{n}≡ t') = citg_Forall2 (λ _, (≡{n}≡)) (≡{n}≡) t t'.
  Proof. done. Qed.
  Lemma citg_equiv_eq {D CIT} {t t' : citg I C D CIT} :
    (t ≡ t') = ∀ n, citg_Forall2 (λ _, (≡{n}≡)) (≡{n}≡) t t'.
  Proof. done. Qed.

  (** [cita I C D] is discrete if [D] is discrete *)
  #[export] Instance cita_discrete `{!∀ s, OfeDiscrete (D s)} :
    OfeDiscrete (cita I C D).
  Proof.
    move=> ?? E ? n. move: (E n).
    by apply citi_Forall2_mono=> ??? /discrete_0/equiv_dist.
  Qed.
  (** [citg I C D CIT] is discrete if [D] and [CIT] are discrete *)
  #[export] Instance citg_discrete {D CIT}
    `{!∀ s, OfeDiscrete (D s), !OfeDiscrete CIT} : OfeDiscrete (citg I C D CIT).
  Proof.
    move=> ?? + ?.
    by apply citg_Forall2_mono; [move=> ?|]=> ?? /discrete_0/equiv_dist.
  Qed.

  (** [Citg] is non-expansive *)
  #[export] Instance Citg_ne {D CIT s n} :
    Proper (pointwise_relation _ (≡{n}≡) ==> pointwise_relation _ (≡{n}≡) ==>
      (≡{n}≡) ==> (≡{n}≡)) (@Citg _ I C D CIT s).
  Proof. move=> ?????????. by apply citg_Forall2_eq. Qed.
  #[export] Instance Citg_proper {D CIT s} :
    Proper (pointwise_relation _ (≡) ==> pointwise_relation _ (≡) ==>
      (≡) ==> (≡)) (@Citg _ I C D CIT s).
  Proof.
    move=> ?? eqi ?? eqc ?? eqd n. apply citg_Forall2_eq=>/= >.
    { apply eqi. } { by apply equiv_dist. } { by apply equiv_dist. }
  Qed.

  (** [Citg] preserves discreteness *)
  #[export] Instance Citg_discrete {D CIT s ti tc d}
    `{!∀ i, Discrete (ti i), !∀ c, Discrete (tc c), !Discrete d} :
    Discrete (@Citg _ I C D CIT s ti tc d).
  Proof.
    move=> [????][/=?]. subst=>/= Ei Ec deq n. apply citg_Forall2_eq.
    - move=> i. move: (Ei i)=>/(discrete_0 (ti i)) Ei'. apply Ei'.
    - move=> c. by move: (Ec c)=>/discrete_0/equiv_dist.
    - by move: deq=> /discrete_0/equiv_dist.
  Qed.

  (** [citg_sel] is non-expansive *)
  Definition cit_sel_ne {D CIT n} {t t' : citg I C D CIT}
    (eqv : t ≡{n}≡ t') : t.(citg_sel) = t'.(citg_sel) := eqv.(citgf2_sel).
  (** [citg_ikids] is non-expansive *)
  Lemma citg_ikids_ne {D CIT n} {t t' : citg I C D CIT} {i} (eqv : t ≡{n}≡ t') :
    t.(citg_ikids) i ≡{n}≡ t'.(citg_ikids) (rew cit_sel_ne eqv in i).
  Proof. apply eqv. Qed.
  (** [citg_ckids] is non-expansive *)
  Lemma citg_ckids_ne {D CIT n} {t t' : citg I C D CIT} {c} (eqv : t ≡{n}≡ t') :
    t.(citg_ckids) c ≡{n}≡ t'.(citg_ckids) (rew cit_sel_ne eqv in c).
  Proof. apply eqv. Qed.
  (** [citg_data] is non-expansive *)
  Lemma cit_data_ne {D CIT n} {t t' : citg I C D CIT} (eqv : t ≡{n}≡ t') :
    t.(citg_data) ≡{n}≡ rew eq_sym (cit_sel_ne eqv) in t'.(citg_data).
  Proof. apply eqv. Qed.

  (** [of_cit] is non-expansive *)
  #[export] Instance of_cit_ne {D} : NonExpansive (@of_cit _ I C D).
  Proof. move=> ????. by apply of_cit_proper. Qed.
  #[export] Instance of_cit_equiv {D} : Proper ((≡) ==> (≡)) (@of_cit _ I C D).
  Proof. apply ne_proper, _. Qed.

  (** [to_cit] is non-expansive, under UIP over [SEL] *)
  #[export] Instance to_cit_ne {D} `{!Uip SEL} : NonExpansive (@to_cit _ I C D).
  Proof. move=> ????. by apply to_cit_proper. Qed.
  #[export] Instance to_cit_equiv {D} `{!Uip SEL} :
    Proper ((≡) ==> (≡)) (@to_cit _ I C D).
  Proof. apply ne_proper, _. Qed.

  (** Simplify [to_cit] over [of_cit] under [≡] *)
  Lemma to_of_cit' {D t} : to_cit (@of_cit _ I C D t) ≡ t.
  Proof. move=> ?. apply to_of_cit. Qed.

  (** [cit_map] is non-expansive *)
  #[export] Instance cit_map_ne_gen {D D' n} :
    Proper (forall_relation (λ _, (≡{n}≡) ==> (≡{n}≡)) ==>
      (≡{n}≡) ==> (≡{n}≡)) (@cit_map _ I C D D').
  Proof. move=> ?? eqv ??. apply cit_map_proper, eqv. Qed.
  #[export] Instance cit_map_ne {D D'} `{!∀ s, NonExpansive (f s)} :
    NonExpansive (@cit_map _ I C D D' f).
  Proof. move=> ?. apply cit_map_ne_gen. solve_proper. Qed.

  (** [citg_fold] is non-expansive *)
  #[export] Instance citg_fold_ne_gen {D CIT A n} :
    Proper (forall_relation (λ _, pointwise_relation _ (≡{n}≡) ==>
      pointwise_relation _ (≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡)) ==>
      (≡{n}≡) ==> (≡{n}≡)) (@citg_fold _ I C D CIT A).
  Proof.
    move=> ?? to ??. elim=>/=. move=> [????][????]/= ?. subst=>/= ????.
    by apply to.
  Qed.
  #[export] Instance citg_fold_ne {D CIT A n}
    `{!∀ s, Proper (pointwise_relation _ (≡{n}≡) ==>
        pointwise_relation _ (≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡)) (f s)} :
    Proper ((≡{n}≡) ==> (≡{n}≡)) (@citg_fold _ I C D CIT A f).
  Proof. apply citg_fold_ne_gen. solve_proper. Qed.

  (** [cit_fold] is non-expansive, under UIP over [SEL] *)
  #[export] Instance cit_fold_ne_gen `{!Uip SEL} {D A n} :
    Proper (forall_relation (λ _, pointwise_relation _ (≡{n}≡) ==>
      pointwise_relation _ (≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡)) ==>
      (≡{n}≡) ==> (≡{n}≡)) (@cit_fold _ I C D A).
  Proof.
    move=> ?? to ???. apply citg_fold_ne_gen; [|done]=> ??????????.
    apply to=>//. by do 2 f_equiv.
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
End citgO.

(** ** [citOF]: [oFunctor] for [cit] *)
Program Definition citOF {SEL} I C (D : SEL → oFunctor) : oFunctor := {|
  oFunctor_car A _ B _ := cit I C (λ s, (D s).(oFunctor_car) A B);
  oFunctor_map _ _ _ _ _ _ _ _ fg :=
    OfeMor (cit_map (λ s, oFunctor_map (D s) fg));
|}.
Next Obligation.
  move=> > [[??][??]][[??][??]][/=??]?/=. apply cit_map_ne_gen; solve_proper.
Qed.
Next Obligation.
  move=>/= * ?. apply cit_map_id=> ??. apply equiv_dist, oFunctor_map_id.
Qed.
Next Obligation.
  move=>/= * ?. etrans; [|symmetry; exact cit_map_compose]. f_equiv=> ????.
  etrans; [|apply equiv_dist; exact: oFunctor_map_compose]. by f_equiv.
Qed.

(** [citOF I C D] is contractive when [D] is contractive *)
#[export] Instance citOF_contractive {SEL I C}
  `{!∀ s, oFunctorContractive (D s)} :
  oFunctorContractive (citOF (SEL:=SEL) I C D).
Proof.
  move=> > ? * ? /=. apply cit_map_ne_gen=>// ???->.
  by apply oFunctor_map_contractive.
Qed.
