(** * Pseudo-gfp *)

From nola.util Require Export order.
Import BigMJNotation FunPNotation.

Section psg.
  Context `{!BigMeet OT}.
  Implicit Type (f : OT → OT) (o : OT).

  (** ** [Psgoid]: Set of pseudo-gfp-oids *)
  Definition Psgoid_gen f (self : OT -p> Prop) : OT -p> Prop :=
    λ o, ([⊓] o' :: self o' ∧ o ⊑ f o', f o') ⊑ o.
  #[export] Instance Psgoid_gen_mono {f} : Mono (Psgoid_gen f).
  Proof.
    move=>/= ?? imp ? /= le. unfold Psgoid_gen. etrans; [|done].
    apply big_meet_mono; [|done]=>/= ?[??]. split; by [apply imp|].
  Qed.
  Definition Psgoid f : OT -p> Prop := lfp (Psgoid_gen f).

  (** Factorizing [Psgoid] *)
  Lemma Psgoid_factor' {f o} :
    Psgoid f o → ([⊓] o' :: Psgoid f o' ∧ o ⊑ f o', f o') ⊑ o.
  Proof. apply (lfp_unfold (f:=Psgoid_gen f)). Qed.
  Lemma Psgoid_factor {f o} :
    Psgoid f o → o ≡ [⊓] o' :: Psgoid f o' ∧ o ⊑ f o', f o'.
  Proof.
    move=> /Psgoid_factor' ?. apply equiv_ole. split; [|done].
    by apply big_meet_intro=> ?[??].
  Qed.
  Lemma factor'_Psgoid {f o} :
    ([⊓] o' :: Psgoid f o' ∧ o ⊑ f o', f o') ⊑ o → Psgoid f o.
  Proof. apply (lfp_unfold (f:=Psgoid_gen f)). Qed.

  (** [Psgoid f] is proper *)
  #[export] Instance Psgoid_proper' {f} : Proper ((≡) ==> (⊑)) (Psgoid f).
  Proof.
    move=> ?? /equiv_ole[??] /Psgoid_factor' ?. apply factor'_Psgoid.
    do 2 (etrans; [|done]). apply big_meet_mono; [|done]=>/= ?[??].
    split; [done|]. by etrans.
  Qed.
  #[export] Instance Psgoid_proper {f} : Proper ((≡) ==> (≡)) (Psgoid f).
  Proof. move=> ???; split; exact: Psgoid_proper'. Qed.

  (** ** [Psgoidp]: [Psgoid] parameterized with an inductive hypothesis [ih] *)
  Definition Psgoidp f (ih : OT -p> Prop) : OT -p> Prop :=
    lfp (aug_meet (Psgoid_gen f) ih).

  (** [Psgoidp f] is monotone *)
  #[export] Instance Psgoidp_mono {f} : Mono (Psgoidp f).
  Proof. move=> *. by apply (mono (f:=lfp)), mono. Qed.

  (** [Psgoidp] over [⊤] is equivalent to [Psgoid] *)
  Lemma Psgoidp_Psgoid {f} : Psgoidp f ⊤ ≡ Psgoid f.
  Proof. apply (mono_proper (f:=lfp)), aug_meet_top. Qed.

  (** Parameterized induction principle for [Psgoidp] *)
  Lemma Psgoidp_ind {f ih'} ih o :
    Psgoidp f ih' o → Psgoidp f (ih ⊓ ih') ⊑ ih → ih o.
  Proof. move=> + H. exact: (lfp_para_ind' (o:=ih) H o). Qed.

  (** Factorizing [Psgoidp] *)
  Lemma Psgoidp_factor' {f ih o} :
    Psgoidp f ih o → ([⊓] o' :: Psgoidp f ih o' ∧ o ⊑ f o' ∧ ih o', f o') ⊑ o.
  Proof.
    move=> /(lfp_unfold_1 (f:=aug_meet _ ih)). etrans; [|done].
    by apply big_meet_mono; [|done]=>/= ?[[??]?].
  Qed.
  Lemma Psgoidp_factor {f ih o} :
    Psgoidp f ih o → o ≡ [⊓] o' :: Psgoidp f ih o' ∧ o ⊑ f o' ∧ ih o', f o'.
  Proof.
    move=> ?. apply equiv_ole. split; [|by apply Psgoidp_factor'].
    by apply big_meet_intro=> ?[?[??]].
  Qed.
  Lemma factor'_Psgoidp {f ih o} :
    ([⊓] o' :: Psgoidp f ih o' ∧ o ⊑ f o' ∧ ih o', f o') ⊑ o → Psgoidp f ih o.
  Proof.
    move=> ?. apply (lfp_unfold (f:=aug_meet _ ih)).
    unfold aug_meet, Psgoid_gen. etrans; [|done].
    by apply big_meet_mono; [|done]=>/= ?[?[??]].
  Qed.

  (** [Psgoidp f] is proper *)
  #[export] Instance Psgoidp_proper' {f} :
    Proper ((⊑) ==> (≡) ==> (⊑)) (Psgoidp f).
  Proof.
    move=> ?*?? /equiv_ole[??] /Psgoidp_factor' ?. apply: Psgoidp_mono; [done|].
    apply factor'_Psgoidp. do 2 (etrans; [|done]).
    apply big_meet_mono; [|done]=>/= ?[?[??]]. split; [done|].
    split; by [etrans|].
  Qed.
  #[export] Instance Psgoidp_proper {f} :
    Proper ((≡) ==> (≡) ==> (≡)) (Psgoidp f).
  Proof. move=> ?? /equiv_ole[??] ?*. split; by apply Psgoidp_proper'. Qed.

  (** ** [Psgoid' f]: Another definition of [Psgoid f], the closure under [f]
    and the meet *)
  Definition Psgoid'_gen f (self : OT -p> Prop) : OT -p> Prop :=
    λ o, (∃ o', self o' ∧ o ≡ f o') ∨ ∃ S, S ⊑ self ∧ o ≡ [⊓] o' :: S o', o'.
  #[export] Instance Psgoid'_gen_mono {f} : Mono (Psgoid'_gen f).
  Proof.
    move=>/= ?? imp ?[[?[??]]|[?[??]]]; [left|right]; eexists _;
      (split; [|done]); by [apply imp|etrans].
  Qed.
  Definition Psgoid' f : OT → Prop := lfp (Psgoid'_gen f).

  (** [Psgoid] and [Psgoid'] are equivalent *)
  Lemma Psgoid_Psgoid' {f} : Psgoid f ≡ Psgoid' f.
  Proof.
    apply equiv_ole. split.
    - apply lfp_ind=> o ?. apply (lfp_unfold (f:=Psgoid'_gen f)). right.
      exists (λ o', ∃ o'', o' = f o'' ∧ Psgoid' f o'' ∧ o ⊑ f o''). split.
      { move=> ?[?[->[? _]]]. apply (lfp_unfold (f:=Psgoid'_gen f)). left.
        by eexists _. }
      apply equiv_ole. split. { by apply big_meet_intro=> ?[?[->[_ ?]]]. }
      etrans; [|done]. apply big_meet_intro=> ?[??]. apply (big_meet_elim id).
      eauto.
    - apply lfp_ind=> o [[o'[? /equiv_ole[??]]]|[S[sub /equiv_ole[??]]]];
        apply factor'_Psgoid; (etrans; [|done]); [exact: big_meet_elim|].
      apply big_meet_intro=> o' s. move: (sub _ s)=> /Psgoid_factor ->.
      apply big_meet_mono; [|done]=> ?[??]. split; [done|]. etrans; [done|].
      etrans; [|done]. exact: (big_meet_elim id).
  Qed.

  (** ** Properties of [Psgoid] *)

  (** [Psgoid f] is closed under [f] *)
  Lemma Psgoid_app {f o} : Psgoid f o → Psgoid f (f o).
  Proof.
    move=> /Psgoid_Psgoid' ?. apply Psgoid_Psgoid'.
    apply (lfp_unfold (f:=Psgoid'_gen f)). left. by eexists _.
  Qed.

  (** [Psgoid f] is closed under the big meet *)
  Lemma Psgoid_big_meet {f A S} {g : A → OT} :
    (∀ a, S a → Psgoid f (g a)) → Psgoid f ([⊓] a :: S a, g a).
  Proof.
    move=> sub. apply Psgoid_Psgoid'. apply (lfp_unfold (f:=Psgoid'_gen f)).
    right. exists (λ o, ∃ a, S a ∧ o = g a). split.
    { move=> ?[?[?->]]. by apply Psgoid_Psgoid', sub. }
    apply equiv_ole. split; apply big_meet_intro=> ?.
    { move=> [?[?->]]. exact: big_meet_elim. }
    move=> ?. apply (big_meet_elim id). eauto.
  Qed.

  (** ** [psg]: Pseudo-gfp *)
  Definition psg_def f : OT := [⊓] o :: Psgoid f o, o.
  Lemma psg_aux : seal psg_def. Proof. by eexists. Qed.
  Definition psg := psg_aux.(unseal).
  Lemma psg_unseal : psg = psg_def. Proof. exact: seal_eq. Qed.

  (** [psg f] is [Psgoid f] *)
  Lemma psg_Psgoid {f} : Psgoid f (psg f).
  Proof. rewrite psg_unseal. exact: Psgoid_big_meet. Qed.

  (** [psg f] lower-bounds [Psgoid f] *)
  Lemma psg_Psgoid_lb {f o} : Psgoid f o → psg f ⊑ o.
  Proof. rewrite psg_unseal. exact: (big_meet_elim id). Qed.

  (** [psg f] is a post-fixpoint *)
  Lemma psg_post {f} : psg f ⊑ f (psg f).
  Proof. apply psg_Psgoid_lb, Psgoid_app, psg_Psgoid. Qed.
End psg.

(** ** [psg f] agrees with [gfp f] when [f] is monotone *)
Section psg_gfp.
  Context `{!BigMeet OT, !BigJoin OT, !@Mono OT OT f}.

 (** [gfp f] lower-bounds [Psgoid f] *)
  Lemma Psgoid_gfp {o} : Psgoid f o → gfp f ⊑ o.
  Proof.
    apply (lfp_ind (OT:=_-p>_) (o:=(gfp f ⊑.)))=> ??. etrans; [|done].
    apply big_meet_intro=> ?[??]. etrans; [apply gfp_unfold_1|]. exact: mono.
  Qed.

  (** [psg f] agrees with [gfp f] *)
  Lemma psg_gfp : psg f ≡ gfp f.
  Proof.
    apply equiv_ole. split; [|apply Psgoid_gfp, psg_Psgoid].
    apply gfp_coind, psg_post.
  Qed.
End psg_gfp.
