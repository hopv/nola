(** * Pseudo-gfp *)

From nola.util Require Export order.
Import OrderNotation.

Section psg.
  Context `{!BigMeet OT}.
  Implicit Type (f : OT → OT) (o : OT).

  (** ** [Psgoid]: Set of pseudo-gfp-oids *)
  Definition Psgoid_gen f (self : OT → Prop) (o : OT) : Prop :=
    ([⊓] o' :: self o' ∧ o ⊑ f o', f o') ⊑ o.
  #[export] Instance Psgoid_gen_mono {f} : Mono (Psgoid_gen f).
  Proof.
    move=>/= ?? imp ? /= le. unfold Psgoid_gen. etrans; [|done].
    apply big_meet_mono; [|done]=>/= ?[??]. split; by [apply imp|].
  Qed.
  Definition Psgoid f : OT → Prop := lfp (Psgoid_gen f).

  (** Pseudo-coinduction principle on [Psgoid] *)
  Lemma to_Psgoid {f o} :
    Psgoid f o → ([⊓] o' :: Psgoid f o' ∧ o ⊑ f o', f o') ⊑ o.
  Proof. apply (lfp_unfold (f:=Psgoid_gen f)). Qed.
  Lemma Psgoid_eq {f o} :
    Psgoid f o → o ≃ [⊓] o' :: Psgoid f o' ∧ o ⊑ f o', f o'.
  Proof.
    move=> ?. split; [|by apply to_Psgoid]. by apply big_meet_intro=> ?[??].
  Qed.

  (** ** [Psgoidp]: [Psgoid] parameterized with an inductive hypothesis [ih] *)
  Definition Psgoidp f (ih : OT → Prop) : OT → Prop :=
    lfp (aug_meet (Psgoid_gen f) ih).

  (** [Psgoidp f] is monotone *)
  #[export] Instance Psgoidp_mono {f} : Mono (Psgoidp f).
  Proof. move=> *. by apply (mono (f:=lfp)), mono. Qed.

  (** Pseudo-coinduction principle on [Psgoidp] *)
  Lemma to_Psgoidp {f ih o} :
    Psgoidp f ih o → ([⊓] o' :: Psgoidp f ih o' ∧ o ⊑ f o' ∧ ih o', f o') ⊑ o.
  Proof.
    move=> /(lfp_unfold_1 (f:=aug_meet _ ih)). etrans; [|done].
    by apply big_meet_mono; [|done]=>/= ?[[??]?].
  Qed.
  Lemma Psgoidp_eq {f ih o} :
    Psgoidp f ih o → o ≃ [⊓] o' :: Psgoidp f ih o' ∧ o ⊑ f o' ∧ ih o', f o'.
  Proof. split; [|by apply to_Psgoidp]. by apply big_meet_intro=> ?[?[??]]. Qed.

  (** [Psgoidp] on [⊤] is equivalent to [Psgoid] *)
  Lemma Psgoidp_Psgoid {f} : Psgoidp f ⊤ ≃ Psgoid f.
  Proof. apply (mono_proper (f:=lfp)), aug_meet_top. Qed.

  (** Parameterized induction principle for [Psgoidp] *)
  Lemma Psgoidp_ind {f ih ih'} {P : OT → Prop} :
    Psgoidp f (ih ⊓ ih') ⊑ ih → Psgoidp f ih' ⊑ ih.
  Proof.
    move=> ?. apply lfp_para_ind. etrans; [|done].
    apply (mono (f:=lfp)), aug_meet_nest.
  Qed.

  (** ** [Psgoid' f]: Another definition of [Psgoid], the closure under the
    meet after [f] *)
  Definition Psgoid'_gen f (self : OT → Prop) o : Prop :=
    ∃ S, S ⊑ self ∧ o ≃ [⊓] o' :: S o', f o'.
  #[export] Instance Psgoid'_gen_mono `{!BigMeet OT} {f} : Mono (Psgoid'_gen f).
  Proof. move=>/= ????[S[??]]. exists S. split; by [etrans|]. Qed.
  Definition Psgoid' f : OT → Prop := lfp (Psgoid'_gen f).

  (** [Psgoid] and [Psgoid'] are equivalent *)
  Lemma Psgoid_Psgoid' {f} : Psgoid f ≃ Psgoid' f.
  Proof.
    split.
    - apply lfp_ind=> o ?. apply (lfp_unfold (f:=Psgoid'_gen f)).
      exists (λ o', Psgoid' f o' ∧ o ⊑ f o'). split; [by move=> ?[??]|].
      split; [|done]. by apply big_meet_intro=> ?[??].
    - apply lfp_ind=> o [S[sub[??]]]. apply (lfp_unfold (f:=Psgoid_gen f)).
      unfold Psgoid_gen. etrans; [|done]. apply big_meet_intro=> ??.
      apply big_meet_elim. split; [by apply sub|]. etrans; [done|].
      by apply big_meet_elim.
  Qed.

  (** ** [Psgoid'' f]: Yet another definition of [Psgoid f], the closure under [f]
    and the meet *)
  Definition Psgoid''_gen f (self : OT → Prop) o : Prop :=
    (∃ o', self o' ∧ o ≃ f o') ∨ ∃ S, S ⊑ self ∧ o ≃ [⊓] o' :: S o', o'.
  #[export] Instance Psgoid''_gen_mono {f} : Mono (Psgoid''_gen f).
  Proof.
    move=>/= ?? imp ?[[?[??]]|[?[??]]]; [left|right]; eexists _;
      (split; [|done]); by [apply imp|etrans].
  Qed.
  Definition Psgoid'' f : OT → Prop := lfp (Psgoid''_gen f).

  (** [Psgoid], [Psgoid'] and [Psgoid''] are equivalent *)
  Lemma Psgoid'_Psgoid'' {f} : Psgoid' f ≃ Psgoid'' f.
  Proof.
    split.
    - apply lfp_ind=> o [S[sub eq]]. apply (lfp_unfold (f:=Psgoid''_gen f)).
      right. exists (λ o', ∃ o'', S o'' ∧ o' ≃ f o''). split.
      { move=> ?[?[??]]. apply (lfp_unfold (f:=Psgoid''_gen f)). left.
        eexists _. split; by [apply sub|]. }
      rewrite eq. split; apply big_meet_intro=> ?.
      { move=> [?[?->]]. by apply big_meet_elim. }
      move=> ?. apply (big_meet_elim id). by eexists _.
    - apply lfp_ind=> o [[o'[? eq]]|[S[sub eq]]];
        apply (lfp_unfold (f:=Psgoid'_gen f)).
      { exists (.= o'). split; [by move=> ?->|]. rewrite eq. split.
        { by apply big_meet_intro=> ?->. } { by apply big_meet_elim. } }
      exists (λ o', Psgoid f o' ∧ ∃ o'', S o'' ∧ o'' ⊑ f o'). split.
      { move=> ?[?[?[??]]]. by apply Psgoid_Psgoid'. }
      rewrite eq. split; apply big_meet_intro=> o'.
      { move=> [?[?[??]]]. etrans; [|done]. by apply (big_meet_elim id). }
      move=> el. move: (sub _ el)=> PS. apply Psgoid_Psgoid', to_Psgoid in PS.
      etrans; [|done]. apply big_meet_mono; [|done]=> ?[??]. eauto.
  Qed.
  Lemma Psgoid_Psgoid'' {f} : Psgoid f ≃ Psgoid'' f.
  Proof. by rewrite Psgoid_Psgoid' Psgoid'_Psgoid''. Qed.

  (** ** Properties on [Psgoid] *)

  (** [Psgoid f] is closed under [f] *)
  Lemma Psgoid_app {f o} : Psgoid f o → Psgoid f (f o).
  Proof.
    move=> PS. apply Psgoid_Psgoid'' in PS. apply Psgoid_Psgoid''.
    apply (lfp_unfold (f:=Psgoid''_gen f)). left. by eexists _.
  Qed.

  (** [Psgoid f] is closed under the big meet *)
  Lemma Psgoid_big_meet {f A S} {g : A → OT} :
    (∀ a, S a → Psgoid f (g a)) → Psgoid f ([⊓] a :: S a, g a).
  Proof.
    move=> sub. apply Psgoid_Psgoid''. apply (lfp_unfold (f:=Psgoid''_gen f)).
    right. exists (λ o, ∃ a, S a ∧ o = g a). split.
    { move=> ?[?[?->]]. by apply Psgoid_Psgoid'', sub. }
    split; apply big_meet_intro=> ?.
    { move=> [?[?->]]. by apply big_meet_elim. }
    move=> ?. apply (big_meet_elim id). eauto.
  Qed.

  (** [Psgoid f] is proper *)
  Lemma Psgoid_proper' {f} : Proper ((≃) ==> (⊑)) (Psgoid f).
  Proof.
    move=> ??? PS. apply Psgoid_Psgoid', (lfp_unfold (f:=Psgoid'_gen f)) in PS.
    move: PS=> [?[??]]. apply Psgoid_Psgoid', (lfp_unfold (f:=Psgoid'_gen f)).
    eexists _. split; [done|]. by etrans.
  Qed.
  #[export] Instance Psgoid_proper {f} : Proper ((≃) ==> (≃)) (Psgoid f).
  Proof. move=> ???; split; by apply Psgoid_proper'. Qed.

  (** ** [psg]: Pseudo-gfp *)
  Definition psg f : OT := [⊓] o :: Psgoid f o, o.

  (** [psg f] is [Psgoid f] *)
  Lemma psg_Psgoid {f} : Psgoid f (psg f).
  Proof. by apply Psgoid_big_meet. Qed.

  (** [psg f] lower-bounds [Psgoid f] *)
  Lemma psg_Psgoid_lb {f o} : Psgoid f o → psg f ⊑ o.
  Proof. exact (big_meet_elim id). Qed.

  (** [psg f] is a post-fixpoint *)
  Lemma psg_post {f} : psg f ⊑ f (psg f).
  Proof. apply psg_Psgoid_lb, Psgoid_app, psg_Psgoid. Qed.
End psg.

(** ** [psg f] agrees with [gfp f] when [f] is monotone *)
Section psg_gfp.
  Context `{!BigMeet OT, !BigJoin OT, !@Mono OT OT f}.
  Implicit Type o : OT.

 (** [gfp f] lower-bounds [Psgoid f] *)
  Lemma Psgoid_gfp {o} : Psgoid f o → gfp f ⊑ o.
  Proof.
    move: o. apply (lfp_ind (o:=(gfp f ⊑.)))=> ??. etrans; [|done].
    apply big_meet_intro=> ?[??]. etrans; [apply gfp_unfold|]. by apply mono.
  Qed.

  (** [psg f] agrees with [gfp f] *)
  Lemma psg_gfp : psg f ≃ gfp f.
  Proof. split; [|apply Psgoid_gfp, psg_Psgoid]. apply gfp_coind, psg_post. Qed.
End psg_gfp.
