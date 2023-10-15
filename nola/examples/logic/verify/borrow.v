(** * Verification on borrowing *)

From nola.examples.logic Require Export borrow.
From nola.examples.heap_lang Require Export proofmode notation.
From iris.base_logic.lib Require Export ghost_var.

Section borrow.
  Context `{!nintpGS Σ}.

  (** Convert a nested borrow *)
  Lemma bor_bor_conv' `{!nderivy ih δ} {α β P Q} :
    α ⊑□ β -∗ β ⊑□ α -∗ □ conv δ P Q -∗ □ conv δ Q P -∗
    conv δ (n_bor' [] α P) (n_bor' [] β Q).
    iIntros "#⊑ #⊑' #PQ #QP". iApply (derivy_byintp (δ:=δ))=>/=.
    iIntros "% % % _ #→ _ b". iDestruct (bor_lft with "⊑' b") as "b".
    iApply (bor_conv with "[] [] b"); iModIntro; by iApply "→".
  Qed.
  Lemma bor_bor_conv `{!nderivy ih δ} {α β P Q} :
    α ⊑□ β -∗ β ⊑□ α -∗ □ conv δ P Q -∗ □ conv δ Q P -∗
    bor δ α (n_bor' [] α P) -∗ bor δ β (n_bor' [] β Q).
  Proof.
    iIntros "#⊑ #⊑' #PQ #QP b". iDestruct (bor_lft with "⊑' b") as "b".
    iApply (bor_conv with "[] [] b"); iModIntro; by iApply bor_bor_conv'.
  Qed.

  (** Dereference a nested mutable reference *)
  Lemma bor_bor_deref {α β l Φ q} :
    [[{ q.[α ⊓ β] ∗
      bord α (∃ l' : loc, l ↦ #l' ∗ n_bor' [] β (∃ v, l' ↦ v ∗ Φ v)) }]]
      [borrow_wsatd ∗ fborrow_wsat' ∗ proph_wsat]
      !#l
    [[{ l', RET #l' ; q.[α ⊓ β] ∗ bord (α ⊓ β) (∃ v, l' ↦ v ∗ Φ v) }]].
  Proof.
    iIntros "%Ψ [[α β] b] →Ψ". iMod (bor_open with "α b") as "[o big]"=>/=.
    iDestruct "big" as (l') "[↦ b']". iApply twpw_fupdw_nonval; [done|].
    wp_load. iModIntro. iMod (bor_reborrow α with "β b'") as "[β[b' →b']]".
    rewrite [_⊓_]comm.
    iMod (obor_subdiv [] [] with "o [//] [//] [↦ →b']") as "[α _]"=>/=.
    { iIntros "† _ _". iModIntro. iExists _. iFrame "↦". by iApply "→b'". }
    iModIntro. iApply "→Ψ". rewrite borc_bor. iFrame.
  Qed.

  Implicit Type X : nsynty.

  (** Value observer *)
  Notation vo γ X x := (γ ⤇{X}(1/2) x)%I.
  Notation n_vo γ X x := (γ ⤇{X}(1/2) x)%n.
  Notation vo2 γ X x := (γ ⤇{X}(1) x)%I.
  Notation n_vo2 γ X x := (γ ⤇{X}(1) x)%n.

  (** Prophecy controller *)
  Definition pc γ X x (ξ : prvar X) : iProp Σ :=
    (vo γ X x ∗ 1:[ξ]) ∨
    ((∃ x', vo2 γ X x') ∗ ⟨π, π ξ = x⟩).
  Definition n_pc {κ Γ} γ X x (ξ : prvar X) : nProp κ Γ :=
    (n_vo γ X x ∗ 1:[ξ]) ∨
    ((∃ x', n_vo2 γ X x') ∗ ⟨π, π ξ = x⟩).

  (** [vo] and [vo2] can't coexist *)
  Lemma vo_vo2 {γ X x x'} : vo γ X x -∗ vo2 γ X x' -∗ False.
  Proof.
    iIntros "vo vo'". by iDestruct (ghost_var_valid_2 with "vo vo'") as %[? _].
  Qed.

  (** Allocate [vo] and [pc] *)
  Lemma vo_pc_alloc {X x} {ξ : prvar X} : 1:[ξ] ==∗ ∃ γ, vo γ X x ∗ pc γ X x ξ.
  Proof.
    iIntros "ξ". iMod (ghost_var_alloc) as (γ) "[vo vo']". iModIntro. iExists _.
    iFrame "vo". iLeft. iFrame.
  Qed.

  (** Agreement between [vo] and [pc] *)
  Lemma vo_pc_agree {γ X x x' ξ} : vo γ X x -∗ pc γ X x' ξ -∗ ⌜x = x'⌝.
  Proof.
    iIntros "vo [[vo' _]|[[% vo2] _]]"; last first.
    { iDestruct (vo_vo2 with "vo vo2") as %[]. }
    by iDestruct (anyty_var_agree with "vo vo'") as %?.
  Qed.

  (** Update the value of [vo] and [pc] *)
  Lemma vo_pc_update {γ X x x' y ξ} :
    vo γ X x -∗ pc γ X x' ξ ==∗ vo γ X y ∗ pc γ X y ξ.
  Proof.
    iIntros "vo [[vo' ξ]|[[% vo2] _]]"; last first.
    { iDestruct (vo_vo2 with "vo vo2") as %[]. }
    iMod (ghost_var_update_2 with "vo vo'") as "[$ vo]"; [by rewrite Qp.div_2|].
    iModIntro. iLeft. iFrame.
  Qed.

  (** Resolve the prophecy of [pc] *)
  Lemma vo_pc_preresolve {γ X x x'} ξ aπ ηl q : aπ ./ ηl →
    q:∗[ηl] -∗ vo γ X x -∗ pc γ X x' ξ =[proph_wsat]=∗
      q:∗[ηl] ∗ ⟨π, π ξ = aπ π⟩ ∗ (∀ y, ⟨π, aπ π = y⟩ -∗ pc γ X y ξ).
  Proof.
    iIntros "% ηl vo [[vo' ξ]|[[% vo2] _]]"; last first.
    { iDestruct (vo_vo2 with "vo vo2") as %[]. }
    iMod (proph_resolve_dep with "ξ ηl") as "[$ #obs]"; [done|]. iModIntro.
    iFrame "obs". iIntros "%y obs'". iRight. iCombine "vo vo'" as "vo2".
    iSplit; [by iExists _|]. by iApply (proph_obs_impl2 with "obs obs'")=> ?->.
  Qed.
  Lemma pc_resolve {γ X x} ξ :
    pc γ X x ξ =[proph_wsat]=∗ ⟨π, π ξ = x⟩.
  Proof.
    iIntros "[[_ ξ]|[_ $]]"; [|done]. iApply (proph_resolve with "ξ").
  Qed.

  (** Dereference a nested prophetic mutable reference *)
  Lemma proph_bor_bor_deref
    {γ X η ξ α β l q} {x : X} {Φ : _ → _ → nPropS (;ᵞ)} :
    [[{ q.[α ⊓ β] ∗ vo γ (X *'ₛ prvarₛ X) (x, ξ)' ∗
      bord α (∃ (x : X) ξ γ' (l' : loc),
        n_pc γ (X *'ₛ prvarₛ X) (x, ξ)' η ∗ l ↦ #l' ∗ n_vo γ' X x ∗
        n_bor' [] β (∃ x v, n_pc γ' X x ξ ∗ l' ↦ v ∗ ↑ˡ Φ x v)) }]]
      [borrow_wsatd ∗ fborrow_wsat' ∗ proph_wsat]
      !#l
    [[{ l', RET #l' ; q.[α ⊓ β] ∗ ∃ (ζ : prvar X) γ'',
      ⟨π, π η = (π ζ, ξ)'⟩ ∗ vo γ'' X x ∗
      bord (α ⊓ β) (∃ x v, n_pc γ'' X x ζ ∗ l' ↦ v ∗ ↑ˡ Φ x v) }]].
  Proof.
    iIntros "%Ψ [[α β][vo b]] →Ψ". iMod (bor_open with "α b") as "[o big]"=>/=.
    iDestruct "big" as (x2 ξ2 γ' l') "[pc[↦[vo' b']]]".
    iApply twpw_fupdw_nonval; [done|]. wp_load. iModIntro.
    iDestruct (vo_pc_agree with "vo pc") as %eq. case: eq=> <-<-.
    iMod (bor_reborrow α with "β b'") as "[[β β'][b' →b']]". rewrite [β⊓_]comm.
    iMod (obor_subdiv
      [∃ (x : X), n_pc γ (X *'ₛ prvarₛ X) (x, ξ)' η ∗ n_vo γ' X x]%n [] with
      "o [pc vo'] [//] [↦ →b']") as "[[α α'][[c _]_]]"=>/=.
    { iSplit; [|done]. iExists _. by iFrame "vo'". }
    { iIntros "† [big _] _". iDestruct "big" as (x'') "[pc vo']". iModIntro.
      iExists _, _, _, _. iFrame "↦ vo' pc". by iApply "→b'". }
    iDestruct (borc_lft with "[] c") as "c"; [iApply lft_sincl_meet_l|].
    iMod (borc_open with "[α β] c") as "[o big]"; [by iFrame|]=>/=.
    iDestruct "big" as (x') "[pc vo']".
    iMod (borc_open with "[α' β'] b'") as "[o' big]"; [by iFrame|]=>/=.
    iDestruct "big" as (x'2 v) "[pc'[↦' Φ]]".
    iDestruct (vo_pc_agree with "vo' pc'") as %<-.
    iDestruct (vo_pc_agree with "vo pc") as %eq. case: eq=> <-.
    iMod (proph_intro X x) as (ζ) "ζ".
    iMod (vo_pc_preresolve η (λ π, (π ζ, ξ)') [ζ : aprvarn]
      with "[$ζ//] vo pc") as "[[ζ _][#obs →pc]]".
    { apply (proph_dep_constr (λ x, (x, ξ)')), (proph_dep_one ζ). }
    iMod (vo_pc_alloc with "ζ") as (γ'') "[vo'' pc'']".
    iMod (obor_merge_subdiv [(_,_)';(_,_)']
      [∃ x v, n_pc γ'' X x ζ ∗ l' ↦ v ∗ Φ x v]%n []
      with "[$o $o'//] [pc'' ↦' Φ] [//] [→pc vo' pc']")
      as "[[αβ[αβ' _]][[c _]_]]"=>/=.
    { iSplit; [|done]. iExists _, _. rewrite nintp_nlarge. iFrame. }
    { iIntros "† [big _] _". iDestruct "big" as (x'' v') "[pc''[↦ Φ]]".
      iMod (vo_pc_update with "vo' pc'") as "[vo' pc']".
      iMod (pc_resolve with "pc''") as "#obs'". iModIntro. iSplitL "→pc vo'".
      - iExists x''. iFrame "vo'". iApply "→pc".
        by iApply (proph_obs_impl with "obs'")=> ?->.
      - iSplit; [|done]. iExists _, _. rewrite nintp_nlarge. iFrame. }
    iModIntro. iApply "→Ψ". iFrame "αβ αβ'". iExists _, _.
    rewrite borc_bor. by iFrame.
  Qed.
End borrow.
