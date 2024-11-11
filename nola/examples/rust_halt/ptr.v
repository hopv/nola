(** * Utility for pointer types *)

From nola.examples.rust_halt Require Export type.

Implicit Type l : loc.

(** ** Function *)

(** Memory copy *)
Definition memcpy : val := rec: "memcpy" ["tgt"; "len"; "src"] :=
  if: "len" ≤ #0 then #☠ else
    "tgt" <- !"src";; "memcpy" ["tgt" +ₗ #1 ; "len" - #1 ; "src" +ₗ #1].
Notation "e1 <-{ n } ! e2" :=
  (App (of_val memcpy) [e1%E; Lit (LitInt n); e2%E])
  (at level 80, n at next level, format "e1  <-{ n }  ! e2") : expr_scope.

Section twp.
  Context `{!lrustGS_gen hlc Σ}.

  (** [twp] over [memcpy] *)
  Lemma twp_memcpy vls vlt {W E ls lt  q n} :
    length vls = n → length vlt = n →
    [[{ ls ↦∗{q} vls ∗ lt ↦∗ vlt }]][W]
      #lt <-{n} !#ls @ E
    [[{ RET #☠; ls ↦∗{q} vls ∗ lt ↦∗ vls }]].
  Proof.
    move: ls vls lt vlt. elim: n=>/=.
    { move=> ?[|//]?[|//]_ _. iIntros (?) "[??] →Φ".
      rewrite heap_pointsto_vec_nil. wp_rec. wp_op. wp_case. iApply "→Φ".
      iFrame. }
    move=> n IH ?[//|? vls]?[//|? vlt]/=[?][?]. iIntros (?).
    rewrite !heap_pointsto_vec_cons. iIntros "[[↦s ↦sl] [↦t ↦tl]] →Φ". wp_rec.
    wp_op. wp_case. wp_read. wp_write. do 3 wp_op.
    have -> : (S n - 1)%Z = n by lia.
    wp_apply (IH _ vls _ vlt with "[$↦sl $↦tl]")=>//. iIntros "[??]".
    iApply "→Φ". iFrame.
  Qed.
End twp.

(** ** Read and write *)

Section read_write.
  Context `{!rust_haltGS CON Σ, rust_haltJ CON JUDG Σ, !Csem CON JUDG Σ,
    !Jsem JUDG (iProp Σ)}.

  (** [Read]: Read from a pointer type *)
  Class Read {X Y X'} (κ : lft) (T : ty CON Σ X) (U : ty CON Σ Y)
    (T' : ty CON Σ X') (get : X → Y) (set : X → X') : Prop := READ {
    read {q t d xπ v} :
      q.[κ] -∗ na_own t ⊤ -∗ ⟦ ty_own T t d xπ [v] ⟧ᶜ =[rust_halt_wsat]{⊤}=∗
        ∃ l wl r du, ⌜v = # l⌝ ∧ l ↦∗{r} wl ∗ ⟦ ty_own U t du (get ∘ xπ) wl ⟧ᶜ ∗
          (l ↦∗{r} wl =[rust_halt_wsat]{⊤}=∗ ∃ d',
            q.[κ] ∗ na_own t ⊤ ∗ ⟦ ty_own T' t d' (set ∘ xπ) [v] ⟧ᶜ);
  }.

  (** [Write]: Write to a pointer type *)
  Class Write {X Y Y' X'} (κ : lft) (T : ty CON Σ X) (U : ty CON Σ Y)
    (U' : ty CON Σ Y') (T' : ty CON Σ X') (get : X → Y) (set : X → Y' → X')
    : Prop := WRITE {
    write {q t d xπ v} :
      q.[κ] -∗ ⟦ ty_own T t d xπ [v] ⟧ᶜ =[rust_halt_wsat]{⊤}=∗ ∃ l wl du,
        ⌜v = # l⌝ ∧ l ↦∗ wl ∗ ⟦ ty_own U t du (get ∘ xπ) wl ⟧ᶜ ∗
        (∀ wl' du' yπ', l ↦∗ wl' -∗ ⟦ ty_own U' t du' yπ' wl' ⟧ᶜ
          =[rust_halt_wsat]{⊤}=∗ ∃ d',
          q.[κ] ∗ ⟦ ty_own T' t d' (λ π, set (xπ π) (yπ' π)) [v] ⟧ᶜ);
  }.

  (** Reading a value from a pointer *)
  Lemma type_read p
    `(!EtcxExtract (X:=X) (Yl:=Zl) (Zl:=Zl') (p ◁ T) Γ Γr get' getr,
      !Read (Y:=Y) (X':=X') κ T U T' get set, !Ty U) :
    ty_size U = 1 →
    ⊢ type κ Γ (!p) (λ r, r ◁ U ᵖ:: p ◁ T' ᵖ:: Γr)
        (λ post zl, let x := get' zl in post (get x, set x, getr zl)').
  Proof.
    rewrite type_unseal. iIntros (U1 ????) "!> κ t pre".
    rewrite etcx_extract /=. iIntros "[(% & % & % & T) Γr]".
    iMod (read with "κ t T") as (? wl ?? ->) "(↦ & U & →T')".
    iDestruct (ty_own_size with "U") as %lwl. rewrite U1 in lwl.
    destruct wl as [|w[|??]]=>//. rewrite heap_pointsto_vec_singleton.
    wp_path p. wp_read. iMod ("→T'" with "↦") as (?) "($ & $ & T')". iModIntro.
    iFrame "pre". iFrame. by rewrite of_path_val.
  Qed.

  (** Writing a value to a pointer *)
  Lemma type_write p p' {Y Ya} Ua f
    `(!TcxExtract (Xl:=[X;Y]) (Yl:=Zl) (Zl:=Zl') ᵖ[p ◁ T; p' ◁ U] Γ Γr
        get' getr,
      !Write (Y:=Y') (Y':=Ya) (X':=X') κ T U' Ua T' get set, !Ty U',
      !Resol U' κ postr) :
    ty_size U' = 1 →
    subtyd U Ua f
    ⊢ type κ Γ (p <- p') (λ _, p ◁ T' ᵖ:: Γr)
        (λ post zl, let '(x, y, _)' := get' zl in
          postr (get x) → post (set x (f y), getr zl)')%type.
  Proof.
    rewrite subty_unseal type_unseal. iIntros (U'1) "[_[#UUa _]] !>".
    iIntros (????) "κ t pre". rewrite tcx_extract /=.
    iIntros "[((% & % & % & T) & (% & % & % & U) & _) Γr]".
    iMod (write with "κ T") as (? wl ? ->) "(↦ & U' & →T')".
    iDestruct (ty_own_size with "U'") as %lwl. rewrite U'1 in lwl.
    destruct wl as [|?[|??]]=>//. rewrite heap_pointsto_vec_singleton.
    wp_path p. wp_path p'. wp_write. rewrite -heap_pointsto_vec_singleton.
    iDestruct ("UUa" with "U") as "Ua".
    iMod ("→T'" with "↦ Ua") as (?) "[κ Tt']".
    iMod (resol with "κ t U'") as "($ & $ & postr)". iModIntro.
    iExists (λ _, (_, _)'). iFrame "Tt' Γr". iSplit; [|done].
    iApply (proph_obs_impl2 with "postr pre")=>/= ?? to. by apply to.
  Qed.

  (** Memory copy *)
  Lemma type_memcopy ps pt {Y Ya} Ua f
    `(!TcxExtract (Xl:=[Xs; Xt]) (Yl:=Zl) (Zl:=Zl') ᵖ[ps ◁ Ts; pt ◁ Tt] Γ Γr
        get getr,
      !Read (Y:=Y) (X':=Xs') κ Ts U Ts' gets sets,
      !Write (Y:=Y') (Y':=Ya) (X':=Xt') κ Tt U' Ua Tt' gett sett, !Ty U, !Ty U',
      !Resol U' κ postr) {sz} :
    ty_size U = sz → ty_size U' = sz →
    subtyd U Ua f ⊢
      type κ Γ (pt <-{sz} !ps)%E (λ _, ps ◁ Ts' ᵖ:: pt ◁ Tt' ᵖ:: Γr)
        (λ post zl, let '(xs, xt, _)' := get zl in postr (gett xt) →
          post (sets xs, sett xt (f (gets xs)), getr zl)')%type.
  Proof.
    rewrite subty_unseal type_unseal. iIntros (Usz U'sz) "#[_[UUa _]] !>".
    iIntros (????) "[κ κ'] t pre". rewrite tcx_extract /=.
    iIntros "[((% & % & % & Ts) & (% & % & % & Tt) & _) Γr]".
    iMod (read with "κ t Ts") as (? wls ?? ->) "(↦s & U & →Ts')".
    iMod (write with "κ' Tt") as (? wlt ? ->) "(↦t & U' & →Tt')".
    iDestruct (ty_own_size with "U") as %lU. rewrite Usz in lU.
    iDestruct (ty_own_size with "U'") as %lU'. rewrite U'sz in lU'.
    wp_path pt. wp_path ps. wp_apply (twp_memcpy wls wlt with "[$↦s $↦t]")=>//.
    iIntros "[↦s ↦t]". iMod ("→Ts'" with "↦s") as (?) "($ & t & Ts')".
    iDestruct ("UUa" with "U") as "Ua".
    iMod ("→Tt'" with "↦t Ua") as (?) "[κ Tt']".
    iMod (resol with "κ t U'") as "($ & $ & postr)". iModIntro.
    iExists (λ _, (_, _, _)'). iFrame "Ts' Tt' Γr". iSplit; [|done].
    iApply (proph_obs_impl2 with "postr pre")=>/= ?? to. by apply to.
  Qed.
End read_write.
