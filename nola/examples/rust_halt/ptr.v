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
  Class Read {X Y X'} (α : lft) (T : ty CON Σ X) (U : ty CON Σ Y)
    (T' : ty CON Σ X') (get : X → Y) (set : X → X') : Prop := READ {
    read {q t d xπ v} :
      q.[α] -∗ na_own t ⊤ -∗ ⟦ T.1 t d xπ [v] ⟧ᶜ =[rust_halt_wsat]{⊤}=∗
        ∃ l wl du r, ⌜v = # l⌝ ∗ l ↦∗{r} wl ∗ ⟦ U.1 t du (get ∘ xπ) wl ⟧ᶜ ∗
          (l ↦∗{r} wl =[rust_halt_wsat]{⊤}=∗ ∃ d',
            q.[α] ∗ na_own t ⊤ ∗ ⟦ T'.1 t d' (set ∘ xπ) [v] ⟧ᶜ);
  }.

  (** [Write]: Write to a pointer type *)
  Class Write {X Y Y' X'} (α : lft) (T : ty CON Σ X) (U : ty CON Σ Y)
    (U' : ty CON Σ Y') (T' : ty CON Σ X') (get : X → Y) (set : X → Y' → X')
    : Prop := WRITE {
    write {q t d xπ v} :
      q.[α] -∗ ⟦ T.1 t d xπ [v] ⟧ᶜ =[rust_halt_wsat]{⊤}=∗ ∃ l wl du,
        ⌜v = # l⌝ ∗ l ↦∗ wl ∗ ⟦ U.1 t du (get ∘ xπ) wl ⟧ᶜ ∗
        (∀ du' yπ' wl', l ↦∗ wl' -∗ ⟦ U'.1 t du' yπ' wl' ⟧ᶜ
          =[rust_halt_wsat]{⊤}=∗ ∃ d',
          q.[α] ∗ ⟦ T'.1 t d' (λ π, set (xπ π) (yπ' π)) [v] ⟧ᶜ);
  }.

  (** Reading a value from a pointer *)
  Lemma type_read v
    `(!EtcxExtract (X:=X) (Yl:=Zl) (Zl:=Zl') (v ◁ T) Γ Γr get' getr,
      !Read (Y:=Y) (X':=X') α T U T' get set, !Ty U 1) :
    ⊢ type α Γ (!v) (λ r, r ◁ U ᵖ:: v ◁ T' ᵖ:: Γr)
      (λ post zl, let x := get' zl in post (get x, set x, getr zl)').
  Proof.
    rewrite type_unseal. iIntros (????) "!> α t pre".
    rewrite etcx_extract /=. iIntros "[[% T] Γr]".
    iMod (read with "α t T") as (? wl ?? ->) "(↦ & U & →T')".
    iDestruct (ty_own_size with "U") as %?. destruct wl as [|w[|??]]=>//.
    rewrite heap_pointsto_vec_singleton. wp_read.
    iMod ("→T'" with "↦") as (?) "($ & $ & T')". iModIntro. iFrame "pre".
    iFrame.
  Qed.

  (** Writing a value to a pointer *)
  Lemma type_write v w
    `(!TcxExtract (Xl:=[X;Y]) (Yl:=Zl) (Zl:=Zl') ᵖ[v ◁ T; w ◁ U] Γ Γr get' getr,
      !Write (Y:=Y') (X':=X') α T U' U T' get set, !Ty U' 1) :
    ⊢ type α Γ (v <- w) (λ _, v ◁ T' ᵖ:: Γr)
        (λ post zl, let '(x, y, _)' := get' zl in post (set x y, getr zl)').
  Proof.
    rewrite type_unseal. iIntros (????) "!> α $ pre". rewrite tcx_extract /=.
    iIntros "[([% T] & [% U] & _) Γr]".
    iMod (write with "α T") as (? wl ? ->) "(↦ & U' & →T')".
    iDestruct (ty_own_size with "U'") as %?. destruct wl as [|?[|??]]=>//.
    rewrite heap_pointsto_vec_singleton. wp_write.
    rewrite -heap_pointsto_vec_singleton.
    iMod ("→T'" with "↦ U") as (?) "($ & Tt')". iModIntro. iFrame "pre". iFrame.
  Qed.

  (** Memory copy *)
  Lemma type_memcopy vs vt
    `(!TcxExtract (Xl:=[Xs; Xt]) (Yl:=Zl) (Zl:=Zl') ᵖ[vs ◁ Ts; vt ◁ Tt] Γ Γr
        get getr,
      !Read (Y:=Y) (X':=Xs') α Ts U Ts' gets sets,
      !Write (Y:=Y') (X':=Xt') α Tt U' U Tt' gett sett, !Ty U sz, !Ty U' sz) :
    ⊢ type α Γ (vt <-{sz} !vs)%E (λ _, vs ◁ Ts' ᵖ:: vt ◁ Tt' ᵖ:: Γr)
        (λ post zl, let '(xs, xt, _)' := get zl in
          post (sets xs, sett xt (gets xs), getr zl)').
  Proof.
    rewrite type_unseal. iIntros (????) "!> [α α'] t pre".
    rewrite tcx_extract /=. iIntros "[([% Ts] & [% Tt] & _) Γr]".
    iMod (read with "α t Ts") as (? wls ?? ->) "(↦s & U & →Ts')".
    iMod (write with "α' Tt") as (? wlt ? ->) "(↦t & U' & →Tt')".
    iDestruct (ty_own_size with "U") as %?.
    iDestruct (ty_own_size with "U'") as %?.
    wp_apply (twp_memcpy wls wlt with "[$↦s $↦t]")=>//. iIntros "[↦s ↦t]".
    iMod ("→Ts'" with "↦s") as (?) "($ & $ & Ts')".
    iMod ("→Tt'" with "↦t U") as (?) "($ & Tt')". iModIntro. iFrame "pre".
    iFrame.
  Qed.
End read_write.
