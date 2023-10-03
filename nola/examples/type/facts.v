(** * Facts *)

From nola.examples.type Require Export deriv.

Section facts.
  Context `{!tintpGS L Σ}.

  (** ** Behavior of [tintp] *)
  Fact tintp_nat {δ i v} : ⟦ ℕ ⟧{i}(δ) v ⊣⊢ ∃ n : nat, ⌜v = # n⌝.
  Proof. done. Qed.
  Fact tintp_bool {δ i v} : ⟦ 𝔹 ⟧{i}(δ) v ⊣⊢ ∃ b : bool, ⌜v = # b⌝.
  Proof. done. Qed.
  Fact tintp_unit {δ i v} : ⟦ 𝟙 ⟧{i}(δ) v ⊣⊢ ⌜v = # ()⌝.
  Proof. done. Qed.
  Fact tintp_and {δ i T U v} : ⟦ T ∧ᵗ U ⟧{i}(δ) v ⊣⊢ ⟦ T ⟧(δ) v ∗ ⟦ U ⟧(δ) v.
  Proof. done. Qed.
  Fact tintp_pair {δ i T U v} :
    ⟦ T × U ⟧{i}(δ) v ⊣⊢ ∃ u u', ⌜v = (u, u')%V⌝ ∗ ⟦ T ⟧(δ) u ∗ ⟦ U ⟧(δ) u'.
  Proof. done. Qed.
  Fact tintp_fun `{! j ≤ⁿ i} {δ T U v} :
    ⟦ T →(j) U ⟧{i}(δ) v ⊣⊢ □ ∀ u,
      ⟦ T ⟧{i}(δ) u -∗ WP[tinv_wsat δ j] v u [{ ⟦ U ⟧{i}(δ) }].
  Proof. simpl. do 4 f_equiv. exact twpw_tinv_wsat_lt_tinv_wsat. Qed.
  Fact tintp_ref {δ i o j v} {T : _ (;ᵞ)} :
    ⟦ ref[o] T ⟧{i}(δ) v ⊣⊢ ∃ l : loc, ⌜v = # l⌝ ∗ tref (i:=j) δ (l +ₗ o) T.
  Proof. done. Qed.
  Fact tintp_guard {δ i j v} {T : _ (;ᵞ)} :
    ⟦ ▽{j,_} T ⟧{i}(δ) v ⊣⊢ tguard (i:=j) δ T v.
  Proof. done. Qed.
  Fact tintp_forall {δ i j T v} : ⟦ ∀: j, T ⟧{i}(δ) v ⊣⊢ ∀ V, ⟦ T /: V ⟧(δ) v.
  Proof. simpl. do 3 f_equiv. apply rew_eq_hwf. Qed.
  Fact tintp_exist {δ i j T v} : ⟦ ∃: j, T ⟧{i}(δ) v ⊣⊢ ∃ V, ⟦ T /: V ⟧(δ) v.
  Proof. simpl. do 3 f_equiv. apply rew_eq_hwf. Qed.
  Fact tintp_rec `{! j ≤ⁿ i} {δ T v} :
    ⟦ recᵗ: j, T ⟧{i}(δ) v ⊣⊢ ⟦ T /: recᵗ: j, T ⟧(δ) v.
  Proof. rewrite/= rew_eq_hwf. exact tintp_tbump. Qed.
  Fact tintp_subu `{! j <ⁿ i} {δ T v} : ⟦ !ᵘ T ⟧{i}(δ) v ⊣⊢ ⟦ T ⟧(δ) v.
  Proof. exact tintp_lt_tintp. Qed.
End facts.
