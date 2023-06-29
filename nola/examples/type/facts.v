(** * Facts *)

From nola.examples.type Require Export sintp.

Section facts.
  Context `{!tintpGS L Σ}.

  (** ** Behavior of [tintp] *)
  Fact tintp_nat {s i v} : ⟦ ℕ ⟧{i}(s) v ⊣⊢ ∃ n : nat, ⌜v = # n⌝.
  Proof. done. Qed.
  Fact tintp_bool {s i v} : ⟦ 𝔹 ⟧{i}(s) v ⊣⊢ ∃ b : bool, ⌜v = # b⌝.
  Proof. done. Qed.
  Fact tintp_unit {s i v} : ⟦ 𝟙 ⟧{i}(s) v ⊣⊢ ⌜v = # ()⌝.
  Proof. done. Qed.
  Fact tintp_and {s i T U v} : ⟦ T ∧ᵗ U ⟧{i}(s) v ⊣⊢ ⟦ T ⟧(s) v ∗ ⟦ U ⟧(s) v.
  Proof. done. Qed.
  Fact tintp_pair {s i T U v} :
    ⟦ T × U ⟧{i}(s) v ⊣⊢ ∃ u u', ⌜v = (u, u')%V⌝ ∗ ⟦ T ⟧(s) u ∗ ⟦ U ⟧(s) u'.
  Proof. done. Qed.
  Fact tintp_fun `{! j ≤ⁿ i} {s T U v} :
    ⟦ T →(j) U ⟧{i}(s) v ⊣⊢ □ ∀ u,
      ⟦ T ⟧{i}(s) u -∗ WP[tinv_wsat s j] v u [{ ⟦ U ⟧{i}(s) }].
  Proof. simpl. do 4 f_equiv. exact twpw_tinv_wsat_lt_tinv_wsat. Qed.
  Fact tintp_ref {s i o j v} {T : _ (;ᵞ)} :
    ⟦ ref[o] T ⟧{i}(s) v ⊣⊢ ∃ l : loc, ⌜v = # l⌝ ∗ tref (i:=j) s (l +ₗ o) T.
  Proof. done. Qed.
  Fact tintp_guard {s i j v} {T : _ (;ᵞ)} :
    ⟦ ▽{j,_} T ⟧{i}(s) v ⊣⊢ tguard (i:=j) s T v.
  Proof. done. Qed.
  Fact tintp_forall {s i j T v} : ⟦ ∀: j, T ⟧{i}(s) v ⊣⊢ ∀ V, ⟦ T /: V ⟧(s) v.
  Proof. simpl. do 3 f_equiv. apply rew_eq_hwf. Qed.
  Fact tintp_exist {s i j T v} : ⟦ ∃: j, T ⟧{i}(s) v ⊣⊢ ∃ V, ⟦ T /: V ⟧(s) v.
  Proof. simpl. do 3 f_equiv. apply rew_eq_hwf. Qed.
  Fact tintp_rec `{! j ≤ⁿ i} {s T v} :
    ⟦ recᵗ: j, T ⟧{i}(s) v ⊣⊢ ⟦ T /: recᵗ: j, T ⟧(s) v.
  Proof. rewrite/= rew_eq_hwf. exact tintp_tbump. Qed.
  Fact tintp_subu `{! j <ⁿ i} {s T v} : ⟦ !ᵘ T ⟧{i}(s) v ⊣⊢ ⟦ T ⟧(s) v.
  Proof. exact tintp_lt_tintp. Qed.
End facts.
