(** * Facts *)

From nola.examples.type Require Export deriv.

Section facts.
  Context `{!tintpGS L Σ}.

  (** ** Behavior of [tintp] *)
  Fact tintp_nat {d i v} : ⟦ ℕ ⟧{i}(d) v ⊣⊢ ∃ n : nat, ⌜v = # n⌝.
  Proof. done. Qed.
  Fact tintp_bool {d i v} : ⟦ 𝔹 ⟧{i}(d) v ⊣⊢ ∃ b : bool, ⌜v = # b⌝.
  Proof. done. Qed.
  Fact tintp_unit {d i v} : ⟦ 𝟙 ⟧{i}(d) v ⊣⊢ ⌜v = # ()⌝.
  Proof. done. Qed.
  Fact tintp_and {d i T U v} : ⟦ T ∧ᵗ U ⟧{i}(d) v ⊣⊢ ⟦ T ⟧(d) v ∗ ⟦ U ⟧(d) v.
  Proof. done. Qed.
  Fact tintp_pair {d i T U v} :
    ⟦ T × U ⟧{i}(d) v ⊣⊢ ∃ u u', ⌜v = (u, u')%V⌝ ∗ ⟦ T ⟧(d) u ∗ ⟦ U ⟧(d) u'.
  Proof. done. Qed.
  Fact tintp_fun `{! j ≤ⁿ i} {d T U v} :
    ⟦ T →(j) U ⟧{i}(d) v ⊣⊢ □ ∀ u,
      ⟦ T ⟧{i}(d) u -∗ WP[tinv_wsat d j] v u [{ ⟦ U ⟧{i}(d) }].
  Proof. simpl. do 4 f_equiv. exact twpw_tinv_wsat_lt_tinv_wsat. Qed.
  Fact tintp_ref {d i o j v} {T : _ (;ᵞ)} :
    ⟦ ref[o] T ⟧{i}(d) v ⊣⊢ ∃ l : loc, ⌜v = # l⌝ ∗ tref (i:=j) d (l +ₗ o) T.
  Proof. done. Qed.
  Fact tintp_guard {d i j v} {T : _ (;ᵞ)} :
    ⟦ ▽{j,_} T ⟧{i}(d) v ⊣⊢ tguard (i:=j) d T v.
  Proof. done. Qed.
  Fact tintp_forall {d i j T v} : ⟦ ∀: j, T ⟧{i}(d) v ⊣⊢ ∀ V, ⟦ T /: V ⟧(d) v.
  Proof. simpl. do 3 f_equiv. apply rew_eq_hwf. Qed.
  Fact tintp_exist {d i j T v} : ⟦ ∃: j, T ⟧{i}(d) v ⊣⊢ ∃ V, ⟦ T /: V ⟧(d) v.
  Proof. simpl. do 3 f_equiv. apply rew_eq_hwf. Qed.
  Fact tintp_rec `{! j ≤ⁿ i} {d T v} :
    ⟦ recᵗ: j, T ⟧{i}(d) v ⊣⊢ ⟦ T /: recᵗ: j, T ⟧(d) v.
  Proof. rewrite/= rew_eq_hwf. exact tintp_tbump. Qed.
  Fact tintp_subu `{! j <ⁿ i} {d T v} : ⟦ !ᵘ T ⟧{i}(d) v ⊣⊢ ⟦ T ⟧(d) v.
  Proof. exact tintp_lt_tintp. Qed.
End facts.
