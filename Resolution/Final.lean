import Resolution.PrimDecide
import Resolution.BoundPrim
import Resolution.NormFam

/-!
# Decidability

The bounds at a query `m` are read off `m` itself: every type of the judgment it names has
size and `∀`-nesting at most `m + 1`, and its scope is at most `m`. Lemma 4 at these bounds
gives the `Norm` predicate `GoodB` the code-level decision needs.
-/

namespace Dsub

theorem Ty.nu_le_size {n : ℕ} (T : Ty n) : T.nu ≤ T.size := by
  induction T with
  | top => simp [Ty.nu]
  | bot => simp [Ty.nu]
  | sel => simp [Ty.nu]
  | bnd S U ihS ihU => simp only [Ty.nu, Ty.size]; omega
  | all S T ihS ihT => simp only [Ty.nu, Ty.size]; omega

theorem Ty.size_le_code {n : ℕ} (T : Ty n) : T.size ≤ T.code + 1 := by
  induction T with
  | top => simp [Ty.size, Ty.code]
  | bot => simp [Ty.size, Ty.code]
  | sel => simp [Ty.size, Ty.code]
  | bnd S U ihS ihU =>
    have := Nat.left_le_pair S.code U.code
    have := Nat.right_le_pair S.code U.code
    simp only [Ty.size, Ty.code]; omega
  | all S T ihS ihT =>
    have := Nat.left_le_pair S.code T.code
    have := Nat.right_le_pair S.code T.code
    simp only [Ty.size, Ty.code]; omega

theorem Ctx.lookup_size_le : ∀ {n : ℕ} (Γ : Ctx n) (x : BVar n),
    (Γ.lookup x).size ≤ Γ.code + 1
  | _, .push Γ T, .here => by
    have := Nat.right_le_pair Γ.code T.code
    have := Ty.size_le_code T
    simp only [Ctx.lookup, Ty.weaken, Ty.size_rename, Ctx.code]; omega
  | _, .push Γ T, .there x => by
    have := Nat.left_le_pair Γ.code T.code
    have := Ctx.lookup_size_le Γ x
    simp only [Ctx.lookup, Ty.weaken, Ty.size_rename, Ctx.code]; omega

/-- The scope bound at a query. -/
def boundL (m : ℕ) : ℕ := m + Bnd (m + 1) (m + 1) m

/-- The size bound at a query. -/
def boundS (m : ℕ) : ℕ := m + 1

theorem boundL_primrec : Primrec boundL :=
  Primrec.nat_add.comp .id (Bnd_primrec.comp
    ((Primrec.succ).pair ((Primrec.succ).pair .id)))

theorem boundS_primrec : Primrec boundS := Primrec.succ

theorem GoodB.mono_base {N s n₀ n₁ B : ℕ} {j : Judgment} (h : GoodB N s n₀ B j)
    (hn : n₀ ≤ n₁) : GoodB N s n₁ B j :=
  let ⟨a, h1, h2, h3, h4⟩ := h; ⟨a, h1, h2, le_trans h3 hn, h4⟩

theorem queryOK (m : ℕ) : QueryOK boundL boundS m := by
  rintro ⟨Γ, S, U⟩ hj -
  simp only [Judgment.code] at hj
  have hn : _ ≤ m := hj ▸ Nat.left_le_pair _ _
  have hr : Nat.pair Γ.code (Nat.pair S.code U.code) ≤ m := hj ▸ Nat.right_le_pair _ _
  have hΓc := le_trans (Nat.left_le_pair _ _) hr
  have hSUc := le_trans (Nat.right_le_pair _ _) hr
  have hSc := le_trans (Nat.left_le_pair _ _) hSUc
  have hUc := le_trans (Nat.right_le_pair _ _) hSUc
  have hS : S.size ≤ m + 1 := le_trans (Ty.size_le_code S) (by omega)
  have hU : U.size ≤ m + 1 := le_trans (Ty.size_le_code U) (by omega)
  have hΓ : ∀ x, (Γ.lookup x).size ≤ m + 1 := fun x =>
    le_trans (Ctx.lookup_size_le Γ x) (by omega)
  refine ⟨le_trans hn (Nat.le_add_right _ _), Ctx.bounded_of_lookup hΓ, hS, hU,
    Nat.le_add_left _ _, GoodB (m + 1) (m + 1) m (Bnd (m + 1) (m + 1) m),
    GoodB.norm (lemma4 _ _ _), ?_⟩
  exact (GoodB.root (le_trans (Ty.nu_le_size S) hS) (le_trans (Ty.nu_le_size U) hU)
    (fun x => le_trans (Ty.nu_le_size _) (hΓ x)) hS hU hΓ).mono_base hn

/-- Subtyping in kernel D<: with bad bounds is decidable. -/
theorem subtyping_computable : ComputablePred Subtyping :=
  Subtyping_computable_of_bounds boundL_primrec boundS_primrec queryOK

end Dsub
