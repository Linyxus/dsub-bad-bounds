import Resolution.NormFam

/-!
# Glue

The bounds of an input judgment, and the reduction of `Subtyping` to `decideFam` at those
bounds, given Lemma 4 for every choice of the bounds.
-/

namespace Dsub

/-- The `∀`-nesting depth of a judgment: the maximum over its two types and its context. -/
def Judgment.nu (j : Judgment) : ℕ :=
  max (max j.S.nu j.U.nu) (Finset.univ.sup fun x => (j.Γ.lookup x).nu)

/-- The size bound of a judgment, at least `1`. -/
def Judgment.sz (j : Judgment) : ℕ :=
  max 1 (max (max j.S.size j.U.size) (Finset.univ.sup fun x => (j.Γ.lookup x).size))

/-- The decider at the bounds of the input. -/
def Judgment.decideAt (Bnd : ℕ → ℕ → ℕ → ℕ) (j : Judgment) : Bool :=
  decideFam (j.n + Bnd j.nu j.sz j.n) j.sz j

theorem Judgment.decideAt_iff {Bnd : ℕ → ℕ → ℕ → ℕ}
    (L4 : ∀ N s n₀, Lemma4 N s n₀ (Bnd N s n₀)) (j : Judgment) :
    j.decideAt Bnd = true ↔ j.Holds := by
  obtain ⟨Γ, S, U⟩ := j
  have hΓ : ∀ x, (Γ.lookup x).nu ≤ Judgment.nu ⟨Γ, S, U⟩ := fun x =>
    le_max_of_le_right (Finset.le_sup (f := fun x => (Γ.lookup x).nu) (Finset.mem_univ x))
  have hΓ' : ∀ x, (Γ.lookup x).size ≤ Judgment.sz ⟨Γ, S, U⟩ := fun x =>
    le_max_of_le_right (le_max_of_le_right
      (Finset.le_sup (f := fun x => (Γ.lookup x).size) (Finset.mem_univ x)))
  exact decideFam_iff_of_lemma4 (L4 _ _ _) (le_max_left _ _)
    (le_max_of_le_left (le_max_left _ _)) (le_max_of_le_left (le_max_right _ _)) hΓ
    (le_max_of_le_right (le_max_of_le_left (le_max_left _ _)))
    (le_max_of_le_right (le_max_of_le_left (le_max_right _ _))) hΓ'

/-- `Subtyping` is decidable once Lemma 4 holds for a bound `Bnd` and the decider at the
bounds of the input is computable on codes. -/
theorem decidable_of {Bnd : ℕ → ℕ → ℕ → ℕ} (L4 : ∀ N s n₀, Lemma4 N s n₀ (Bnd N s n₀))
    (hc : ComputablePred fun m => ∃ j, Judgment.decode m = some j ∧ j.decideAt Bnd = true) :
    ComputablePred Subtyping := by
  have : (fun m => ∃ j, Judgment.decode m = some j ∧ j.decideAt Bnd = true) = Subtyping := by
    funext m
    simp only [Subtyping, Judgment.decideAt_iff L4]
  rwa [this] at hc

end Dsub
