import Resolution.Syntax

/-!
Subtyping is preserved by renaming along context morphisms.
-/

namespace Dsub

/-! ### Renaming -/

/-- Subtyping is preserved by context morphisms (not necessarily injective ones). -/
theorem Sub.rename {n : ℕ} {Γ : Ctx n} {S U : Ty n} (h : Sub Γ S U) :
    ∀ {m : ℕ} {Δ : Ctx m} {f : Rename n m}, f.IsCtxMorph Γ Δ →
      Sub Δ (S.rename f) (U.rename f) := by
  induction h with
  | top T => intro m Δ f _; exact .top _
  | bot T => intro m Δ f _; exact .bot _
  | refl_sel x => intro m Δ f _; exact .refl_sel _
  | bnd _ _ ih1 ih2 => intro m Δ f hf; exact .bnd (ih1 hf) (ih2 hf)
  | all _ ih => intro m Δ f hf; exact .all (ih (hf.lift _))
  | sel_lower x _ ih =>
    intro m Δ f hf
    have := ih hf
    rw [← hf x] at this
    exact .sel_lower _ this
  | sel_upper x _ ih =>
    intro m Δ f hf
    have := ih hf
    rw [← hf x] at this
    exact .sel_upper _ this
  | bad_bounds x _ _ ih1 ih2 =>
    intro m Δ f hf
    have h1 := ih1 hf
    have h2 := ih2 hf
    rw [← hf x] at h1 h2
    exact .bad_bounds _ h1 h2

end Dsub
