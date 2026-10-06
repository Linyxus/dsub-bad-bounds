import Resolution.Lemmas

/-!
Derivations with a height bound: `SubH h Γ S U` is a derivation of `Γ ⊢ S <: U` of height at
most `h`.  Renaming along context morphisms keeps the height.
-/

namespace Dsub

/-- Subtyping by a derivation of height at most `h`: leaves at every height, and every other
rule one above its premises. -/
inductive SubH : {n : ℕ} → ℕ → Ctx n → Ty n → Ty n → Prop where
  | top {n h : ℕ} {Γ : Ctx n} (T : Ty n) : SubH h Γ T .top
  | bot {n h : ℕ} {Γ : Ctx n} (T : Ty n) : SubH h Γ .bot T
  | refl_sel {n h : ℕ} {Γ : Ctx n} (x : BVar n) : SubH h Γ (.sel x) (.sel x)
  | bnd {n h : ℕ} {Γ : Ctx n} {S₁ U₁ S₂ U₂ : Ty n} :
      SubH h Γ S₂ S₁ → SubH h Γ U₁ U₂ → SubH (h + 1) Γ (.bnd S₁ U₁) (.bnd S₂ U₂)
  | all {n h : ℕ} {Γ : Ctx n} {S : Ty n} {U₁ U₂ : Ty (n + 1)} :
      SubH h (Γ.push S) U₁ U₂ → SubH (h + 1) Γ (.all S U₁) (.all S U₂)
  | sel_lower {n h : ℕ} {Γ : Ctx n} {S : Ty n} (x : BVar n) :
      SubH h Γ (Γ.lookup x) (.bnd S .top) → SubH (h + 1) Γ S (.sel x)
  | sel_upper {n h : ℕ} {Γ : Ctx n} {U : Ty n} (x : BVar n) :
      SubH h Γ (Γ.lookup x) (.bnd .bot U) → SubH (h + 1) Γ (.sel x) U
  | bad_bounds {n h : ℕ} {Γ : Ctx n} {S U : Ty n} (x : BVar n) :
      SubH h Γ (Γ.lookup x) (.bnd S .top) → SubH h Γ (Γ.lookup x) (.bnd .bot U) →
      SubH (h + 1) Γ S U

theorem SubH.succ {n h : ℕ} {Γ : Ctx n} {S U : Ty n} (d : SubH h Γ S U) : SubH (h + 1) Γ S U := by
  induction d with
  | top T => exact .top T
  | bot T => exact .bot T
  | refl_sel x => exact .refl_sel x
  | bnd _ _ ih1 ih2 => exact .bnd ih1 ih2
  | all _ ih => exact .all ih
  | sel_lower x _ ih => exact .sel_lower x ih
  | sel_upper x _ ih => exact .sel_upper x ih
  | bad_bounds x _ _ ih1 ih2 => exact .bad_bounds x ih1 ih2

theorem SubH.mono {n h h' : ℕ} {Γ : Ctx n} {S U : Ty n} (d : SubH h Γ S U) (le : h ≤ h') :
    SubH h' Γ S U := by
  induction le with
  | refl => exact d
  | step _ ih => exact ih.succ

theorem SubH.sub {n h : ℕ} {Γ : Ctx n} {S U : Ty n} (d : SubH h Γ S U) : Sub Γ S U := by
  induction d with
  | top T => exact .top T
  | bot T => exact .bot T
  | refl_sel x => exact .refl_sel x
  | bnd _ _ ih1 ih2 => exact .bnd ih1 ih2
  | all _ ih => exact .all ih
  | sel_lower x _ ih => exact .sel_lower x ih
  | sel_upper x _ ih => exact .sel_upper x ih
  | bad_bounds x _ _ ih1 ih2 => exact .bad_bounds x ih1 ih2

theorem Sub.subH {n : ℕ} {Γ : Ctx n} {S U : Ty n} (d : Sub Γ S U) : ∃ h, SubH h Γ S U := by
  induction d with
  | top T => exact ⟨0, .top T⟩
  | bot T => exact ⟨0, .bot T⟩
  | refl_sel x => exact ⟨0, .refl_sel x⟩
  | bnd _ _ ih1 ih2 =>
    obtain ⟨h1, d1⟩ := ih1
    obtain ⟨h2, d2⟩ := ih2
    exact ⟨max h1 h2 + 1, .bnd (d1.mono (le_max_left _ _)) (d2.mono (le_max_right _ _))⟩
  | all _ ih =>
    obtain ⟨h, d⟩ := ih
    exact ⟨h + 1, .all d⟩
  | sel_lower x _ ih =>
    obtain ⟨h, d⟩ := ih
    exact ⟨h + 1, .sel_lower x d⟩
  | sel_upper x _ ih =>
    obtain ⟨h, d⟩ := ih
    exact ⟨h + 1, .sel_upper x d⟩
  | bad_bounds x _ _ ih1 ih2 =>
    obtain ⟨h1, d1⟩ := ih1
    obtain ⟨h2, d2⟩ := ih2
    exact ⟨max h1 h2 + 1,
      .bad_bounds x (d1.mono (le_max_left _ _)) (d2.mono (le_max_right _ _))⟩

theorem Sub.iff_subH {n : ℕ} {Γ : Ctx n} {S U : Ty n} : Sub Γ S U ↔ ∃ h, SubH h Γ S U :=
  ⟨Sub.subH, fun ⟨_, d⟩ => d.sub⟩

theorem Sub_iff_SubH {n : ℕ} {Γ : Ctx n} {S U : Ty n} : Sub Γ S U ↔ ∃ h, SubH h Γ S U :=
  Sub.iff_subH

/-- Renaming along a context morphism keeps the height. -/
theorem SubH.rename {n h : ℕ} {Γ : Ctx n} {S U : Ty n} (d : SubH h Γ S U) :
    ∀ {m : ℕ} {Δ : Ctx m} {f : Rename n m}, f.IsCtxMorph Γ Δ →
      SubH h Δ (S.rename f) (U.rename f) := by
  induction d with
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
