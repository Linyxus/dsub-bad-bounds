import Resolution.Syntax

/-!
Renaming and weakening of subtyping, reflexivity, and inversion: for each shape of the right
side, the rules that can conclude a judgment.
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

/-- Weakening. -/
theorem Sub.weaken {n : ℕ} {Γ : Ctx n} {S U : Ty n} (h : Sub Γ S U) (T : Ty n) :
    Sub (Γ.push T) S.weaken U.weaken :=
  h.rename (Rename.isCtxMorph_succ Γ T)

/-! ### Reflexivity -/

theorem Sub.reflex {n : ℕ} (Γ : Ctx n) (T : Ty n) : Sub Γ T T := by
  induction T with
  | top => exact .top _
  | bot => exact .bot _
  | bnd S U ih1 ih2 => exact .bnd (ih1 Γ) (ih2 Γ)
  | sel x => exact .refl_sel x
  | all S T _ ih2 => exact .all (ih2 (Γ.push S))

/-! ### Inversion -/

/-- The rules that can conclude `Γ ⊢ S <: U`, in order: top, bot, refl_sel, bnd, all,
sel_lower, sel_upper, bad_bounds. -/
theorem Sub.iff {n : ℕ} {Γ : Ctx n} {S U : Ty n} :
    Sub Γ S U ↔
      U = .top ∨ S = .bot ∨ (∃ x, S = .sel x ∧ U = .sel x) ∨
      (∃ S₁ U₁ S₂ U₂, S = .bnd S₁ U₁ ∧ U = .bnd S₂ U₂ ∧ Sub Γ S₂ S₁ ∧ Sub Γ U₁ U₂) ∨
      (∃ P T₁ T₂, S = .all P T₁ ∧ U = .all P T₂ ∧ Sub (Γ.push P) T₁ T₂) ∨
      (∃ x, U = .sel x ∧ Sub Γ (Γ.lookup x) (.bnd S .top)) ∨
      (∃ x, S = .sel x ∧ Sub Γ (Γ.lookup x) (.bnd .bot U)) ∨
      (∃ x, Sub Γ (Γ.lookup x) (.bnd S .top) ∧ Sub Γ (Γ.lookup x) (.bnd .bot U)) := by
  constructor
  · intro h
    cases h with
    | top => exact Or.inl rfl
    | bot => exact Or.inr (Or.inl rfl)
    | refl_sel x => exact Or.inr (Or.inr (Or.inl ⟨x, rfl, rfl⟩))
    | bnd h1 h2 => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, rfl, rfl, h1, h2⟩)))
    | all h => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl, rfl, h⟩))))
    | sel_lower x h => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨x, rfl, h⟩)))))
    | sel_upper x h =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨x, rfl, h⟩))))))
    | bad_bounds x h1 h2 =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨x, h1, h2⟩))))))
  · rintro (h | h | ⟨x, rfl, rfl⟩ | ⟨_, _, _, _, rfl, rfl, h1, h2⟩ | ⟨_, _, _, rfl, rfl, h⟩ |
      ⟨x, rfl, h⟩ | ⟨x, rfl, h⟩ | ⟨x, h1, h2⟩)
    · subst h; exact .top _
    · subst h; exact .bot _
    · exact .refl_sel x
    · exact .bnd h1 h2
    · exact .all h
    · exact .sel_lower x h
    · exact .sel_upper x h
    · exact .bad_bounds x h1 h2

theorem Sub.inv_top {n : ℕ} {Γ : Ctx n} {P : Ty n} : Sub Γ P .top ↔ True :=
  ⟨fun _ => trivial, fun _ => .top _⟩

theorem Sub.inv_bot {n : ℕ} {Γ : Ctx n} {P : Ty n} :
    Sub Γ P .bot ↔
      P = .bot ∨ (∃ y, P = .sel y ∧ Sub Γ (Γ.lookup y) (.bnd .bot .bot)) ∨
      (∃ x, Sub Γ (Γ.lookup x) (.bnd P .top) ∧ Sub Γ (Γ.lookup x) (.bnd .bot .bot)) := by
  rw [Sub.iff]
  constructor
  · rintro (h | h | ⟨_, _, h⟩ | ⟨_, _, _, _, _, h, _⟩ | ⟨_, _, _, _, h, _⟩ | ⟨_, h, _⟩ | h | h)
    · simp at h
    · exact Or.inl h
    · simp at h
    · simp at h
    · simp at h
    · simp at h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

theorem Sub.inv_sel {n : ℕ} {Γ : Ctx n} {P : Ty n} {x : BVar n} :
    Sub Γ P (.sel x) ↔
      P = .bot ∨ P = .sel x ∨ Sub Γ (Γ.lookup x) (.bnd P .top) ∨
      (∃ y, P = .sel y ∧ Sub Γ (Γ.lookup y) (.bnd .bot (.sel x))) ∨
      (∃ z, Sub Γ (Γ.lookup z) (.bnd P .top) ∧ Sub Γ (Γ.lookup z) (.bnd .bot (.sel x))) := by
  rw [Sub.iff]
  constructor
  · rintro (h | h | ⟨_, h, h'⟩ | ⟨_, _, _, _, _, h, _⟩ | ⟨_, _, _, _, h, _⟩ | ⟨_, h, h'⟩ | h | h)
    · simp at h
    · exact Or.inl h
    · cases h'; exact Or.inr (Or.inl h)
    · simp at h
    · simp at h
    · cases h; exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · rintro (h | h | h | h | h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨x, h, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨x, rfl, h⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

theorem Sub.inv_bnd {n : ℕ} {Γ : Ctx n} {P S₂ U₂ : Ty n} :
    Sub Γ P (.bnd S₂ U₂) ↔
      P = .bot ∨ (∃ S₁ U₁, P = .bnd S₁ U₁ ∧ Sub Γ S₂ S₁ ∧ Sub Γ U₁ U₂) ∨
      (∃ y, P = .sel y ∧ Sub Γ (Γ.lookup y) (.bnd .bot (.bnd S₂ U₂))) ∨
      (∃ x, Sub Γ (Γ.lookup x) (.bnd P .top) ∧ Sub Γ (Γ.lookup x) (.bnd .bot (.bnd S₂ U₂))) := by
  rw [Sub.iff]
  constructor
  · rintro (h | h | ⟨_, _, h⟩ | ⟨_, _, _, _, h, h', h1, h2⟩ | ⟨_, _, _, _, h, _⟩ | ⟨_, h, _⟩ |
      h | h)
    · simp at h
    · exact Or.inl h
    · simp at h
    · cases h'; exact Or.inr (Or.inl ⟨_, _, h, h1, h2⟩)
    · simp at h
    · simp at h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · rintro (h | ⟨_, _, h, h1, h2⟩ | h | h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, h, rfl, h1, h2⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

theorem Sub.inv_all {n : ℕ} {Γ : Ctx n} {P S : Ty n} {T₂ : Ty (n + 1)} :
    Sub Γ P (.all S T₂) ↔
      P = .bot ∨ (∃ T₁, P = .all S T₁ ∧ Sub (Γ.push S) T₁ T₂) ∨
      (∃ y, P = .sel y ∧ Sub Γ (Γ.lookup y) (.bnd .bot (.all S T₂))) ∨
      (∃ x, Sub Γ (Γ.lookup x) (.bnd P .top) ∧ Sub Γ (Γ.lookup x) (.bnd .bot (.all S T₂))) := by
  rw [Sub.iff]
  constructor
  · rintro (h | h | ⟨_, _, h⟩ | ⟨_, _, _, _, _, h, _⟩ | ⟨_, _, _, h, h', h1⟩ | ⟨_, h, _⟩ |
      h | h)
    · simp at h
    · exact Or.inl h
    · simp at h
    · simp at h
    · cases h'; exact Or.inr (Or.inl ⟨_, h, h1⟩)
    · simp at h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · rintro (h | ⟨_, h, h1⟩ | h | h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, h, rfl, h1⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

/-- Inversion for nested declarations `{A:⊥..{A:⊥..…V}}`. -/
theorem Sub.inv_dN {n : ℕ} {Γ : Ctx n} {P V : Ty n} {k : ℕ} :
    Sub Γ P (Ty.dN (k + 1) V) ↔
      P = .bot ∨ (∃ L H, P = .bnd L H ∧ Sub Γ H (Ty.dN k V)) ∨
      (∃ y, P = .sel y ∧ Sub Γ (Γ.lookup y) (Ty.dN (k + 2) V)) ∨
      (∃ x, Sub Γ (Γ.lookup x) (.bnd P .top) ∧ Sub Γ (Γ.lookup x) (Ty.dN (k + 2) V)) := by
  rw [Ty.dN_succ, Sub.inv_bnd]
  constructor
  · rintro (h | ⟨_, _, h, _, h2⟩ | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨_, _, h, h2⟩)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · rintro (h | ⟨_, _, h, h2⟩ | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨_, _, h, .bot _, h2⟩)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

end Dsub
