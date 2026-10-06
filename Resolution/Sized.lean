import Resolution.Collapse
import Resolution.FamilyEnum

/-!
The size part of the invariant: every type of a state has size at most `s`, except that the
right side may be wrapped in `Dᵏ(·)` and `{A:·..⊤}` around such types.  Like the rest of the
invariant it is preserved backward by every rule and by removing variables.
-/

namespace Dsub

/-- A right side of size at most `s` up to the wrappers: `Dᵏ(V)` with `V` of size at most
`s`, or `V = {A:P..⊤}` with `P` of size at most `s`. -/
def Ty.RSized (s : ℕ) : {n : ℕ} → Ty n → Prop
  | _, .top => 1 ≤ s
  | _, .bot => 1 ≤ s
  | _, .sel _ => 1 ≤ s
  | _, .bnd L H => (Ty.bnd L H).size ≤ s ∨ (L = .bot ∧ H.RSized s) ∨ (H = .top ∧ L.size ≤ s)
  | _, .all S T => (Ty.all S T).size ≤ s

@[simp] theorem Ty.size_weaken {n : ℕ} {T : Ty n} : T.weaken.size = T.size := Ty.size_rename T _

theorem Ty.rSized_of_size {n s : ℕ} {T : Ty n} (h : T.size ≤ s) : T.RSized s := by
  cases T with
  | top => exact h
  | bot => exact h
  | sel x => exact h
  | bnd L H => exact Or.inl h
  | all S T => exact h

theorem Ty.rSized_rename {n m s : ℕ} {T : Ty n} {f : Rename n m} :
    (T.rename f).RSized s ↔ T.RSized s := by
  induction T generalizing m with
  | top => exact Iff.rfl
  | bot => exact Iff.rfl
  | sel x => exact Iff.rfl
  | bnd L H _ ihH =>
    simp only [Ty.rename_bnd, Ty.RSized]
    have hL : L.rename f = .bot ↔ L = .bot := by cases L <;> simp
    have hH : H.rename f = .top ↔ H = .top := by cases H <;> simp
    rw [hL, hH, ihH, ← Ty.rename_bnd, Ty.size_rename, Ty.size_rename]
  | all S T =>
    show ((Ty.all S T).rename f).size ≤ s ↔ _
    rw [Ty.size_rename]; rfl

theorem Ty.RSized.one_le {n s : ℕ} {T : Ty n} (h : T.RSized s) : 1 ≤ s := by
  induction T with
  | top => exact h
  | bot => exact h
  | sel x => exact h
  | bnd L H _ ihH =>
    rcases h with h | ⟨_, h⟩ | ⟨_, h⟩
    · simp only [Ty.size] at h; omega
    · exact ihH h
    · have := L.size_pos; omega
  | all S T =>
    have : 1 ≤ (Ty.all S T).size := Ty.size_pos _
    exact le_trans this h

/-- The bounds of a sized right-hand declaration. -/
theorem Ty.RSized.bnd {n s : ℕ} {L H : Ty n} (h : (Ty.bnd L H).RSized s) :
    L.size ≤ s ∧ H.RSized s := by
  have one := h.one_le
  rcases h with h | ⟨rfl, h⟩ | ⟨rfl, h⟩
  · simp only [Ty.size] at h
    exact ⟨by omega, Ty.rSized_of_size (by omega)⟩
  · exact ⟨one, h⟩
  · exact ⟨h, one⟩

/-- The size part of the invariant, for the state `Γ ⊢ S <: U`. -/
structure Sized {n : ℕ} (s : ℕ) (Γ : Ctx n) (S U : Ty n) : Prop where
  left : S.size ≤ s
  right : U.RSized s
  ctx : ∀ x, (Γ.lookup x).size ≤ s

theorem Sized.root {n s : ℕ} {Γ : Ctx n} {S U : Ty n} (hS : S.size ≤ s) (hU : U.size ≤ s)
    (hΓ : ∀ x, (Γ.lookup x).size ≤ s) : Sized s Γ S U :=
  ⟨hS, Ty.rSized_of_size hU, hΓ⟩

theorem Sized.bnd {n s : ℕ} {Γ : Ctx n} {S₁ U₁ S₂ U₂ : Ty n}
    (h : Sized s Γ (.bnd S₁ U₁) (.bnd S₂ U₂)) : Sized s Γ S₂ S₁ ∧ Sized s Γ U₁ U₂ := by
  have hl := h.left
  simp only [Ty.size] at hl
  obtain ⟨h1, h2⟩ := h.right.bnd
  exact ⟨⟨h1, Ty.rSized_of_size (by omega), h.ctx⟩, ⟨by omega, h2, h.ctx⟩⟩

theorem Sized.all {n s : ℕ} {Γ : Ctx n} {S : Ty n} {B B' : Ty (n + 1)}
    (h : Sized s Γ (.all S B) (.all S B')) : Sized s (Γ.push S) B B' := by
  have hl := h.left
  have hr : (Ty.all S B').size ≤ s := h.right
  simp only [Ty.size] at hl hr
  refine ⟨by omega, Ty.rSized_of_size (by omega), ?_⟩
  intro x
  cases x with
  | here => simp only [Ctx.lookup_here, Ty.size_weaken]; omega
  | there x => simp only [Ctx.lookup_there, Ty.size_weaken]; exact h.ctx x

theorem Sized.sel_lower {n s : ℕ} {Γ : Ctx n} {S : Ty n} {x : BVar n}
    (h : Sized s Γ S (.sel x)) : Sized s Γ (Γ.lookup x) (.bnd S .top) :=
  ⟨h.ctx x, Or.inr (Or.inr ⟨rfl, h.left⟩), h.ctx⟩

theorem Sized.sel_upper {n s : ℕ} {Γ : Ctx n} {U : Ty n} {x : BVar n}
    (h : Sized s Γ (.sel x) U) : Sized s Γ (Γ.lookup x) (.bnd .bot U) :=
  ⟨h.ctx x, Or.inr (Or.inl ⟨rfl, h.right⟩), h.ctx⟩

theorem Sized.bad_bounds {n s : ℕ} {Γ : Ctx n} {S U : Ty n} (h : Sized s Γ S U) (x : BVar n) :
    Sized s Γ (Γ.lookup x) (.bnd S .top) ∧ Sized s Γ (Γ.lookup x) (.bnd .bot U) :=
  ⟨⟨h.ctx x, Or.inr (Or.inr ⟨rfl, h.left⟩), h.ctx⟩,
   ⟨h.ctx x, Or.inr (Or.inl ⟨rfl, h.right⟩), h.ctx⟩⟩

/-- Restricting a state along a thinning keeps the size bound. -/
theorem Sized.restrict {m n s : ℕ} {Γ : Ctx n} {θ : Thin m n} {Δ : Ctx m}
    {S U : Ty n} {S' U' : Ty m} (hΔ : Γ.restrict θ = some Δ) (hS : S.unthin θ = some S')
    (hU : U.unthin θ = some U') (h : Sized s Γ S U) : Sized s Δ S' U' := by
  have eS := Ty.unthin_rename hS
  have eU := Ty.unthin_rename hU
  have eΓ := Ctx.restrict_morph hΔ
  subst eS eU
  refine ⟨?_, ?_, ?_⟩
  · rw [← Ty.size_rename _ θ.ren]; exact h.left
  · rw [← Ty.rSized_rename (f := θ.ren)]; exact h.right
  · intro y; rw [← Ty.size_rename _ θ.ren, ← eΓ y]; exact h.ctx _

end Dsub
