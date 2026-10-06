import Dsub

/-! Scratch checks of the definitions: not part of the task. -/

namespace Dsub

/-- Subtyping is reflexive, though only on paths by a rule of its own (Hu and Lhoták,
Lemma 20). -/
theorem Sub.refl : ∀ {n : ℕ} (Γ : Ctx n) (T : Ty n), Sub Γ T T
  | _, _, .top => .top _
  | _, _, .bot => .bot _
  | _, _, .sel x => .refl_sel x
  | _, Γ, .bnd S U => .bnd (Sub.refl Γ S) (Sub.refl Γ U)
  | _, Γ, .all S T => .all (Sub.refl (Γ.push S) T)

/-- `x : {A : ⊤..⊥}`: the bounds of `x.A` are bad. -/
def Γbad : Ctx 1 := Ctx.empty.push (.bnd .top .bot)

example : Γbad.lookup .here = .bnd .top .bot := rfl

/-- Bad bounds give `⊤ <: ⊥`. -/
example : Sub Γbad .top .bot :=
  .bad_bounds .here (.bnd (.top _) (.top _)) (.bnd (.top _) (.bot _))

/-- `x : {A : ⊤..⊤}`: `x.A` is an alias of `⊤`, and `⊤ <: x.A` by its lower bound. -/
def Γalias : Ctx 1 := Ctx.empty.push (.bnd .top .top)

example : Sub Γalias .top (.sel .here) :=
  .sel_lower .here (.bnd (.top _) (.top _))

example : Sub Γalias (.sel .here) .top :=
  .top _

/-- `x : {A : ⊥..⊤}, y : {A : ⊥..⊤}, z : {A : x.A..y.A}`: the harmless use of bad bounds from
Hu and Lhoták (§7.1), `x.A <: y.A` through `z`. -/
def Γzxy : Ctx 3 :=
  ((Ctx.empty.push (.bnd .bot .top)).push (.bnd .bot .top)).push
    (.bnd (.sel (.there .here)) (.sel .here))

def x₃ : BVar 3 := .there (.there .here)
def y₃ : BVar 3 := .there .here

example : Γzxy.lookup .here = .bnd (.sel x₃) (.sel y₃) := rfl

example : Sub Γzxy (.sel x₃) (.sel y₃) :=
  .bad_bounds (Γ := Γzxy) .here (.bnd (.refl_sel _) (.top _)) (.bnd (.bot _) (.refl_sel _))

/-- The kernel function rule compares the results under the shared parameter type. -/
example : Sub Ctx.empty (.all .top (.sel .here)) (.all .top .top) :=
  .all (.top _)

/-! Codes. -/

example : (Ty.bnd .top .bot : Ty 0).code = 3 * Nat.pair 0 1 + 3 := rfl
example : Ty.decode 0 2 = none := by rw [Ty.decode]; simp [BVar.ofNat]   -- no variable in scope
example : Ty.decode 1 2 = some (.sel .here) := by rw [Ty.decode]; simp [BVar.ofNat]

/-- A judgment is recovered from its code. -/
example : Judgment.decode (Judgment.code ⟨Γbad, .top, .bot⟩) = some ⟨Γbad, .top, .bot⟩ :=
  Judgment.decode_code _

/-- Codes are injective. -/
theorem Judgment.code_injective : Function.Injective Judgment.code := by
  intro j₁ j₂ h
  have := Judgment.decode_code j₂
  rw [← h, Judgment.decode_code] at this
  exact Option.some_injective _ this

end Dsub
