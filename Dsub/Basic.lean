import Mathlib.Computability.Halting

/-!
# Kernel D<: with bad bounds

D<: is the fragment of DOT (dependent object types) with type members and path-dependent
types but without self types, intersections or objects. A type member declaration
`{A : S..U}` has a lower bound `S` and an upper bound `U`, and a variable `x` whose type has
such a member gives the path type `x.A`, which lies between those bounds. Dependent function
types `∀(x : S) T` bind `x` in `T`.

Subtyping is given in the syntax-directed style of Hu and Lhoták (POPL 2020), with the
*kernel* rule for function types, which compares the result types only when the parameter
types are identical, and with the *bad bounds* rule `BB`: if the type of a variable `x` has a
member with lower bound `S` and one with upper bound `U`, then `S <: U`. There is no
transitivity rule.

Syntax is intrinsically scoped: `Ty n` is the type of types with `n` variables in scope, which
are de Bruijn indices `BVar n`. A context `Ctx n` gives each of the `n` variables a type,
written in the scope of the variables before it, so every context is well formed by
construction.
-/

namespace Dsub

/-- A variable in a scope of `n` variables, de Bruijn indexed: `here` is the most recently
bound one. -/
inductive BVar : ℕ → Type where
  | here {n : ℕ} : BVar (n + 1)
  | there {n : ℕ} : BVar n → BVar (n + 1)
  deriving DecidableEq

/-- Types with `n` variables in scope. `bnd S U` is the type member declaration
`{A : S..U}`, `sel x` the path type `x.A`, and `all S T` the dependent function type
`∀(x : S) T`, where `T` refers to `x` as index `0`. -/
inductive Ty : ℕ → Type where
  | top {n : ℕ} : Ty n
  | bot {n : ℕ} : Ty n
  | bnd {n : ℕ} : Ty n → Ty n → Ty n
  | sel {n : ℕ} : BVar n → Ty n
  | all {n : ℕ} : Ty n → Ty (n + 1) → Ty n
  deriving DecidableEq

/-- A renaming maps the variables of one scope to those of another. -/
structure Rename (n m : ℕ) where
  var : BVar n → BVar m

/-- Lifts a renaming under a binder: the new variable maps to itself. -/
def Rename.lift {n m : ℕ} (f : Rename n m) : Rename (n + 1) (m + 1) where
  var
    | .here => .here
    | .there x => .there (f.var x)

/-- The renaming that weakens every variable by one binder. -/
def Rename.succ {n : ℕ} : Rename n (n + 1) where
  var := .there

/-- Applies a renaming to a type. -/
def Ty.rename {n m : ℕ} : Ty n → Rename n m → Ty m
  | .top, _ => .top
  | .bot, _ => .bot
  | .bnd S U, f => .bnd (S.rename f) (U.rename f)
  | .sel x, f => .sel (f.var x)
  | .all S T, f => .all (S.rename f) (T.rename f.lift)

/-- Weakens a type into the scope of one more variable. -/
def Ty.weaken {n : ℕ} (T : Ty n) : Ty (n + 1) :=
  T.rename Rename.succ

/-- A context: the types of the variables in scope, each written in the scope of the
variables bound before it. -/
inductive Ctx : ℕ → Type where
  | empty : Ctx 0
  | push {n : ℕ} : Ctx n → Ty n → Ctx (n + 1)

/-- The type of a variable, `Γ(x)`, weakened into the scope of the whole context. -/
def Ctx.lookup {n : ℕ} : Ctx n → BVar n → Ty n
  | .push _ T, .here => T.weaken
  | .push Γ _, .there x => (Γ.lookup x).weaken

/-- Subtyping in kernel D<: with bad bounds: `Sub Γ S U` is `Γ ⊢ S <: U`. -/
inductive Sub : {n : ℕ} → Ctx n → Ty n → Ty n → Prop where
  | top {n : ℕ} {Γ : Ctx n} (T : Ty n) : Sub Γ T .top
  | bot {n : ℕ} {Γ : Ctx n} (T : Ty n) : Sub Γ .bot T
  | refl_sel {n : ℕ} {Γ : Ctx n} (x : BVar n) : Sub Γ (.sel x) (.sel x)
  | bnd {n : ℕ} {Γ : Ctx n} {S₁ U₁ S₂ U₂ : Ty n} :
      Sub Γ S₂ S₁ → Sub Γ U₁ U₂ → Sub Γ (.bnd S₁ U₁) (.bnd S₂ U₂)
  | all {n : ℕ} {Γ : Ctx n} {S : Ty n} {U₁ U₂ : Ty (n + 1)} :
      Sub (Γ.push S) U₁ U₂ → Sub Γ (.all S U₁) (.all S U₂)
  | sel_lower {n : ℕ} {Γ : Ctx n} {S : Ty n} (x : BVar n) :
      Sub Γ (Γ.lookup x) (.bnd S .top) → Sub Γ S (.sel x)
  | sel_upper {n : ℕ} {Γ : Ctx n} {U : Ty n} (x : BVar n) :
      Sub Γ (Γ.lookup x) (.bnd .bot U) → Sub Γ (.sel x) U
  | bad_bounds {n : ℕ} {Γ : Ctx n} {S U : Ty n} (x : BVar n) :
      Sub Γ (Γ.lookup x) (.bnd S .top) → Sub Γ (Γ.lookup x) (.bnd .bot U) → Sub Γ S U

/-- An instance of the subtyping problem: a context and two types over it. -/
structure Judgment where
  {n : ℕ}
  Γ : Ctx n
  S : Ty n
  U : Ty n

/-- The judgment holds. -/
def Judgment.Holds (j : Judgment) : Prop :=
  Sub j.Γ j.S j.U

/-! ## Codes

Judgments are coded by naturals, with `Nat.pair` for the binary constructors, which fixes
what it means for the subtyping problem to be decidable: a decision procedure is given the
code of a judgment. `decode` inverts `code`. -/

/-- The index of a variable. -/
def BVar.toNat {n : ℕ} : BVar n → ℕ
  | .here => 0
  | .there x => x.toNat + 1

/-- The variable with a given index in a given scope, if any. -/
def BVar.ofNat : (n : ℕ) → ℕ → Option (BVar n)
  | 0, _ => none
  | _ + 1, 0 => some .here
  | n + 1, k + 1 => (BVar.ofNat n k).map .there

theorem BVar.ofNat_toNat {n : ℕ} : ∀ x : BVar n, BVar.ofNat n x.toNat = some x
  | .here => rfl
  | .there x => by simp [BVar.toNat, BVar.ofNat, BVar.ofNat_toNat x]

/-- The code of a type. -/
def Ty.code {n : ℕ} : Ty n → ℕ
  | .top => 0
  | .bot => 1
  | .sel x => 3 * x.toNat + 2
  | .bnd S U => 3 * Nat.pair S.code U.code + 3
  | .all S T => 3 * Nat.pair S.code T.code + 4

/-- The type with a given code in a given scope, if any. -/
def Ty.decode (n : ℕ) : ℕ → Option (Ty n)
  | 0 => some .top
  | 1 => some .bot
  | m + 2 =>
    if m % 3 = 0 then (BVar.ofNat n (m / 3)).map .sel
    else if m % 3 = 1 then do
      let S ← Ty.decode n (Nat.unpair (m / 3)).1
      let U ← Ty.decode n (Nat.unpair (m / 3)).2
      pure (.bnd S U)
    else do
      let S ← Ty.decode n (Nat.unpair (m / 3)).1
      let T ← Ty.decode (n + 1) (Nat.unpair (m / 3)).2
      pure (.all S T)
termination_by m => m
decreasing_by
  all_goals
    have h1 := Nat.unpair_left_le (m / 3)
    have h2 := Nat.unpair_right_le (m / 3)
    omega

theorem Ty.decode_code {n : ℕ} : ∀ (T : Ty n), Ty.decode n T.code = some T := by
  intro T
  induction T with
  | top => rw [show (Ty.top : Ty _).code = 0 from rfl, Ty.decode]
  | bot => rw [show (Ty.bot : Ty _).code = 1 from rfl, Ty.decode]
  | sel x =>
    rw [show (Ty.sel x).code = 3 * x.toNat + 2 from rfl, Ty.decode]
    have e1 : (3 * x.toNat) % 3 = 0 := by omega
    have e2 : (3 * x.toNat) / 3 = x.toNat := by omega
    simp [e1, e2, BVar.ofNat_toNat]
  | bnd S U ihS ihU =>
    rw [show (Ty.bnd S U).code = 3 * Nat.pair S.code U.code + 1 + 2 from rfl, Ty.decode]
    have e1 : (3 * Nat.pair S.code U.code + 1) % 3 = 1 := by omega
    have e2 : (3 * Nat.pair S.code U.code + 1) / 3 = Nat.pair S.code U.code := by omega
    simp [e1, e2, Nat.unpair_pair, ihS, ihU]
  | all S T ihS ihT =>
    rw [show (Ty.all S T).code = 3 * Nat.pair S.code T.code + 2 + 2 from rfl, Ty.decode]
    have e1 : (3 * Nat.pair S.code T.code + 2) % 3 = 2 := by omega
    have e2 : (3 * Nat.pair S.code T.code + 2) / 3 = Nat.pair S.code T.code := by omega
    simp [e1, e2, Nat.unpair_pair, ihS, ihT]

/-- The code of a context. -/
def Ctx.code {n : ℕ} : Ctx n → ℕ
  | .empty => 0
  | .push Γ T => Nat.pair Γ.code T.code + 1

/-- The context with a given code and scope, if any. -/
def Ctx.decode : (n : ℕ) → ℕ → Option (Ctx n)
  | 0, 0 => some .empty
  | 0, _ + 1 => none
  | _ + 1, 0 => none
  | n + 1, m + 1 => do
    let Γ ← Ctx.decode n (Nat.unpair m).1
    let T ← Ty.decode n (Nat.unpair m).2
    pure (.push Γ T)

theorem Ctx.decode_code {n : ℕ} : ∀ (Γ : Ctx n), Ctx.decode n Γ.code = some Γ := by
  intro Γ
  induction Γ with
  | empty => simp [Ctx.code, Ctx.decode]
  | push Γ T ih =>
    rw [show (Ctx.push Γ T).code = Nat.pair Γ.code T.code + 1 from rfl, Ctx.decode]
    simp [Nat.unpair_pair, ih, Ty.decode_code]

/-- The code of a judgment: its scope, its context and its two types. -/
def Judgment.code (j : Judgment) : ℕ :=
  Nat.pair j.n (Nat.pair j.Γ.code (Nat.pair j.S.code j.U.code))

/-- The judgment of scope `n` with code `r`, if any. -/
def Judgment.decodeAt (n r : ℕ) : Option Judgment := do
  let Γ ← Ctx.decode n (Nat.unpair r).1
  let S ← Ty.decode n (Nat.unpair (Nat.unpair r).2).1
  let U ← Ty.decode n (Nat.unpair (Nat.unpair r).2).2
  pure ⟨Γ, S, U⟩

/-- The judgment with a given code, if any. -/
def Judgment.decode (m : ℕ) : Option Judgment :=
  Judgment.decodeAt (Nat.unpair m).1 (Nat.unpair m).2

theorem Judgment.decode_code (j : Judgment) : Judgment.decode j.code = some j := by
  obtain ⟨Γ, S, U⟩ := j
  -- The scope is rewritten first, while no type depends on it.
  rw [Judgment.decode, Judgment.code, Nat.unpair_pair]
  simp [Judgment.decodeAt, Nat.unpair_pair, Ctx.decode_code, Ty.decode_code]

/-- The subtyping problem on codes: the code names a judgment, and that judgment holds. -/
def Subtyping (m : ℕ) : Prop :=
  ∃ j : Judgment, Judgment.decode m = some j ∧ j.Holds

end Dsub
