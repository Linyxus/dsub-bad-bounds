import Resolution.Rules

/-!
Occurrences, `∀`-nesting, and removing variables from a context.

A thinning `θ : Thin m n` is an order-preserving embedding of `m` variables into `n`: the
variables of scope `n` it misses are the removed ones.  `Ty.unthin` strengthens a type
along `θ` (it fails if the type mentions a removed variable), and `Ctx.restrict` removes
the missed variables from a context (it fails if a kept variable's type mentions a removed
one).
-/

namespace Dsub

instance {n : ℕ} : Fintype (BVar n) := Fintype.ofList (BVar.list n) BVar.mem_list

/-! ### Occurrences and `∀`-nesting -/

/-- `T.Occ x`: the variable `x` occurs in `T`. -/
def Ty.Occ : {n : ℕ} → Ty n → BVar n → Prop
  | _, .top, _ => False
  | _, .bot, _ => False
  | _, .sel y, x => x = y
  | _, .bnd S U, x => S.Occ x ∨ U.Occ x
  | _, .all S T, x => S.Occ x ∨ T.Occ (.there x)

/-- The `∀`-nesting depth. -/
def Ty.nu : {n : ℕ} → Ty n → ℕ
  | _, .top => 0
  | _, .bot => 0
  | _, .sel _ => 0
  | _, .bnd S U => max S.nu U.nu
  | _, .all S T => max S.nu (T.nu + 1)

@[simp] theorem Ty.occ_top {n : ℕ} {x : BVar n} : ¬ (Ty.top).Occ x := id
@[simp] theorem Ty.occ_bot {n : ℕ} {x : BVar n} : ¬ (Ty.bot).Occ x := id
@[simp] theorem Ty.occ_sel {n : ℕ} {x y : BVar n} : (Ty.sel y).Occ x ↔ x = y := Iff.rfl
@[simp] theorem Ty.occ_bnd {n : ℕ} {x : BVar n} {S U : Ty n} :
    (Ty.bnd S U).Occ x ↔ S.Occ x ∨ U.Occ x := Iff.rfl
@[simp] theorem Ty.occ_all {n : ℕ} {x : BVar n} {S : Ty n} {T : Ty (n + 1)} :
    (Ty.all S T).Occ x ↔ S.Occ x ∨ T.Occ (.there x) := Iff.rfl

@[simp] theorem Ty.nu_top {n : ℕ} : (Ty.top (n := n)).nu = 0 := rfl
@[simp] theorem Ty.nu_bot {n : ℕ} : (Ty.bot (n := n)).nu = 0 := rfl
@[simp] theorem Ty.nu_sel {n : ℕ} {x : BVar n} : (Ty.sel x).nu = 0 := rfl
@[simp] theorem Ty.nu_bnd {n : ℕ} {S U : Ty n} : (Ty.bnd S U).nu = max S.nu U.nu := rfl
@[simp] theorem Ty.nu_all {n : ℕ} {S : Ty n} {T : Ty (n + 1)} :
    (Ty.all S T).nu = max S.nu (T.nu + 1) := rfl

theorem Ty.occ_rename {n m : ℕ} {T : Ty n} {f : Rename n m} {y : BVar m} :
    (T.rename f).Occ y ↔ ∃ x, f.var x = y ∧ T.Occ x := by
  induction T generalizing m y with
  | top => simp
  | bot => simp
  | sel x => simp [eq_comm]
  | bnd S U ihS ihU =>
    simp only [Ty.rename_bnd, Ty.occ_bnd, ihS, ihU]
    constructor
    · rintro (⟨x, rfl, h⟩ | ⟨x, rfl, h⟩)
      · exact ⟨x, rfl, Or.inl h⟩
      · exact ⟨x, rfl, Or.inr h⟩
    · rintro ⟨x, rfl, h | h⟩
      · exact Or.inl ⟨x, rfl, h⟩
      · exact Or.inr ⟨x, rfl, h⟩
  | all S T ihS ihT =>
    simp only [Ty.rename_all, Ty.occ_all, ihS, ihT]
    constructor
    · rintro (⟨x, rfl, h⟩ | ⟨x, hx, h⟩)
      · exact ⟨x, rfl, Or.inl h⟩
      · cases x with
        | here => simp at hx
        | there x =>
          simp only [Rename.lift_there, BVar.there.injEq] at hx
          exact ⟨x, hx, Or.inr h⟩
    · rintro ⟨x, rfl, h | h⟩
      · exact Or.inl ⟨x, rfl, h⟩
      · exact Or.inr ⟨.there x, rfl, h⟩

theorem Ty.occ_weaken {n : ℕ} {T : Ty n} {y : BVar (n + 1)} :
    T.weaken.Occ y ↔ ∃ x, y = .there x ∧ T.Occ x := by
  rw [Ty.weaken, Ty.occ_rename]
  simp only [Rename.succ_var]
  exact ⟨fun ⟨x, h1, h2⟩ => ⟨x, h1.symm, h2⟩, fun ⟨x, h1, h2⟩ => ⟨x, h1.symm, h2⟩⟩

@[simp] theorem Ty.occ_there_weaken {n : ℕ} {T : Ty n} {x : BVar n} :
    T.weaken.Occ (.there x) ↔ T.Occ x := by
  rw [Ty.occ_weaken]
  constructor
  · rintro ⟨y, h, hy⟩; cases h; exact hy
  · intro h; exact ⟨x, rfl, h⟩

theorem Ty.nu_rename {n m : ℕ} {T : Ty n} {f : Rename n m} : (T.rename f).nu = T.nu := by
  induction T generalizing m with
  | top => rfl
  | bot => rfl
  | sel x => rfl
  | bnd S U ihS ihU => simp only [Ty.rename_bnd, Ty.nu_bnd, ihS, ihU]
  | all S T ihS ihT => simp only [Ty.rename_all, Ty.nu_all, ihS, ihT]

@[simp] theorem Ty.nu_weaken {n : ℕ} {T : Ty n} : T.weaken.nu = T.nu := Ty.nu_rename

/-- Renamings that agree on the variables of `T` agree on `T`. -/
theorem Ty.rename_congr {n m : ℕ} {T : Ty n} {f g : Rename n m}
    (h : ∀ x, T.Occ x → f.var x = g.var x) : T.rename f = T.rename g := by
  induction T generalizing m with
  | top => rfl
  | bot => rfl
  | sel x => simp only [Ty.rename_sel, h x rfl]
  | bnd S U ihS ihU =>
    simp only [Ty.rename_bnd, ihS (fun x hx => h x (Or.inl hx)),
      ihU (fun x hx => h x (Or.inr hx))]
  | all S T ihS ihT =>
    simp only [Ty.rename_all, ihS (fun x hx => h x (Or.inl hx))]
    congr 1
    apply ihT
    intro x hx
    cases x with
    | here => rfl
    | there x => simp only [Rename.lift_there, h x (Or.inr hx)]

/-- Renaming along an injective renaming is injective. -/
theorem Ty.rename_inj {n m : ℕ} {f : Rename n m} (hf : Function.Injective f.var) :
    ∀ {S T : Ty n}, S.rename f = T.rename f → S = T := by
  intro S
  induction S generalizing m with
  | top => intro T h; cases T <;> simp_all
  | bot => intro T h; cases T <;> simp_all
  | sel x => intro T h; cases T <;> simp_all [hf.eq_iff]
  | bnd S U ihS ihU =>
    intro T h
    cases T <;> simp only [Ty.rename_bnd, Ty.rename_top, Ty.rename_bot, Ty.rename_sel,
      Ty.rename_all, reduceCtorEq, Ty.bnd.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rw [ihS hf h1, ihU hf h2]
  | all S B ihS ihB =>
    intro T h
    cases T <;> simp only [Ty.rename_bnd, Ty.rename_top, Ty.rename_bot, Ty.rename_sel,
      Ty.rename_all, reduceCtorEq, Ty.all.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have hl : Function.Injective f.lift.var := by
      intro a b e
      cases a <;> cases b <;> simp_all [hf.eq_iff]
    rw [ihS hf h1, ihB hl h2]

/-! ### Thinnings -/

/-- Order-preserving embeddings of `m` variables into `n`. -/
inductive Thin : ℕ → ℕ → Type where
  | done : Thin 0 0
  | keep {m n : ℕ} : Thin m n → Thin (m + 1) (n + 1)
  | drop {m n : ℕ} : Thin m n → Thin m (n + 1)

/-- Where a kept variable goes. -/
def Thin.var : {m n : ℕ} → Thin m n → BVar m → BVar n
  | _, _, .keep _, .here => .here
  | _, _, .keep θ, .there y => .there (θ.var y)
  | _, _, .drop θ, y => .there (θ.var y)

/-- The preimage of a variable, if it is kept. -/
def Thin.unvar : {m n : ℕ} → Thin m n → BVar n → Option (BVar m)
  | _, _, .keep _, .here => some .here
  | _, _, .keep θ, .there x => (θ.unvar x).map .there
  | _, _, .drop _, .here => none
  | _, _, .drop θ, .there x => θ.unvar x

/-- A thinning as a renaming. -/
def Thin.ren {m n : ℕ} (θ : Thin m n) : Rename m n := ⟨θ.var⟩

@[simp] theorem Thin.ren_var {m n : ℕ} {θ : Thin m n} {y : BVar m} : θ.ren.var y = θ.var y := rfl

theorem Thin.unvar_var {m n : ℕ} : ∀ (θ : Thin m n) (y : BVar m), θ.unvar (θ.var y) = some y
  | .keep _, .here => rfl
  | .keep θ, .there y => by simp [Thin.var, Thin.unvar, Thin.unvar_var θ y]
  | .drop θ, y => by simp [Thin.var, Thin.unvar, Thin.unvar_var θ y]

theorem Thin.var_of_unvar {m n : ℕ} :
    ∀ (θ : Thin m n) (x : BVar n) (y : BVar m), θ.unvar x = some y → θ.var y = x
  | .keep _, .here, y, h => by simp only [Thin.unvar, Option.some.injEq] at h; subst h; rfl
  | .keep θ, .there x, y, h => by
    simp only [Thin.unvar, Option.map_eq_some_iff] at h
    obtain ⟨y', h, rfl⟩ := h
    simp [Thin.var, Thin.var_of_unvar θ x y' h]
  | .drop _, .here, y, h => by simp [Thin.unvar] at h
  | .drop θ, .there x, y, h => by
    simp only [Thin.unvar] at h
    simp [Thin.var, Thin.var_of_unvar θ x y h]

theorem Thin.var_injective {m n : ℕ} (θ : Thin m n) : Function.Injective θ.var := by
  intro a b h
  have := congrArg θ.unvar h
  rw [Thin.unvar_var, Thin.unvar_var] at this
  exact Option.some.inj this

theorem Thin.mem_range_iff {m n : ℕ} (θ : Thin m n) (x : BVar n) :
    (∃ y, θ.var y = x) ↔ ∃ y, θ.unvar x = some y :=
  ⟨fun ⟨y, h⟩ => ⟨y, h ▸ Thin.unvar_var θ y⟩, fun ⟨y, h⟩ => ⟨y, Thin.var_of_unvar θ x y h⟩⟩

theorem Thin.keep_ren {m n : ℕ} (θ : Thin m n) : θ.keep.ren = θ.ren.lift := by
  apply Rename.ext; intro x; cases x <;> rfl

theorem Thin.drop_ren {m n : ℕ} (θ : Thin m n) : θ.drop.ren = θ.ren.comp Rename.succ := by
  apply Rename.ext; intro x; rfl

/-- Strengthens a type along a thinning, if it mentions only kept variables. -/
def Ty.unthin : {m n : ℕ} → Ty n → Thin m n → Option (Ty m)
  | _, _, .top, _ => some .top
  | _, _, .bot, _ => some .bot
  | _, _, .sel x, θ => (θ.unvar x).map .sel
  | _, _, .bnd S U, θ => do
    let S' ← S.unthin θ
    let U' ← U.unthin θ
    pure (.bnd S' U')
  | _, _, .all S T, θ => do
    let S' ← S.unthin θ
    let T' ← T.unthin θ.keep
    pure (.all S' T')

theorem Ty.unthin_rename {m n : ℕ} {θ : Thin m n} {T : Ty n} {T' : Ty m}
    (h : T.unthin θ = some T') : T'.rename θ.ren = T := by
  induction T generalizing m T' with
  | top => simp only [Ty.unthin, Option.some.injEq] at h; subst h; rfl
  | bot => simp only [Ty.unthin, Option.some.injEq] at h; subst h; rfl
  | sel x =>
    simp only [Ty.unthin, Option.map_eq_some_iff] at h
    obtain ⟨y, hy, rfl⟩ := h
    simp [Thin.var_of_unvar θ x y hy]
  | bnd S U ihS ihU =>
    simp only [Ty.unthin, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨S', hS, U', hU, rfl⟩ := h
    simp [ihS hS, ihU hU]
  | all S T ihS ihT =>
    simp only [Ty.unthin, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨S', hS, T'', hT, rfl⟩ := h
    simp [ihS hS, ← Thin.keep_ren, ihT hT]

theorem Ty.unthin_of_occ {m n : ℕ} {θ : Thin m n} {T : Ty n}
    (h : ∀ x, T.Occ x → ∃ y, θ.var y = x) : ∃ T', T.unthin θ = some T' := by
  induction T generalizing m with
  | top => exact ⟨_, rfl⟩
  | bot => exact ⟨_, rfl⟩
  | sel x =>
    obtain ⟨y, hy⟩ := (Thin.mem_range_iff θ x).1 (h x rfl)
    exact ⟨.sel y, by simp [Ty.unthin, hy]⟩
  | bnd S U ihS ihU =>
    obtain ⟨S', hS⟩ := ihS (fun x hx => h x (Or.inl hx))
    obtain ⟨U', hU⟩ := ihU (fun x hx => h x (Or.inr hx))
    exact ⟨.bnd S' U', by simp [Ty.unthin, hS, hU]⟩
  | all S T ihS ihT =>
    obtain ⟨S', hS⟩ := ihS (fun x hx => h x (Or.inl hx))
    have : ∀ x, T.Occ x → ∃ y, θ.keep.var y = x := by
      intro x hx
      cases x with
      | here => exact ⟨.here, rfl⟩
      | there x =>
        obtain ⟨y, hy⟩ := h x (Or.inr hx)
        exact ⟨.there y, by simp [Thin.var, hy]⟩
    obtain ⟨T', hT⟩ := ihT this
    exact ⟨.all S' T', by simp [Ty.unthin, hS, hT]⟩

/-- Removes the variables a thinning misses from a context, if no kept variable's type
mentions a removed one. -/
def Ctx.restrict : {m n : ℕ} → Ctx n → Thin m n → Option (Ctx m)
  | _, _, .empty, .done => some .empty
  | _, _, .push Γ T, .keep θ => do
    let Δ ← Γ.restrict θ
    let T' ← T.unthin θ
    pure (.push Δ T')
  | _, _, .push Γ _, .drop θ => Γ.restrict θ

/-- The inclusion of a restricted context is a context morphism. -/
theorem Ctx.restrict_morph {m n : ℕ} {Γ : Ctx n} {θ : Thin m n} {Δ : Ctx m}
    (h : Γ.restrict θ = some Δ) : θ.ren.IsCtxMorph Δ Γ := by
  induction Γ generalizing m with
  | empty =>
    cases θ
    intro y; nomatch y
  | push Γ T ih =>
    cases θ with
    | keep θ =>
      simp only [Ctx.restrict, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨Δ', hΔ, T', hT, rfl⟩ := h
      intro y
      cases y with
      | here =>
        simp only [Thin.ren_var, Thin.var, Ctx.lookup_here]
        rw [Thin.keep_ren, Ty.weaken_rename_comm, Ty.unthin_rename hT]
      | there y =>
        simp only [Thin.ren_var, Thin.var, Ctx.lookup_there]
        rw [Thin.keep_ren, Ty.weaken_rename_comm, ← ih hΔ y]
        rfl
    | drop θ =>
      simp only [Ctx.restrict] at h
      intro y
      simp only [Thin.ren_var, Thin.var, Ctx.lookup_there]
      rw [Thin.drop_ren, ← Ty.rename_comp, ← ih h y]
      rfl

/-- A context can be restricted when no kept variable's type mentions a removed one. -/
theorem Ctx.restrict_of_occ {m n : ℕ} {Γ : Ctx n} {θ : Thin m n}
    (h : ∀ y x, (Γ.lookup (θ.var y)).Occ x → ∃ y', θ.var y' = x) :
    ∃ Δ, Γ.restrict θ = some Δ := by
  induction Γ generalizing m with
  | empty => cases θ; exact ⟨_, rfl⟩
  | push Γ T ih =>
    cases θ with
    | keep θ =>
      obtain ⟨Δ, hΔ⟩ := ih (θ := θ) (by
        intro y x hx
        obtain ⟨y', hy'⟩ := h (.there y) (.there x) (by simpa [Thin.var] using hx)
        cases y' with
        | here => simp [Thin.var] at hy'
        | there y' => exact ⟨y', by simpa [Thin.var] using hy'⟩)
      obtain ⟨T', hT⟩ := Ty.unthin_of_occ (θ := θ) (T := T) (by
        intro x hx
        obtain ⟨y', hy'⟩ := h .here (.there x) (by simpa [Thin.var] using hx)
        cases y' with
        | here => simp [Thin.var] at hy'
        | there y' => exact ⟨y', by simpa [Thin.var] using hy'⟩)
      exact ⟨Δ.push T', by simp [Ctx.restrict, hΔ, hT]⟩
    | drop θ =>
      simp only [Ctx.restrict]
      apply ih
      intro y x hx
      obtain ⟨y', hy'⟩ := h y (.there x) (by simpa [Thin.var] using hx)
      exact ⟨y', by simpa [Thin.var] using hy'⟩

/-- The thinning that keeps exactly the variables satisfying `keep`. -/
def Thin.ofPred : (n : ℕ) → (BVar n → Bool) → (m : ℕ) × Thin m n
  | 0, _ => ⟨0, .done⟩
  | n + 1, k =>
    let r := Thin.ofPred n (fun x => k (.there x))
    if k .here then ⟨r.1 + 1, .keep r.2⟩ else ⟨r.1, .drop r.2⟩

theorem Thin.ofPred_keep {n : ℕ} {k : BVar (n + 1) → Bool} (hk : k .here = true) :
    Thin.ofPred (n + 1) k =
      ⟨(Thin.ofPred n (fun x => k (.there x))).1 + 1, .keep (Thin.ofPred n (fun x => k (.there x))).2⟩ := by
  simp [Thin.ofPred, hk]

theorem Thin.ofPred_drop {n : ℕ} {k : BVar (n + 1) → Bool} (hk : k .here = false) :
    Thin.ofPred (n + 1) k =
      ⟨(Thin.ofPred n (fun x => k (.there x))).1, .drop (Thin.ofPred n (fun x => k (.there x))).2⟩ := by
  simp [Thin.ofPred, hk]

theorem Thin.ofPred_range : ∀ (n : ℕ) (k : BVar n → Bool) (x : BVar n),
    (∃ y, (Thin.ofPred n k).2.var y = x) ↔ k x = true
  | 0, _, x => nomatch x
  | n + 1, k, x => by
    have ih := Thin.ofPred_range n (fun x => k (.there x))
    cases hk : k .here with
    | true =>
      rw [Thin.ofPred_keep hk]
      cases x with
      | here =>
        simp only [hk, iff_true]
        exact ⟨.here, rfl⟩
      | there x =>
        rw [← ih x]
        constructor
        · rintro ⟨y, hy⟩
          cases y with
          | here => simp [Thin.var] at hy
          | there y => exact ⟨y, by simpa [Thin.var] using hy⟩
        · rintro ⟨y, hy⟩
          exact ⟨.there y, by simp [Thin.var, hy]⟩
    | false =>
      rw [Thin.ofPred_drop hk]
      cases x with
      | here =>
        simp only [hk, Bool.false_eq_true, iff_false]
        rintro ⟨y, hy⟩
        simp [Thin.var] at hy
      | there x =>
        rw [← ih x]
        constructor
        · rintro ⟨y, hy⟩
          exact ⟨y, by simpa [Thin.var] using hy⟩
        · rintro ⟨y, hy⟩
          exact ⟨y, by simp [Thin.var, hy]⟩

end Dsub
