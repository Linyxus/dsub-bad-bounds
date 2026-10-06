import Resolution.Height
import Resolution.Thin

/-!
Annotations of states and the invariant `I` (PROOF.md §2), and Lemma 2 (backward
preservation).

A state is a judgment `Γ ⊢ S <: U`.  Its two terms are taken to be `S` and `U` themselves:
`Dᵏ(V)`, `{A:P..⊤}` have the occurrences and the `∀`-nesting of `V`, `P`.

An annotation marks the created variables (`cr`) and arranges them in a forest, given by its
strict ancestor relation `anc`, together with a depth labelling `dep` that is strictly
increasing along `anc`.  (PROOF.md takes `dep` to be the depth in the forest; every property
used of it is that it increases along ancestry, and labelling makes re-parenting after a
collapse trivial: restricting the forest keeps the labels.)
-/

namespace Dsub

/-- Contexts extending a base context by appended variables. -/
inductive Ctx.Extends {n₀ : ℕ} (Γ₀ : Ctx n₀) : {n : ℕ} → Ctx n → Prop where
  | refl : Ctx.Extends Γ₀ Γ₀
  | push {n : ℕ} {Γ : Ctx n} (T : Ty n) : Ctx.Extends Γ₀ Γ → Ctx.Extends Γ₀ (Γ.push T)

/-- An annotation: the created variables, a forest on them (by its strict ancestor relation)
and depth labels increasing along the forest. -/
structure Ann (n : ℕ) where
  cr : BVar n → Prop
  anc : BVar n → BVar n → Prop
  dep : BVar n → ℕ
  anc_trans : ∀ {a b c}, anc a b → anc b c → anc a c
  anc_dep : ∀ {a b}, anc a b → dep a < dep b
  anc_chain : ∀ {a b x}, anc a x → anc b x → a = b ∨ anc a b ∨ anc b a
  anc_cr : ∀ {a b}, anc a b → cr a ∧ cr b
  dep_pos : ∀ {x}, cr x → 1 ≤ dep x

/-- `x`, `y` are equal or one is an ancestor of the other. -/
def Ann.Related {n : ℕ} (a : Ann n) (x y : BVar n) : Prop := x = y ∨ a.anc x y ∨ a.anc y x

/-- The annotation of the root state: nothing created. -/
def Ann.root {n : ℕ} : Ann n where
  cr := fun _ => False
  anc := fun _ _ => False
  dep := fun _ => 0
  anc_trans := fun h _ => h.elim
  anc_dep := fun h => h.elim
  anc_chain := fun h _ => h.elim
  anc_cr := fun h => h.elim
  dep_pos := fun h => h.elim

/-- The invariant `I` with bound `N` on the state `Γ ⊢ S <: U`.  `ctx_anc` is (I1) (for a
base variable it says that its type mentions no created variable), `dep_*` is (I2), `shared`
is (I3), `dep_le` is (I4), and `nu_*` bound the `∀`-nesting by `N` (true of all the types of
PROOF.md's states, which lie in `𝒮`). -/
structure Inv {n : ℕ} (N : ℕ) (Γ : Ctx n) (a : Ann n) (S U : Ty n) : Prop where
  nu_left : S.nu ≤ N
  nu_right : U.nu ≤ N
  nu_ctx : ∀ x, (Γ.lookup x).nu ≤ N
  ctx_anc : ∀ x y, (Γ.lookup x).Occ y → a.cr y → a.anc y x
  dep_left : ∀ x, a.cr x → S.Occ x → S.nu + a.dep x ≤ N
  dep_right : ∀ x, a.cr x → U.Occ x → U.nu + a.dep x ≤ N
  dep_ctx : ∀ x y, a.cr x → (Γ.lookup y).Occ x → (Γ.lookup y).nu + a.dep x ≤ N
  shared : ∀ x y, a.cr x → a.cr y → S.Occ x → S.Occ y → U.Occ x → U.Occ y → a.Related x y
  dep_le : ∀ x, a.cr x → a.dep x ≤ N

theorem Inv.root {n N : ℕ} {Γ : Ctx n} {S U : Ty n} (hS : S.nu ≤ N) (hU : U.nu ≤ N)
    (hΓ : ∀ x, (Γ.lookup x).nu ≤ N) : Inv N Γ Ann.root S U where
  nu_left := hS
  nu_right := hU
  nu_ctx := hΓ
  ctx_anc := fun _ _ _ h => h.elim
  dep_left := fun _ h => h.elim
  dep_right := fun _ h => h.elim
  dep_ctx := fun _ _ h => h.elim
  shared := fun _ _ h => h.elim
  dep_le := fun _ h => h.elim

/-! ### Premises that keep the context -/

/-- `T'` has no more variables and no deeper `∀`-nesting than `T`. -/
def Dom {n : ℕ} (T' T : Ty n) : Prop := (∀ x, T'.Occ x → T.Occ x) ∧ T'.nu ≤ T.nu

theorem Dom.refl {n : ℕ} (T : Ty n) : Dom T T := ⟨fun _ h => h, le_rfl⟩
theorem Dom.bnd_left {n : ℕ} (S U : Ty n) : Dom S (.bnd S U) :=
  ⟨fun _ h => Or.inl h, le_max_left _ _⟩
theorem Dom.bnd_right {n : ℕ} (S U : Ty n) : Dom U (.bnd S U) :=
  ⟨fun _ h => Or.inr h, le_max_right _ _⟩
theorem Dom.bnd_top {n : ℕ} (S : Ty n) : Dom (.bnd S .top) S :=
  ⟨fun _ h => by simpa using h, by simp⟩
theorem Dom.bnd_bot {n : ℕ} (U : Ty n) : Dom (.bnd .bot U) U :=
  ⟨fun _ h => by simpa using h, by simp⟩

theorem Inv.symm {n N : ℕ} {Γ : Ctx n} {a : Ann n} {S U : Ty n} (h : Inv N Γ a S U) :
    Inv N Γ a U S where
  nu_left := h.nu_right
  nu_right := h.nu_left
  nu_ctx := h.nu_ctx
  ctx_anc := h.ctx_anc
  dep_left := h.dep_right
  dep_right := h.dep_left
  dep_ctx := h.dep_ctx
  shared := fun x y hx hy h1 h2 h3 h4 => h.shared x y hx hy h3 h4 h1 h2
  dep_le := h.dep_le

theorem Inv.mono {n N : ℕ} {Γ : Ctx n} {a : Ann n} {S U S' U' : Ty n} (h : Inv N Γ a S U)
    (hS : Dom S' S) (hU : Dom U' U) : Inv N Γ a S' U' where
  nu_left := le_trans hS.2 h.nu_left
  nu_right := le_trans hU.2 h.nu_right
  nu_ctx := h.nu_ctx
  ctx_anc := h.ctx_anc
  dep_left := fun x hx ho => le_trans (Nat.add_le_add_right hS.2 _) (h.dep_left x hx (hS.1 x ho))
  dep_right := fun x hx ho => le_trans (Nat.add_le_add_right hU.2 _) (h.dep_right x hx (hU.1 x ho))
  dep_ctx := h.dep_ctx
  shared := fun x y hx hy h1 h2 h3 h4 =>
    h.shared x y hx hy (hS.1 x h1) (hS.1 y h2) (hU.1 x h3) (hU.1 y h4)
  dep_le := h.dep_le

/-- Replacing the left term by a lookup (kind (b) of Lemma 1). -/
theorem Inv.lookup_left {n N : ℕ} {Γ : Ctx n} {a : Ann n} {S U : Ty n} (h : Inv N Γ a S U)
    (x : BVar n) : Inv N Γ a (Γ.lookup x) U where
  nu_left := h.nu_ctx x
  nu_right := h.nu_right
  nu_ctx := h.nu_ctx
  ctx_anc := h.ctx_anc
  dep_left := fun y hy ho => h.dep_ctx y x hy ho
  dep_right := h.dep_right
  dep_ctx := h.dep_ctx
  shared := fun y y' hy hy' h1 h2 _ _ => by
    rcases a.anc_chain (h.ctx_anc x y h1 hy) (h.ctx_anc x y' h2 hy') with e | e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr e)
  dep_le := h.dep_le

/-! ### Lemma 2 for the rules other than `all` (same annotation) -/

theorem Inv.bnd {n N : ℕ} {Γ : Ctx n} {a : Ann n} {S₁ U₁ S₂ U₂ : Ty n}
    (h : Inv N Γ a (.bnd S₁ U₁) (.bnd S₂ U₂)) : Inv N Γ a S₂ S₁ ∧ Inv N Γ a U₁ U₂ :=
  ⟨h.symm.mono (Dom.bnd_left _ _) (Dom.bnd_left _ _),
   h.mono (Dom.bnd_right _ _) (Dom.bnd_right _ _)⟩

theorem Inv.sel_lower {n N : ℕ} {Γ : Ctx n} {a : Ann n} {S : Ty n} {x : BVar n}
    (h : Inv N Γ a S (.sel x)) : Inv N Γ a (Γ.lookup x) (.bnd S .top) :=
  (h.symm.lookup_left x).mono (Dom.refl _) (Dom.bnd_top _)

theorem Inv.sel_upper {n N : ℕ} {Γ : Ctx n} {a : Ann n} {U : Ty n} {x : BVar n}
    (h : Inv N Γ a (.sel x) U) : Inv N Γ a (Γ.lookup x) (.bnd .bot U) :=
  (h.lookup_left x).mono (Dom.refl _) (Dom.bnd_bot _)

theorem Inv.bad_bounds {n N : ℕ} {Γ : Ctx n} {a : Ann n} {S U : Ty n} (h : Inv N Γ a S U)
    (x : BVar n) :
    Inv N Γ a (Γ.lookup x) (.bnd S .top) ∧ Inv N Γ a (Γ.lookup x) (.bnd .bot U) :=
  ⟨(h.symm.lookup_left x).mono (Dom.refl _) (Dom.bnd_top _),
   (h.lookup_left x).mono (Dom.refl _) (Dom.bnd_bot _)⟩

/-! ### Extending an annotation by a new created variable -/

/-- The proper ancestors of the new variable when its parent is `p`: `p` and its ancestors. -/
def Ann.below {n : ℕ} (a : Ann n) : Option (BVar n) → BVar n → Prop
  | none, _ => False
  | some q, x => x = q ∨ a.anc x q

def Ann.pushCr {n : ℕ} (a : Ann n) : BVar (n + 1) → Prop
  | .here => True
  | .there x => a.cr x

def Ann.pushAnc {n : ℕ} (a : Ann n) (p : Option (BVar n)) : BVar (n + 1) → BVar (n + 1) → Prop
  | .here, _ => False
  | .there x, .here => a.below p x
  | .there x, .there y => a.anc x y

def Ann.pushDep {n : ℕ} (a : Ann n) (p : Option (BVar n)) : BVar (n + 1) → ℕ
  | .here => p.elim 0 a.dep + 1
  | .there x => a.dep x

theorem Ann.below_dep {n : ℕ} (a : Ann n) {p : Option (BVar n)} {x : BVar n}
    (h : a.below p x) : a.dep x < p.elim 0 a.dep + 1 := by
  cases p with
  | none => exact h.elim
  | some q =>
    rcases h with rfl | h
    · simp
    · have := a.anc_dep h; simp; omega

/-- The annotation extended by a new created variable (the innermost one) with parent `p`. -/
def Ann.push {n : ℕ} (a : Ann n) (p : Option (BVar n)) (hp : ∀ q, p = some q → a.cr q) :
    Ann (n + 1) where
  cr := a.pushCr
  anc := a.pushAnc p
  dep := a.pushDep p
  anc_trans := by
    intro u v w h1 h2
    cases u with
    | here => exact h1.elim
    | there x =>
      cases v with
      | here => cases w <;> exact h2.elim
      | there y =>
        cases w with
        | here =>
          cases p with
          | none => exact h2.elim
          | some q =>
            simp only [Ann.pushAnc, Ann.below] at h1 h2 ⊢
            rcases h2 with rfl | h2
            · exact Or.inr h1
            · exact Or.inr (a.anc_trans h1 h2)
        | there z => exact a.anc_trans h1 h2
  anc_dep := by
    intro u v h
    cases u with
    | here => exact h.elim
    | there x =>
      cases v with
      | here => exact a.below_dep h
      | there y => exact a.anc_dep h
  anc_chain := by
    intro u v w h1 h2
    cases u with
    | here => exact h1.elim
    | there x =>
      cases v with
      | here => exact h2.elim
      | there y =>
        cases w with
        | here =>
          cases p with
          | none => exact h1.elim
          | some q =>
            simp only [Ann.pushAnc, Ann.below] at h1 h2
            rcases h1 with rfl | h1 <;> rcases h2 with rfl | h2
            · exact Or.inl rfl
            · exact Or.inr (Or.inr h2)
            · exact Or.inr (Or.inl h1)
            · rcases a.anc_chain h1 h2 with e | e | e
              · exact Or.inl (congrArg _ e)
              · exact Or.inr (Or.inl e)
              · exact Or.inr (Or.inr e)
        | there z =>
          rcases a.anc_chain h1 h2 with e | e | e
          · exact Or.inl (congrArg _ e)
          · exact Or.inr (Or.inl e)
          · exact Or.inr (Or.inr e)
  anc_cr := by
    intro u v h
    cases u with
    | here => exact h.elim
    | there x =>
      cases v with
      | here =>
        refine ⟨?_, trivial⟩
        cases p with
        | none => exact h.elim
        | some q =>
          rcases h with rfl | h
          · exact hp _ rfl
          · exact (a.anc_cr h).1
      | there y => exact a.anc_cr h
  dep_pos := by
    intro x hx
    cases x with
    | here => simp [Ann.pushDep]
    | there x => exact a.dep_pos hx

/-! ### The parent of the new variable: the deepest created variable in both terms -/

theorem Ann.exists_deepest {n : ℕ} (a : Ann n) (C : BVar n → Prop) (h : ∃ x, C x) :
    ∃ p, C p ∧ ∀ x, C x → a.dep x ≤ a.dep p := by
  classical
  obtain ⟨x, hx⟩ := h
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image (Finset.univ.filter C) a.dep
    ⟨x, by simp [hx]⟩
  exact ⟨p, by simpa using hp, fun y hy => hmax y (by simp [hy])⟩

/-- A deepest variable satisfying `C`, if any. -/
noncomputable def Ann.deepest {n : ℕ} (a : Ann n) (C : BVar n → Prop) : Option (BVar n) := by
  classical
  exact if h : ∃ x, C x then some (Classical.choose (a.exists_deepest C h)) else none

theorem Ann.deepest_spec {n : ℕ} (a : Ann n) (C : BVar n → Prop) :
    (a.deepest C = none ∧ ∀ x, ¬ C x) ∨
    (∃ q, a.deepest C = some q ∧ C q ∧ ∀ x, C x → a.dep x ≤ a.dep q) := by
  classical
  by_cases h : ∃ x, C x
  · right
    refine ⟨Classical.choose (a.exists_deepest C h), ?_, Classical.choose_spec (a.exists_deepest C h)⟩
    simp [Ann.deepest, h]
  · left
    refine ⟨by simp [Ann.deepest, h], fun x hx => h ⟨x, hx⟩⟩

/-- The created variables occurring in both terms. -/
def Ann.sharedSet {n : ℕ} (a : Ann n) (S U : Ty n) (x : BVar n) : Prop :=
  a.cr x ∧ S.Occ x ∧ U.Occ x

/-- The parent given to the variable created by entering `S <: U` (both `∀`s). -/
noncomputable def Ann.parent {n : ℕ} (a : Ann n) (S U : Ty n) : Option (BVar n) :=
  a.deepest (a.sharedSet S U)

theorem Ann.parent_cr {n : ℕ} (a : Ann n) (S U : Ty n) :
    ∀ q, a.parent S U = some q → a.cr q := by
  intro q hq
  rcases a.deepest_spec (a.sharedSet S U) with ⟨h, _⟩ | ⟨q', h, hC, _⟩
  · simp [Ann.parent, h] at hq
  · rw [Ann.parent, h] at hq; cases hq; exact hC.1

/-- Under (I3), the shared created variables are the parent and its ancestors. -/
theorem Inv.below_parent {n N : ℕ} {Γ : Ctx n} {a : Ann n} {S U : Ty n} (h : Inv N Γ a S U)
    {x : BVar n} (hx : a.sharedSet S U x) : a.below (a.parent S U) x := by
  rcases a.deepest_spec (a.sharedSet S U) with ⟨_, hn⟩ | ⟨q, hq, hC, hmax⟩
  · exact (hn x hx).elim
  · rw [Ann.parent, hq]
    rcases h.shared x q hx.1 hC.1 hx.2.1 hC.2.1 hx.2.2 hC.2.2 with e | e | e
    · exact Or.inl e
    · exact Or.inr e
    · exact absurd (hmax x hx) (by have := a.anc_dep e; omega)

/-- The parent, if any, occurs in both terms. -/
theorem Ann.parent_shared {n : ℕ} (a : Ann n) (S U : Ty n) :
    ∀ q, a.parent S U = some q → a.sharedSet S U q := by
  intro q hq
  rcases a.deepest_spec (a.sharedSet S U) with ⟨h, _⟩ | ⟨q', h, hC, _⟩
  · simp [Ann.parent, h] at hq
  · rw [Ann.parent, h] at hq; cases hq; exact hC

/-- The annotation of the premise of the `all` rule. -/
noncomputable def Ann.enter {n : ℕ} (a : Ann n) (S U : Ty n) : Ann (n + 1) :=
  a.push (a.parent S U) (a.parent_cr S U)

/-! ### Lemma 2 for the `all` rule -/

theorem Inv.all {n N : ℕ} {Γ : Ctx n} {a : Ann n} {S : Ty n} {B B' : Ty (n + 1)}
    (h : Inv N Γ a (.all S B) (.all S B')) :
    Inv N (Γ.push S) (a.enter (.all S B) (.all S B')) B B' := by
  set p := a.parent (.all S B) (.all S B') with hpdef
  have hl := h.nu_left
  have hr := h.nu_right
  simp only [Ty.nu_all] at hl hr
  constructor
  · omega
  · omega
  · intro x
    cases x with
    | here => simp only [Ctx.lookup_here, Ty.nu_weaken]; omega
    | there x => simp only [Ctx.lookup_there, Ty.nu_weaken]; exact h.nu_ctx x
  · intro x y ho hy
    cases x with
    | here =>
      simp only [Ctx.lookup_here] at ho
      obtain ⟨y', rfl, ho'⟩ := Ty.occ_weaken.1 ho
      exact h.below_parent ⟨hy, Or.inl ho', Or.inl ho'⟩
    | there x =>
      simp only [Ctx.lookup_there] at ho
      obtain ⟨y', rfl, ho'⟩ := Ty.occ_weaken.1 ho
      exact h.ctx_anc x y' ho' hy
  · intro x hx ho
    cases x with
    | here =>
      show B.nu + p.elim 0 a.dep + 1 ≤ N
      cases hp : p with
      | none => simp; omega
      | some q =>
        have := h.dep_left q (a.parent_shared _ _ q hp).1 (a.parent_shared _ _ q hp).2.1
        simp only [Ty.nu_all] at this
        simp; omega
    | there x =>
      have := h.dep_left x hx (Or.inr ho)
      simp only [Ty.nu_all] at this
      show B.nu + a.dep x ≤ N
      omega
  · intro x hx ho
    cases x with
    | here =>
      show B'.nu + p.elim 0 a.dep + 1 ≤ N
      cases hp : p with
      | none => simp; omega
      | some q =>
        have := h.dep_right q (a.parent_shared _ _ q hp).1 (a.parent_shared _ _ q hp).2.2
        simp only [Ty.nu_all] at this
        simp; omega
    | there x =>
      have := h.dep_right x hx (Or.inr ho)
      simp only [Ty.nu_all] at this
      show B'.nu + a.dep x ≤ N
      omega
  · intro x y hx ho
    cases y with
    | here =>
      simp only [Ctx.lookup_here] at ho
      obtain ⟨x', rfl, ho'⟩ := Ty.occ_weaken.1 ho
      have := h.dep_left x' hx (Or.inl ho')
      simp only [Ty.nu_all] at this
      simp only [Ctx.lookup_here, Ty.nu_weaken]
      show S.nu + a.dep x' ≤ N
      omega
    | there y =>
      simp only [Ctx.lookup_there] at ho
      obtain ⟨x', rfl, ho'⟩ := Ty.occ_weaken.1 ho
      simp only [Ctx.lookup_there, Ty.nu_weaken]
      exact h.dep_ctx x' y hx ho'
  · intro x y hx hy h1 h2 h3 h4
    cases x with
    | here =>
      cases y with
      | here => exact Or.inl rfl
      | there y => exact Or.inr (Or.inr (h.below_parent ⟨hy, Or.inr h2, Or.inr h4⟩))
    | there x =>
      cases y with
      | here => exact Or.inr (Or.inl (h.below_parent ⟨hx, Or.inr h1, Or.inr h3⟩))
      | there y =>
        rcases h.shared x y hx hy (Or.inr h1) (Or.inr h2) (Or.inr h3) (Or.inr h4) with e | e | e
        · exact Or.inl (congrArg _ e)
        · exact Or.inr (Or.inl e)
        · exact Or.inr (Or.inr e)
  · intro x hx
    cases x with
    | here =>
      show p.elim 0 a.dep + 1 ≤ N
      cases hp : p with
      | none => simp; omega
      | some q =>
        have := h.dep_left q (a.parent_shared _ _ q hp).1 (a.parent_shared _ _ q hp).2.1
        simp only [Ty.nu_all] at this
        simp; omega
    | there x => exact h.dep_le x hx

end Dsub
