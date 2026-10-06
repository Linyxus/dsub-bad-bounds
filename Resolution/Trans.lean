import Resolution.Lemmas

/-!
Transitivity is admissible.

The proof is by induction on the middle type `T`.  For a fixed `T`, the cuts that the rules
`sel_upper`, `sel_lower` and `bad_bounds` push into the bounds of a declaration are cuts on
`T` inside nested declarations: `P <: dN k T` against `T <: U` (`trans_left`), and
`A <: dN k {T..⊤}` against `P <: T` (`trans_right`).  Each is by induction on the derivation
holding the declaration, and the second calls the first; no narrowing is needed since the
kernel rule for `∀` keeps the parameter type.
-/

namespace Dsub

/-- `Γ ⊢ P <: T` by a rule that fixes the shape of `T`: top, bnd, all or sel_lower. -/
def ShapeSub {n : ℕ} (Γ : Ctx n) (P T : Ty n) : Prop :=
  T = .top ∨
  (∃ S₁ U₁ S₂ U₂, P = .bnd S₁ U₁ ∧ T = .bnd S₂ U₂ ∧ Sub Γ S₂ S₁ ∧ Sub Γ U₁ U₂) ∨
  (∃ S T₀ T₁, P = .all S T₀ ∧ T = .all S T₁ ∧ Sub (Γ.push S) T₀ T₁) ∨
  (∃ x, T = .sel x ∧ Sub Γ (Γ.lookup x) (.bnd P .top))

/-- Cutting `P <: dN k T` against `T <: U`, given the cuts of `T <: U` against the
derivations of `P' <: T` that end in a shape-fixing rule. -/
theorem trans_left {n : ℕ} {Γ : Ctx n} {P Q : Ty n} (D : Sub Γ P Q) :
    ∀ T U : Ty n, (∀ P', ShapeSub Γ P' T → Sub Γ P' U) → Sub Γ T U →
      (Q = T → Sub Γ P U) ∧ (∀ k, Q = Ty.dN (k + 1) T → Sub Γ P (Ty.dN (k + 1) U)) := by
  induction D with
  | top P =>
    intro T U base _
    refine ⟨fun h => base P (Or.inl h.symm), fun k h => ?_⟩
    simp at h
  | bot P => exact fun _ _ _ _ => ⟨fun _ => .bot _, fun _ _ => .bot _⟩
  | refl_sel x =>
    intro T U _ E
    refine ⟨fun h => ?_, fun k h => ?_⟩
    · subst h; exact E
    · simp at h
  | bnd hS hU _ ihU =>
    intro T U base E
    refine ⟨fun h => ?_, fun k h => ?_⟩
    · subst h; exact base _ (Or.inr (Or.inl ⟨_, _, _, _, rfl, rfl, hS, hU⟩))
    · simp only [Ty.dN_succ, Ty.bnd.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      cases k with
      | zero => exact .bnd (.bot _) ((ihU T U base E).1 rfl)
      | succ k => exact .bnd (.bot _) ((ihU T U base E).2 k rfl)
  | all h _ =>
    intro T U base _
    refine ⟨fun e => ?_, fun k e => ?_⟩
    · subst e; exact base _ (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl, rfl, h⟩)))
    · simp at e
  | sel_lower x h _ =>
    intro T U base _
    refine ⟨fun e => ?_, fun k e => ?_⟩
    · subst e; exact base _ (Or.inr (Or.inr (Or.inr ⟨x, rfl, h⟩)))
    · simp at e
  | sel_upper x _ ih =>
    intro T U base E
    refine ⟨fun e => ?_, fun k e => ?_⟩
    · subst e; exact .sel_upper x ((ih _ U base E).2 0 rfl)
    · subst e; exact .sel_upper x ((ih T U base E).2 (k + 1) rfl)
  | bad_bounds x h1 _ _ ih2 =>
    intro T U base E
    refine ⟨fun e => ?_, fun k e => ?_⟩
    · subst e; exact .bad_bounds x h1 ((ih2 _ U base E).2 0 rfl)
    · subst e; exact .bad_bounds x h1 ((ih2 T U base E).2 (k + 1) rfl)

/-- Transitivity through a given middle type. -/
def TransAt {n : ℕ} (T : Ty n) : Prop :=
  ∀ (Γ : Ctx n) (P U : Ty n), Sub Γ P T → Sub Γ T U → Sub Γ P U

/-- Transitivity through the immediate parts of `T`. -/
def TransBelow {n : ℕ} (T : Ty n) : Prop :=
  (∀ S U, T = .bnd S U → TransAt S ∧ TransAt U) ∧
  (∀ S (T₁ : Ty (n + 1)), T = .all S T₁ → TransAt T₁)

/-- Induction on the right derivation: cutting `A <: dN k {T..⊤}` against `P <: T`, and
`T <: B` against `P <: T`. -/
theorem trans_right {n : ℕ} {Γ : Ctx n} {A B : Ty n} (E : Sub Γ A B) :
    ∀ T : Ty n, TransBelow T →
      (∀ k P, B = Ty.dN k (.bnd T .top) → Sub Γ P T → Sub Γ A (Ty.dN k (.bnd P .top))) ∧
      (A = T → ∀ P, Sub Γ P T → Sub Γ P B) := by
  induction E with
  | top A =>
    intro T _
    refine ⟨fun k P h _ => ?_, fun _ P _ => .top _⟩
    cases k <;> simp at h
  | bot B =>
    intro T _
    refine ⟨fun _ _ _ _ => .bot _, fun e P D => ?_⟩
    subst e
    refine (trans_left D .bot B ?_ (.bot B)).1 rfl
    rintro P' (h | ⟨_, _, _, _, _, h, _⟩ | ⟨_, _, _, _, h, _⟩ | ⟨_, h, _⟩) <;> simp at h
  | refl_sel x =>
    intro T _
    refine ⟨fun k P h _ => ?_, fun e P D => ?_⟩
    · cases k <;> simp at h
    · subst e; exact D
  | @bnd _ _ S₁ U₁ S₂ U₂ hS hU ihS ihU =>
    intro T hT
    refine ⟨fun k P h D => ?_, fun e P D => ?_⟩
    · cases k with
      | zero =>
        simp only [Ty.dN_zero, Ty.bnd.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .bnd ((ihS S₂ hT).2 rfl P D) (.top _)
      | succ k =>
        simp only [Ty.dN_succ, Ty.bnd.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .bnd (.bot _) ((ihU T hT).1 k P rfl D)
    · subst e
      obtain ⟨tS, tU⟩ := hT.1 S₁ U₁ rfl
      refine (trans_left D _ _ ?_ (.bnd hS hU)).1 rfl
      rintro P' (h | ⟨_, _, _, _, rfl, h, h1, h2⟩ | ⟨_, _, _, _, h, _⟩ | ⟨_, h, _⟩)
      · simp at h
      · simp only [Ty.bnd.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .bnd (tS _ _ _ hS h1) (tU _ _ _ h2 hU)
      · simp at h
      · simp at h
  | @all _ _ S U₁ U₂ h _ =>
    intro T hT
    refine ⟨fun k P e _ => ?_, fun e P D => ?_⟩
    · cases k <;> simp at e
    · subst e
      have t := hT.2 S U₁ rfl
      refine (trans_left D _ _ ?_ (.all h)).1 rfl
      rintro P' (e | ⟨_, _, _, _, _, e, _⟩ | ⟨_, _, _, rfl, e, h1⟩ | ⟨_, e, _⟩)
      · simp at e
      · simp at e
      · simp only [Ty.all.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        exact .all (t _ _ _ h1 h)
      · simp at e
  | sel_lower x _ ih =>
    intro T hT
    refine ⟨fun k P e _ => ?_, fun e P D => ?_⟩
    · cases k <;> simp at e
    · subst e; exact .sel_lower x ((ih _ hT).1 0 P rfl D)
  | @sel_upper _ _ U x h ih =>
    intro T hT
    refine ⟨fun k P e D => ?_, fun e P D => ?_⟩
    · subst e; exact .sel_upper x ((ih T hT).1 (k + 1) P rfl D)
    · subst e
      refine (trans_left D _ _ ?_ (.sel_upper x h)).1 rfl
      rintro P' (e | ⟨_, _, _, _, _, e, _⟩ | ⟨_, _, _, _, e, _⟩ | ⟨y, e, h1⟩)
      · simp at e
      · simp at e
      · simp at e
      · simp only [Ty.sel.injEq] at e
        subst e
        exact .bad_bounds x h1 h
  | bad_bounds x h1 h2 ih1 ih2 =>
    intro T hT
    refine ⟨fun k P e D => ?_, fun e P D => ?_⟩
    · subst e; exact .bad_bounds x h1 ((ih2 T hT).1 (k + 1) P rfl D)
    · subst e; exact .bad_bounds x ((ih1 _ hT).1 0 P rfl D) h2

theorem Sub.transAt {n : ℕ} (T : Ty n) : TransAt T := by
  induction T with
  | top => exact fun Γ P U D E => (trans_right E _ ⟨by simp, by simp⟩).2 rfl P D
  | bot => exact fun Γ P U D E => (trans_right E _ ⟨by simp, by simp⟩).2 rfl P D
  | sel x => exact fun Γ P U D E => (trans_right E _ ⟨by simp, by simp⟩).2 rfl P D
  | bnd S U ihS ihU =>
    refine fun Γ P V D E => (trans_right E _ ⟨?_, by simp⟩).2 rfl P D
    intro S' U' e
    simp only [Ty.bnd.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨ihS, ihU⟩
  | all S T _ ihT =>
    refine fun Γ P V D E => (trans_right E _ ⟨by simp, ?_⟩).2 rfl P D
    intro S' T' e
    simp only [Ty.all.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ihT

/-- Transitivity is admissible. -/
theorem Sub.trans {n : ℕ} {Γ : Ctx n} {S T U : Ty n} (h₁ : Sub Γ S T) (h₂ : Sub Γ T U) :
    Sub Γ S U :=
  Sub.transAt T Γ S U h₁ h₂

end Dsub
