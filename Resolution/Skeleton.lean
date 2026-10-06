import Resolution.Sized

/-!
The skeleton of PROOF.md §5, abstract in the normaliser and the bound.

`NSub g G` has the rules of `Sub`, except that the premise of the `all` rule is the
normalised judgment `g ⟨Γ, z:S ⊢ B <: B'⟩`, which must also satisfy `G` (the bound on created
variables, in PROOF.md).  Soundness needs `g` sound; completeness needs `g` to keep
derivations with their heights, to keep the invariant, and to land in `G` from annotated
judgments (the last is where Lemma 4 will enter).
-/

namespace Dsub

/-- Subtyping with the premise of the `all` rule normalised by `g` and required to satisfy
`G`. -/
inductive NSub (g : Judgment → Judgment) (G : Judgment → Prop) :
    {n : ℕ} → Ctx n → Ty n → Ty n → Prop where
  | top {n : ℕ} {Γ : Ctx n} (T : Ty n) : NSub g G Γ T .top
  | bot {n : ℕ} {Γ : Ctx n} (T : Ty n) : NSub g G Γ .bot T
  | refl_sel {n : ℕ} {Γ : Ctx n} (x : BVar n) : NSub g G Γ (.sel x) (.sel x)
  | bnd {n : ℕ} {Γ : Ctx n} {S₁ U₁ S₂ U₂ : Ty n} :
      NSub g G Γ S₂ S₁ → NSub g G Γ U₁ U₂ → NSub g G Γ (.bnd S₁ U₁) (.bnd S₂ U₂)
  | all {n : ℕ} {Γ : Ctx n} {S : Ty n} {B B' : Ty (n + 1)} :
      G (g ⟨Γ.push S, B, B'⟩) →
      NSub g G (g ⟨Γ.push S, B, B'⟩).Γ (g ⟨Γ.push S, B, B'⟩).S (g ⟨Γ.push S, B, B'⟩).U →
      NSub g G Γ (.all S B) (.all S B')
  | sel_lower {n : ℕ} {Γ : Ctx n} {S : Ty n} (x : BVar n) :
      NSub g G Γ (Γ.lookup x) (.bnd S .top) → NSub g G Γ S (.sel x)
  | sel_upper {n : ℕ} {Γ : Ctx n} {U : Ty n} (x : BVar n) :
      NSub g G Γ (Γ.lookup x) (.bnd .bot U) → NSub g G Γ (.sel x) U
  | bad_bounds {n : ℕ} {Γ : Ctx n} {S U : Ty n} (x : BVar n) :
      NSub g G Γ (Γ.lookup x) (.bnd S .top) → NSub g G Γ (Γ.lookup x) (.bnd .bot U) →
      NSub g G Γ S U

/-- Soundness: `NSub ⊆ Sub` when the normaliser is sound. -/
theorem NSub.sound {g : Judgment → Judgment} {G : Judgment → Prop}
    (hg : ∀ j : Judgment, (g j).Holds → j.Holds) {n : ℕ} {Γ : Ctx n} {S U : Ty n}
    (d : NSub g G Γ S U) : Sub Γ S U := by
  induction d with
  | top T => exact .top T
  | bot T => exact .bot T
  | refl_sel x => exact .refl_sel x
  | bnd _ _ ih1 ih2 => exact .bnd ih1 ih2
  | all _ _ ih => exact .all (hg _ ih)
  | sel_lower x _ ih => exact .sel_lower x ih
  | sel_upper x _ ih => exact .sel_upper x ih
  | bad_bounds x _ _ ih1 ih2 => exact .bad_bounds x ih1 ih2

/-- A property of judgments that every rule passes from its conclusion to its premises
(Lemma 2 for the invariant). -/
structure BackClosed (P : Judgment → Prop) : Prop where
  bnd : ∀ {n : ℕ} {Γ : Ctx n} {S₁ U₁ S₂ U₂ : Ty n}, P ⟨Γ, .bnd S₁ U₁, .bnd S₂ U₂⟩ →
    P ⟨Γ, S₂, S₁⟩ ∧ P ⟨Γ, U₁, U₂⟩
  all : ∀ {n : ℕ} {Γ : Ctx n} {S : Ty n} {B B' : Ty (n + 1)}, P ⟨Γ, .all S B, .all S B'⟩ →
    P ⟨Γ.push S, B, B'⟩
  sel_lower : ∀ {n : ℕ} {Γ : Ctx n} {S : Ty n} {x : BVar n}, P ⟨Γ, S, .sel x⟩ →
    P ⟨Γ, Γ.lookup x, .bnd S .top⟩
  sel_upper : ∀ {n : ℕ} {Γ : Ctx n} {U : Ty n} {x : BVar n}, P ⟨Γ, .sel x, U⟩ →
    P ⟨Γ, Γ.lookup x, .bnd .bot U⟩
  bad_bounds : ∀ {n : ℕ} {Γ : Ctx n} {S U : Ty n}, P ⟨Γ, S, U⟩ → ∀ x : BVar n,
    P ⟨Γ, Γ.lookup x, .bnd S .top⟩ ∧ P ⟨Γ, Γ.lookup x, .bnd .bot U⟩

theorem BackClosed.and {P Q : Judgment → Prop} (hP : BackClosed P) (hQ : BackClosed Q) :
    BackClosed (fun j => P j ∧ Q j) where
  bnd := fun h => ⟨⟨(hP.bnd h.1).1, (hQ.bnd h.2).1⟩, ⟨(hP.bnd h.1).2, (hQ.bnd h.2).2⟩⟩
  all := fun h => ⟨hP.all h.1, hQ.all h.2⟩
  sel_lower := fun h => ⟨hP.sel_lower h.1, hQ.sel_lower h.2⟩
  sel_upper := fun h => ⟨hP.sel_upper h.1, hQ.sel_upper h.2⟩
  bad_bounds := fun h x =>
    ⟨⟨(hP.bad_bounds h.1 x).1, (hQ.bad_bounds h.2 x).1⟩,
     ⟨(hP.bad_bounds h.1 x).2, (hQ.bad_bounds h.2 x).2⟩⟩

/-- Completeness for any backward-closed property `P`: with a normaliser that keeps
derivations with their heights and keeps `P`, and lands in `G` from `P`, every derivable
judgment satisfying `P` is derivable in `NSub`. -/
theorem NSub.complete_of {P : Judgment → Prop} {g : Judgment → Judgment} {G : Judgment → Prop}
    (hP : BackClosed P)
    (hg : ∀ (j : Judgment) (h : ℕ), SubH h j.Γ j.S j.U → SubH h (g j).Γ (g j).S (g j).U)
    (hgP : ∀ j, P j → P (g j)) (hG : ∀ j, P j → G (g j)) :
    ∀ (h : ℕ) {n : ℕ} {Γ : Ctx n} {S U : Ty n}, SubH h Γ S U → P ⟨Γ, S, U⟩ →
      NSub g G Γ S U := by
  intro h
  induction h with
  | zero =>
    intro n Γ S U d _
    cases d with
    | top _ => exact .top _
    | bot _ => exact .bot _
    | refl_sel _ => exact .refl_sel _
  | succ h ih =>
    intro n Γ S U d hj
    cases d with
    | top _ => exact .top _
    | bot _ => exact .bot _
    | refl_sel _ => exact .refl_sel _
    | bnd d1 d2 => exact .bnd (ih d1 (hP.bnd hj).1) (ih d2 (hP.bnd hj).2)
    | all d =>
      have hj' := hP.all hj
      exact .all (hG _ hj') (ih (hg _ h d) (hgP _ hj'))
    | sel_lower x d => exact .sel_lower x (ih d (hP.sel_lower hj))
    | sel_upper x d => exact .sel_upper x (ih d (hP.sel_upper hj))
    | bad_bounds x d1 d2 =>
      exact .bad_bounds x (ih d1 (hP.bad_bounds hj x).1) (ih d2 (hP.bad_bounds hj x).2)

/-- A judgment admits an annotation satisfying the invariant with bound `N`. -/
def Annotated (N : ℕ) (j : Judgment) : Prop := ∃ a, Inv N j.Γ a j.S j.U

theorem Annotated.root {n N : ℕ} {Γ : Ctx n} {S U : Ty n} (hS : S.nu ≤ N) (hU : U.nu ≤ N)
    (hΓ : ∀ x, (Γ.lookup x).nu ≤ N) : Annotated N ⟨Γ, S, U⟩ :=
  ⟨Ann.root, Inv.root hS hU hΓ⟩

/-- Lemma 2. -/
theorem Annotated.backClosed (N : ℕ) : BackClosed (Annotated N) where
  bnd := fun ⟨a, h⟩ => ⟨⟨a, h.bnd.1⟩, ⟨a, h.bnd.2⟩⟩
  all := fun ⟨_, h⟩ => ⟨_, h.all⟩
  sel_lower := fun ⟨a, h⟩ => ⟨a, h.sel_lower⟩
  sel_upper := fun ⟨a, h⟩ => ⟨a, h.sel_upper⟩
  bad_bounds := fun ⟨a, h⟩ x => ⟨⟨a, (h.bad_bounds x).1⟩, ⟨a, (h.bad_bounds x).2⟩⟩

/-- The size bound as a property of judgments. -/
def SizedJ (s : ℕ) (j : Judgment) : Prop := Sized s j.Γ j.S j.U

theorem SizedJ.backClosed (s : ℕ) : BackClosed (SizedJ s) where
  bnd := fun h => Sized.bnd h
  all := fun h => Sized.all h
  sel_lower := fun h => Sized.sel_lower h
  sel_upper := fun h => Sized.sel_upper h
  bad_bounds := fun h x => Sized.bad_bounds h x

/-- The full invariant of a judgment: an annotation with `I` for bound `N`, and sizes at most
`s`. -/
def Invariant (N s : ℕ) (j : Judgment) : Prop := Annotated N j ∧ SizedJ s j

theorem Invariant.backClosed (N s : ℕ) : BackClosed (Invariant N s) :=
  (Annotated.backClosed N).and (SizedJ.backClosed s)

theorem Invariant.root {n N s : ℕ} {Γ : Ctx n} {S U : Ty n} (hS : S.nu ≤ N) (hU : U.nu ≤ N)
    (hΓ : ∀ x, (Γ.lookup x).nu ≤ N) (hS' : S.size ≤ s) (hU' : U.size ≤ s)
    (hΓ' : ∀ x, (Γ.lookup x).size ≤ s) : Invariant N s ⟨Γ, S, U⟩ :=
  ⟨Annotated.root hS hU hΓ, Sized.root hS' hU' hΓ'⟩

/-- Removing variables along a thinning keeps the full invariant. -/
theorem Invariant.restrict {m n N s : ℕ} {Γ : Ctx n} {θ : Thin m n} {Δ : Ctx m}
    {S U : Ty n} {S' U' : Ty m} (hΔ : Γ.restrict θ = some Δ) (hS : S.unthin θ = some S')
    (hU : U.unthin θ = some U') (h : Invariant N s ⟨Γ, S, U⟩) : Invariant N s ⟨Δ, S', U'⟩ :=
  ⟨⟨_, h.1.choose_spec.restrict hΔ hS hU⟩, Sized.restrict hΔ hS hU h.2⟩

/-- Completeness with the annotation invariant alone. -/
theorem NSub.complete {N : ℕ} {g : Judgment → Judgment} {G : Judgment → Prop}
    (hg : ∀ (j : Judgment) (h : ℕ), SubH h j.Γ j.S j.U → SubH h (g j).Γ (g j).S (g j).U)
    (hgI : ∀ j, Annotated N j → Annotated N (g j))
    (hG : ∀ j, Annotated N j → G (g j)) :
    ∀ (h : ℕ) {n : ℕ} {Γ : Ctx n} {S U : Ty n}, SubH h Γ S U → Annotated N ⟨Γ, S, U⟩ →
      NSub g G Γ S U :=
  NSub.complete_of (Annotated.backClosed N) hg hgI hG

/-- `NSub` and `Sub` agree on judgments satisfying a backward-closed `P`, for a sound
normaliser that keeps derivations and `P` and lands in `G`. -/
theorem NSub.iff_of {P : Judgment → Prop} {g : Judgment → Judgment} {G : Judgment → Prop}
    (hP : BackClosed P) (hsound : ∀ j : Judgment, (g j).Holds → j.Holds)
    (hg : ∀ (j : Judgment) (h : ℕ), SubH h j.Γ j.S j.U → SubH h (g j).Γ (g j).S (g j).U)
    (hgP : ∀ j, P j → P (g j)) (hG : ∀ j, P j → G (g j)) {n : ℕ} {Γ : Ctx n} {S U : Ty n}
    (hj : P ⟨Γ, S, U⟩) : NSub g G Γ S U ↔ Sub Γ S U := by
  constructor
  · exact NSub.sound hsound
  · intro d
    obtain ⟨h, d⟩ := d.subH
    exact NSub.complete_of hP hg hgP hG h d hj

/-- The two directions together, for the annotation invariant. -/
theorem NSub.iff {N : ℕ} {g : Judgment → Judgment} {G : Judgment → Prop}
    (hsound : ∀ j : Judgment, (g j).Holds → j.Holds)
    (hg : ∀ (j : Judgment) (h : ℕ), SubH h j.Γ j.S j.U → SubH h (g j).Γ (g j).S (g j).U)
    (hgI : ∀ j, Annotated N j → Annotated N (g j))
    (hG : ∀ j, Annotated N j → G (g j)) {n : ℕ} {Γ : Ctx n} {S U : Ty n}
    (hj : Annotated N ⟨Γ, S, U⟩) : NSub g G Γ S U ↔ Sub Γ S U :=
  NSub.iff_of (Annotated.backClosed N) hsound hg hgI hG hj

end Dsub
