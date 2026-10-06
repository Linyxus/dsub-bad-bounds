import Resolution.Skeleton
import Resolution.Counts

/-!
Good judgments and normalisation, abstract in Lemma 4.

A judgment is good (for bounds `N`, `s`, `n₀`) if it has an annotation satisfying the
invariant, its types have size at most `s` (up to the wrappers of the right side), and at
most `n₀` of its variables are not created.  Goodness is preserved backward by every rule and
by removing a collapse.  Given Lemma 4 (as the hypothesis `Lemma4`), removing collapses one
at a time normalises every good judgment to one with at most `Bnd` created variables, along
an injective context morphism that keeps the non-created variables, with derivations of the
same heights.
-/

namespace Dsub

/-! ### Counting variables -/

/-- Variables as numbers below the scope. -/
def BVar.toFin : {n : ℕ} → BVar n → Fin n
  | _, .here => ⟨0, Nat.succ_pos _⟩
  | _, .there x => x.toFin.succ

theorem BVar.toFin_bijective (n : ℕ) : Function.Bijective (BVar.toFin (n := n)) := by
  constructor
  · intro a b h
    induction a with
    | here => cases b with
      | here => rfl
      | there b => exact absurd (congrArg Fin.val h) (by simp [BVar.toFin])
    | there a ih => cases b with
      | here => exact absurd (congrArg Fin.val h) (by simp [BVar.toFin])
      | there b => simp only [BVar.toFin, Fin.succ_inj] at h; rw [ih h]
  · induction n with
    | zero => intro k; exact k.elim0
    | succ n ih =>
      intro k
      cases k using Fin.cases with
      | zero => exact ⟨.here, rfl⟩
      | succ k => obtain ⟨x, hx⟩ := ih k; exact ⟨.there x, by simp [BVar.toFin, hx]⟩

theorem BVar.card (n : ℕ) : Nat.card (BVar n) = n := by
  rw [Nat.card_eq_of_bijective _ (BVar.toFin_bijective n)]; simp

theorem Ann.nBase_add_nCreated {n : ℕ} (a : Ann n) : a.nBase + a.nCreated = n := by
  have := Set.ncard_add_ncard_compl {x | a.cr x}
  rw [Set.compl_ofPred, BVar.card] at this
  unfold Ann.nBase Ann.nCreated
  omega

theorem Ty.occCount_le_size {n : ℕ} (T : Ty n) : T.occCount ≤ T.size := by
  unfold Ty.occCount
  induction T with
  | top => simp [Ty.size]
  | bot => simp [Ty.size]
  | sel y => simp [Ty.size]
  | bnd S U ihS ihU =>
    simp only [Ty.occ_bnd, Ty.size]
    have := Set.ncard_union_le {x | S.Occ x} {x | U.Occ x}
    rw [Set.ofPred_or]
    omega
  | all S T ihS ihT =>
    simp only [Ty.occ_all, Ty.size]
    have h1 := Set.ncard_union_le {x | S.Occ x} {x | T.Occ (.there x)}
    have h2 : {x | T.Occ (.there x)}.ncard ≤ {y | T.Occ y}.ncard :=
      Set.ncard_le_ncard_of_injOn BVar.there (fun x hx => hx)
        (fun a _ b _ h => by cases h; rfl)
    rw [Set.ofPred_or]
    omega

theorem Ty.occCount_rename {n m : ℕ} {T : Ty n} {f : Rename n m}
    (hf : Function.Injective f.var) : (T.rename f).occCount = T.occCount := by
  unfold Ty.occCount
  have : {y | (T.rename f).Occ y} = f.var '' {x | T.Occ x} := by
    ext y; simp only [Ty.occ_rename, Set.mem_ofPred_eq, Set.mem_image]; aesop
  rw [this, Set.ncard_image_of_injective _ hf]

theorem Ty.RSized.occCount_le {n s : ℕ} {T : Ty n} (h : T.RSized s) : T.occCount ≤ s := by
  induction T with
  | top => exact le_trans (Ty.occCount_le_size _) h
  | bot => exact le_trans (Ty.occCount_le_size _) h
  | sel x => exact le_trans (Ty.occCount_le_size _) h
  | all S T => exact le_trans (Ty.occCount_le_size _) h
  | bnd L H _ ihH =>
    rcases h with h | ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact le_trans (Ty.occCount_le_size _) h
    · have e : (Ty.bnd .bot H).occCount = H.occCount := by
        unfold Ty.occCount; congr 1; ext x; simp
      rw [e]; exact ihH h
    · have e : (Ty.bnd L .top).occCount = L.occCount := by
        unfold Ty.occCount; congr 1; ext x; simp
      rw [e]; exact le_trans (Ty.occCount_le_size _) h

theorem Ann.nBase_push {n : ℕ} (a : Ann n) (p : Option (BVar n))
    (hp : ∀ q, p = some q → a.cr q) : (a.push p hp).nBase = a.nBase := by
  unfold Ann.nBase
  have : {x | ¬ (a.push p hp).cr x} = BVar.there '' {x | ¬ a.cr x} := by
    ext x
    cases x with
    | here => simp [Ann.push, Ann.pushCr]
    | there x => simp [Ann.push, Ann.pushCr]
  rw [this, Set.ncard_image_of_injective _ (fun a b h => by cases h; rfl)]

theorem Ann.nBase_restrict_le {m n : ℕ} (a : Ann n) (θ : Thin m n) :
    (a.restrict θ).nBase ≤ a.nBase :=
  Set.ncard_le_ncard_of_injOn θ.var (fun _ hx => hx) (θ.var_injective.injOn)

theorem Ann.nCreated_restrict_lt {m n : ℕ} (a : Ann n) (θ : Thin m n) {w : BVar n}
    (hw : a.cr w) (hn : ∀ y, θ.var y ≠ w) : (a.restrict θ).nCreated < a.nCreated := by
  unfold Ann.nCreated
  rw [← Set.ncard_image_of_injective _ θ.var_injective]
  apply Set.ncard_lt_ncard _ (Set.toFinite _)
  refine ⟨?_, fun h => ?_⟩
  · rintro _ ⟨y, hy, rfl⟩; exact hy
  · obtain ⟨y, _, e⟩ := h hw
    exact hn y e

theorem Ann.nBase_root {n : ℕ} : (Ann.root : Ann n).nBase = n := by
  have := (Ann.root : Ann n).nBase_add_nCreated
  have h0 : (Ann.root : Ann n).nCreated = 0 := by simp [Ann.nCreated, Ann.root]
  omega

theorem Ann.nCreated_root {n : ℕ} : (Ann.root : Ann n).nCreated = 0 := by
  simp [Ann.nCreated, Ann.root]

/-! ### Good judgments -/

/-- Good judgments: an annotation with the invariant for `N`, sizes at most `s`, and at
most `n₀` non-created variables. -/
def Good (N s n₀ : ℕ) (j : Judgment) : Prop :=
  ∃ a : Ann j.n, Inv N j.Γ a j.S j.U ∧ Sized s j.Γ j.S j.U ∧ a.nBase ≤ n₀

/-- Good judgments with at most `B` created variables. -/
def GoodB (N s n₀ B : ℕ) (j : Judgment) : Prop :=
  ∃ a : Ann j.n, Inv N j.Γ a j.S j.U ∧ Sized s j.Γ j.S j.U ∧ a.nBase ≤ n₀ ∧ a.nCreated ≤ B

theorem Good.root {n N s : ℕ} {Γ : Ctx n} {S U : Ty n} (hS : S.nu ≤ N) (hU : U.nu ≤ N)
    (hΓ : ∀ x, (Γ.lookup x).nu ≤ N) (hS' : S.size ≤ s) (hU' : U.size ≤ s)
    (hΓ' : ∀ x, (Γ.lookup x).size ≤ s) : Good N s n ⟨Γ, S, U⟩ :=
  ⟨Ann.root, Inv.root hS hU hΓ, Sized.root hS' hU' hΓ', le_of_eq Ann.nBase_root⟩

theorem GoodB.root {n N s B : ℕ} {Γ : Ctx n} {S U : Ty n} (hS : S.nu ≤ N) (hU : U.nu ≤ N)
    (hΓ : ∀ x, (Γ.lookup x).nu ≤ N) (hS' : S.size ≤ s) (hU' : U.size ≤ s)
    (hΓ' : ∀ x, (Γ.lookup x).size ≤ s) : GoodB N s n B ⟨Γ, S, U⟩ :=
  ⟨Ann.root, Inv.root hS hU hΓ, Sized.root hS' hU' hΓ', le_of_eq Ann.nBase_root,
    by rw [Ann.nCreated_root]; exact Nat.zero_le _⟩

theorem GoodB.good {N s n₀ B : ℕ} {j : Judgment} (h : GoodB N s n₀ B j) : Good N s n₀ j :=
  let ⟨a, h1, h2, h3, _⟩ := h; ⟨a, h1, h2, h3⟩

/-- Lemma 2 for good judgments. -/
theorem Good.backClosed (N s n₀ : ℕ) : BackClosed (Good N s n₀) where
  bnd := fun ⟨a, hI, hs, hb⟩ => ⟨⟨a, hI.bnd.1, hs.bnd.1, hb⟩, ⟨a, hI.bnd.2, hs.bnd.2, hb⟩⟩
  all := fun ⟨a, hI, hs, hb⟩ =>
    ⟨_, hI.all, hs.all, by rw [Ann.enter, Ann.nBase_push]; exact hb⟩
  sel_lower := fun ⟨a, hI, hs, hb⟩ => ⟨a, hI.sel_lower, hs.sel_lower, hb⟩
  sel_upper := fun ⟨a, hI, hs, hb⟩ => ⟨a, hI.sel_upper, hs.sel_upper, hb⟩
  bad_bounds := fun ⟨a, hI, hs, hb⟩ x =>
    ⟨⟨a, (hI.bad_bounds x).1, (hs.bad_bounds x).1, hb⟩,
     ⟨a, (hI.bad_bounds x).2, (hs.bad_bounds x).2, hb⟩⟩

/-- The rules other than `all` keep the annotation, hence the count of created variables. -/
theorem GoodB.bnd {N s n₀ B n : ℕ} {Γ : Ctx n} {S₁ U₁ S₂ U₂ : Ty n}
    (h : GoodB N s n₀ B ⟨Γ, .bnd S₁ U₁, .bnd S₂ U₂⟩) :
    GoodB N s n₀ B ⟨Γ, S₂, S₁⟩ ∧ GoodB N s n₀ B ⟨Γ, U₁, U₂⟩ :=
  let ⟨a, hI, hs, hb, hc⟩ := h
  ⟨⟨a, hI.bnd.1, hs.bnd.1, hb, hc⟩, ⟨a, hI.bnd.2, hs.bnd.2, hb, hc⟩⟩

theorem GoodB.sel_lower {N s n₀ B n : ℕ} {Γ : Ctx n} {S : Ty n} {x : BVar n}
    (h : GoodB N s n₀ B ⟨Γ, S, .sel x⟩) : GoodB N s n₀ B ⟨Γ, Γ.lookup x, .bnd S .top⟩ :=
  let ⟨a, hI, hs, hb, hc⟩ := h
  ⟨a, hI.sel_lower, hs.sel_lower, hb, hc⟩

theorem GoodB.sel_upper {N s n₀ B n : ℕ} {Γ : Ctx n} {U : Ty n} {x : BVar n}
    (h : GoodB N s n₀ B ⟨Γ, .sel x, U⟩) : GoodB N s n₀ B ⟨Γ, Γ.lookup x, .bnd .bot U⟩ :=
  let ⟨a, hI, hs, hb, hc⟩ := h
  ⟨a, hI.sel_upper, hs.sel_upper, hb, hc⟩

theorem GoodB.bad_bounds {N s n₀ B n : ℕ} {Γ : Ctx n} {S U : Ty n}
    (h : GoodB N s n₀ B ⟨Γ, S, U⟩) (x : BVar n) :
    GoodB N s n₀ B ⟨Γ, Γ.lookup x, .bnd S .top⟩ ∧ GoodB N s n₀ B ⟨Γ, Γ.lookup x, .bnd .bot U⟩ :=
  let ⟨a, hI, hs, hb, hc⟩ := h
  ⟨⟨a, (hI.bad_bounds x).1, (hs.bad_bounds x).1, hb, hc⟩,
   ⟨a, (hI.bad_bounds x).2, (hs.bad_bounds x).2, hb, hc⟩⟩

/-- Removing variables along a thinning keeps goodness (the counts only shrink). -/
theorem Good.restrict {m n N s n₀ : ℕ} {Γ : Ctx n} {θ : Thin m n} {Δ : Ctx m}
    {S U : Ty n} {S' U' : Ty m} {a : Ann n} (hΔ : Γ.restrict θ = some Δ)
    (hS : S.unthin θ = some S') (hU : U.unthin θ = some U') (hI : Inv N Γ a S U)
    (hs : Sized s Γ S U) (hb : a.nBase ≤ n₀) :
    Inv N Δ (a.restrict θ) S' U' ∧ Sized s Δ S' U' ∧ (a.restrict θ).nBase ≤ n₀ :=
  ⟨hI.restrict hΔ hS hU, hs.restrict hΔ hS hU, le_trans (a.nBase_restrict_le θ) hb⟩

/-! ### Normalisation, given Lemma 4 -/

/-- Lemma 4, as a hypothesis: a state with the invariant, sizes at most `s`, at most `s`
variables in each term and at most `n₀` non-created variables has at most `Bnd` created
variables or admits a collapse. -/
def Lemma4 (N s n₀ Bnd : ℕ) : Prop :=
  ∀ {n : ℕ} {Γ : Ctx n} {a : Ann n} {S U : Ty n}, Inv N Γ a S U →
    (∀ x, (Γ.lookup x).size ≤ s) → S.occCount ≤ s → U.occCount ≤ s → a.nBase ≤ n₀ →
    a.nCreated ≤ Bnd ∨ ∃ X r, Collapse a.cr Γ X r S U

/-- Normalisation: every good state is equivalent, with heights, to a good state with at
most `Bnd` created variables, which embeds into it along an injective context morphism that
keeps the non-created variables and maps the restricted annotation's created variables to
created ones. -/
theorem normalise {N s n₀ Bnd : ℕ} (L4 : Lemma4 N s n₀ Bnd) :
    ∀ (k : ℕ) {n : ℕ} {Γ : Ctx n} {S U : Ty n} {a : Ann n}, a.nCreated = k →
      Inv N Γ a S U → Sized s Γ S U → a.nBase ≤ n₀ →
      ∃ (m : ℕ) (Δ : Ctx m) (S' U' : Ty m) (a' : Ann m) (ι : Rename m n),
        Inv N Δ a' S' U' ∧ Sized s Δ S' U' ∧ a'.nBase ≤ n₀ ∧ a'.nCreated ≤ Bnd ∧
        Function.Injective ι.var ∧ ι.IsCtxMorph Δ Γ ∧ S'.rename ι = S ∧ U'.rename ι = U ∧
        (∀ x, ¬ a.cr x → ∃ y, ι.var y = x) ∧ (∀ y, a'.cr y ↔ a.cr (ι.var y)) ∧
        ∀ h, SubH h Γ S U ↔ SubH h Δ S' U' := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro n Γ S U a hk hI hs hb
  rcases L4 hI hs.ctx (le_trans (Ty.occCount_le_size S) hs.left) hs.right.occCount_le hb with
    hB | ⟨X, r, c⟩
  · exact ⟨n, Γ, S, U, a, Rename.id, hI, hs, hb, hB, fun _ _ h => h,
      Rename.isCtxMorph_id Γ, Ty.rename_id, Ty.rename_id, fun x _ => ⟨x, rfl⟩,
      fun _ => Iff.rfl, fun _ => Iff.rfl⟩
  · obtain ⟨Δ₁, S₁, U₁, hΔ, hS, hU, hiff⟩ := c.exact'
    set θ := (thinOf X).2
    obtain ⟨hI₁, hs₁, hb₁⟩ := Good.restrict hΔ hS hU hI hs hb
    obtain ⟨w, hw⟩ := c.nonempty
    have hlt : (a.restrict θ).nCreated < k := by
      rw [← hk]
      refine a.nCreated_restrict_lt θ (c.created w hw) (fun y e => ?_)
      have := (thinOf_range X w).1 ⟨y, e⟩
      rw [hw] at this; exact Bool.noConfusion this
    obtain ⟨m, Δ, S', U', a', ι, hI', hs', hb', hB', hinj, hmor, eS, eU, hkeep, hcr, hiff'⟩ :=
      ih _ hlt rfl hI₁ hs₁ hb₁
    refine ⟨m, Δ, S', U', a', ι.comp θ.ren, hI', hs', hb', hB', ?_, hmor.comp
      (Ctx.restrict_morph hΔ), ?_, ?_, ?_, ?_, ?_⟩
    · intro u v e
      exact hinj (θ.var_injective e)
    · rw [← Ty.rename_comp, eS, Ty.unthin_rename hS]
    · rw [← Ty.rename_comp, eU, Ty.unthin_rename hU]
    · intro x hx
      have hX : X x = false := by
        cases h : X x
        · rfl
        · exact absurd (c.created x h) hx
      obtain ⟨y, rfl⟩ := (thinOf_range X x).2 hX
      obtain ⟨z, hz⟩ := hkeep y hx
      exact ⟨z, by simp [hz, θ]⟩
    · intro y; rw [hcr y]; rfl
    · intro h; rw [hiff h, hiff' h]

/-- Normalisation of good judgments. -/
theorem Good.normalise {N s n₀ Bnd : ℕ} (L4 : Lemma4 N s n₀ Bnd) {j : Judgment}
    (hj : Good N s n₀ j) :
    ∃ (j' : Judgment) (ι : Rename j'.n j.n), GoodB N s n₀ Bnd j' ∧
      Function.Injective ι.var ∧ ι.IsCtxMorph j'.Γ j.Γ ∧ j'.S.rename ι = j.S ∧
      j'.U.rename ι = j.U ∧ ∀ h, SubH h j.Γ j.S j.U ↔ SubH h j'.Γ j'.S j'.U := by
  obtain ⟨a, hI, hs, hb⟩ := hj
  obtain ⟨m, Δ, S', U', a', ι, hI', hs', hb', hB', hinj, hmor, eS, eU, -, -, hiff⟩ :=
    Dsub.normalise L4 _ rfl hI hs hb
  exact ⟨⟨Δ, S', U'⟩, ι, ⟨a', hI', hs', hb', hB'⟩, hinj, hmor, eS, eU, hiff⟩

/-- A good judgment with at most `Bnd` created variables has at most `n₀ + Bnd` variables. -/
theorem GoodB.scope_le {N s n₀ B : ℕ} {j : Judgment} (h : GoodB N s n₀ B j) : j.n ≤ n₀ + B := by
  obtain ⟨a, -, -, hb, hc⟩ := h
  have := a.nBase_add_nCreated
  omega

end Dsub
