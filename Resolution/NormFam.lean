import Resolution.Good
import Resolution.FamilyEnum

/-!
Good judgments with at most `Bnd` created variables satisfy the conditions `Family.Norm` of
saturation over the family `Φ (n₀ + Bnd) s` of all contexts with at most `n₀ + Bnd`
variables and types of size at most `s`, given Lemma 4.  Hence `decideFam` decides every
input judgment within the bounds.
-/

namespace Dsub

theorem Ctx.bounded_of_lookup {s : ℕ} : ∀ {n : ℕ} {Γ : Ctx n},
    (∀ x, (Γ.lookup x).size ≤ s) → Γ.Bounded s
  | _, .empty, _ => trivial
  | _, .push Γ T, h =>
    ⟨Ctx.bounded_of_lookup (fun x => by simpa using h (.there x)),
     by simpa using h .here⟩

/-- The normalisation conditions of saturation over `Φ (n₀ + Bnd) s`, for good judgments
with at most `Bnd` created variables. -/
theorem GoodB.norm {N s n₀ Bnd : ℕ} (L4 : Lemma4 N s n₀ Bnd) :
    (Φ (n₀ + Bnd) s).Norm ((Φ (n₀ + Bnd) s).goodOf (GoodB N s n₀ Bnd)) where
  bnd := fun _ _ _ _ _ h => GoodB.bnd h
  sel_lower := fun _ _ _ h => GoodB.sel_lower h
  sel_upper := fun _ _ _ h => GoodB.sel_upper h
  bad_bounds := fun _ _ _ x h => GoodB.bad_bounds h x
  all := by
    intro i T B₁ B₂ h h1 h2 hg d
    obtain ⟨a, hI, hs, hb, -⟩ := hg
    have hb' : (a.enter (.all T B₁) (.all T B₂)).nBase ≤ n₀ := by
      rw [Ann.enter, Ann.nBase_push]; exact hb
    obtain ⟨m, Δ, S', U', a', ι, hI', hs', hb'', hB', -, hmor, eS, eU, -, -, hiff⟩ :=
      Dsub.normalise L4 _ rfl hI.all hs.all hb'
    have hm : m ≤ n₀ + Bnd := by have := a'.nBase_add_nCreated; omega
    obtain ⟨j, e⟩ := Φ.exists_member hm (Ctx.bounded_of_lookup hs'.ctx)
    obtain ⟨e1, e2⟩ := Sigma.mk.inj_iff.1 e
    subst e1
    have e3 := eq_of_heq e2
    subst e3
    have s1 := Φ.mem_F.1 h1
    have s2 := Φ.mem_F.1 h2
    simp only [Ty.size] at s1 s2
    refine ⟨j, S', U', ι, hmor, eS, eU, Φ.mem_F.2 ?_, mem_ext_of_mem (Φ.mem_F.2 ?_),
      (hiff h).1 d, ⟨a', hI', hs', hb'', hB'⟩⟩
    · rw [← Ty.size_rename S' ι, eS]; omega
    · rw [← Ty.size_rename U' ι, eU]; omega

/-- Given Lemma 4 for the bounds `N`, `s`, `n₀`, `Bnd`, `decideFam (n₀ + Bnd) s` decides
every judgment over a context of `n₀` variables whose types have `∀`-nesting at most `N`
and size at most `s`. -/
theorem decideFam_iff_of_lemma4 {N s n₀ Bnd : ℕ} (L4 : Lemma4 N s n₀ Bnd) (hs : 1 ≤ s)
    {Γ : Ctx n₀} {S U : Ty n₀} (hS : S.nu ≤ N) (hU : U.nu ≤ N)
    (hΓ : ∀ x, (Γ.lookup x).nu ≤ N) (hS' : S.size ≤ s) (hU' : U.size ≤ s)
    (hΓ' : ∀ x, (Γ.lookup x).size ≤ s) :
    decideFam (n₀ + Bnd) s ⟨Γ, S, U⟩ = true ↔ Sub Γ S U := by
  constructor
  · exact decideFam_sound
  · intro h
    exact decideFam_complete hs (GoodB.norm L4) (j := ⟨Γ, S, U⟩) (Nat.le_add_right _ _)
      (Ctx.bounded_of_lookup hΓ') hS' hU' (GoodB.root hS hU hΓ hS' hU' hΓ') h

end Dsub
