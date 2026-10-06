import Resolution.Annot

/-!
Collapses (PROOF.md §3) and Lemma 3: removing a collapse is exact, with heights, and keeps
the invariant.

The removed set `X` is a Boolean predicate on the variables.  The context without `X` is
`Γ.restrict (thinOf X)`, the kept variables embedded by the thinning `thinOf X`.  (C1) makes
the judgment strengthen along it, (C2) makes the restriction exist, and (C3) is stated
inside `Γ`: with `retr X r` the renaming that sends `w ∈ X` to `r w` and fixes the rest,
`Γ(r w) = retr(Γ(w))`.  (This is equivalent to PROOF.md's `Γ∖X(r w) = r̂(Γ(w))`, since
renaming along the inclusion is injective.)
-/

namespace Dsub

/-- `r` on the removed variables, the identity elsewhere. -/
def retr {n : ℕ} (X : BVar n → Bool) (r : BVar n → BVar n) : Rename n n :=
  ⟨fun x => if X x then r x else x⟩

/-- The thinning that keeps the variables outside `X`. -/
def thinOf {n : ℕ} (X : BVar n → Bool) : (m : ℕ) × Thin m n :=
  Thin.ofPred n (fun x => !X x)

theorem thinOf_range {n : ℕ} (X : BVar n → Bool) (x : BVar n) :
    (∃ y, (thinOf X).2.var y = x) ↔ X x = false := by
  rw [thinOf, Thin.ofPred_range]; simp

/-- A collapse of the state `Γ ⊢ S <: U`, with created variables `cr`: a non-empty set `X`
of created variables and a map `r` from `X` to created variables outside `X`. -/
structure Collapse {n : ℕ} (cr : BVar n → Prop) (Γ : Ctx n) (X : BVar n → Bool)
    (r : BVar n → BVar n) (S U : Ty n) : Prop where
  nonempty : ∃ x, X x = true
  created : ∀ x, X x = true → cr x
  /-- (C1) the judgment mentions no variable of `X`. -/
  left_free : ∀ x, X x = true → ¬ S.Occ x
  right_free : ∀ x, X x = true → ¬ U.Occ x
  /-- (C2) no variable outside `X` has a type mentioning a variable of `X`. -/
  closed : ∀ x, X x = false → ∀ y, (Γ.lookup x).Occ y → X y = false
  /-- (C3) `r` maps `X` to created variables outside `X` ... -/
  target : ∀ w, X w = true → X (r w) = false ∧ cr (r w)
  /-- ... and, extended by the identity, is a context morphism. -/
  morph : ∀ w, X w = true → Γ.lookup (r w) = (Γ.lookup w).rename (retr X r)

section

variable {n : ℕ} {cr : BVar n → Prop} {Γ : Ctx n} {X : BVar n → Bool} {r : BVar n → BVar n}
  {S U : Ty n}

theorem Collapse.retr_kept (c : Collapse cr Γ X r S U) (x : BVar n) :
    X ((retr X r).var x) = false := by
  simp only [retr]
  cases hx : X x
  · simpa using hx
  · simpa using (c.target x hx).1

theorem Collapse.retr_fix (x : BVar n) (hx : X x = false) : (retr X r).var x = x := by
  simp [retr, hx]

/-- `retr` is an endomorphism of `Γ`. -/
theorem Collapse.retr_morph (c : Collapse cr Γ X r S U) : (retr X r).IsCtxMorph Γ Γ := by
  intro x
  cases hx : X x
  · rw [Collapse.retr_fix x hx]
    conv => lhs; rw [← Ty.rename_id (T := Γ.lookup x)]
    apply Ty.rename_congr
    intro y hy
    simp [Collapse.retr_fix y (c.closed x hx y hy)]
  · simp only [retr, hx, ite_true]
    exact c.morph x hx

theorem Collapse.restrict_exists (c : Collapse cr Γ X r S U) :
    ∃ Δ, Γ.restrict (thinOf X).2 = some Δ := by
  apply Ctx.restrict_of_occ
  intro y x hx
  have hk : X ((thinOf X).2.var y) = false := (thinOf_range X _).1 ⟨y, rfl⟩
  exact (thinOf_range X x).2 (c.closed _ hk x hx)

theorem Collapse.unthin_left (c : Collapse cr Γ X r S U) :
    ∃ S', S.unthin (thinOf X).2 = some S' := by
  apply Ty.unthin_of_occ
  intro x hx
  apply (thinOf_range X x).2
  cases h : X x
  · rfl
  · exact absurd hx (c.left_free x h)

theorem Collapse.unthin_right (c : Collapse cr Γ X r S U) :
    ∃ U', U.unthin (thinOf X).2 = some U' := by
  apply Ty.unthin_of_occ
  intro x hx
  apply (thinOf_range X x).2
  cases h : X x
  · rfl
  · exact absurd hx (c.right_free x h)

/-- The retraction onto the context without `X`. -/
noncomputable def Collapse.proj (c : Collapse cr Γ X r S U) : Rename n (thinOf X).1 :=
  ⟨fun x => Classical.choose ((thinOf_range X _).2 (c.retr_kept x))⟩

theorem Collapse.proj_spec (c : Collapse cr Γ X r S U) (x : BVar n) :
    (thinOf X).2.var (c.proj.var x) = (retr X r).var x :=
  Classical.choose_spec ((thinOf_range X _).2 (c.retr_kept x))

theorem Collapse.thin_proj (c : Collapse cr Γ X r S U) :
    (thinOf X).2.ren.comp c.proj = Rename.id := by
  apply Rename.ext
  intro y
  apply (thinOf X).2.var_injective
  simp only [Rename.comp_var, Thin.ren_var, Rename.id_var, c.proj_spec]
  exact Collapse.retr_fix _ ((thinOf_range X _).1 ⟨y, rfl⟩)

theorem Collapse.proj_thin (c : Collapse cr Γ X r S U) :
    c.proj.comp (thinOf X).2.ren = retr X r := by
  apply Rename.ext
  intro x
  simp [c.proj_spec]

theorem Collapse.proj_morph (c : Collapse cr Γ X r S U) {Δ : Ctx (thinOf X).1}
    (hΔ : Γ.restrict (thinOf X).2 = some Δ) : c.proj.IsCtxMorph Γ Δ := by
  intro x
  apply Ty.rename_inj (f := (thinOf X).2.ren) (thinOf X).2.var_injective
  calc (Δ.lookup (c.proj.var x)).rename (thinOf X).2.ren
      = Γ.lookup ((thinOf X).2.ren.var (c.proj.var x)) := (Ctx.restrict_morph hΔ _).symm
    _ = Γ.lookup ((retr X r).var x) := by rw [Thin.ren_var, c.proj_spec]
    _ = (Γ.lookup x).rename (retr X r) := c.retr_morph x
    _ = ((Γ.lookup x).rename c.proj).rename (thinOf X).2.ren := by
      rw [Ty.rename_comp, c.proj_thin]

/-- Lemma 3: removing a collapse is exact, by derivations of the same height. -/
theorem Collapse.exact (c : Collapse cr Γ X r S U) {Δ : Ctx (thinOf X).1}
    {S' U' : Ty (thinOf X).1} (hΔ : Γ.restrict (thinOf X).2 = some Δ)
    (hS : S.unthin (thinOf X).2 = some S') (hU : U.unthin (thinOf X).2 = some U') (h : ℕ) :
    SubH h Γ S U ↔ SubH h Δ S' U' := by
  rw [← Ty.unthin_rename hS, ← Ty.unthin_rename hU]
  constructor
  · intro d
    have := d.rename (c.proj_morph hΔ)
    rwa [Ty.rename_comp, Ty.rename_comp, c.thin_proj, Ty.rename_id, Ty.rename_id] at this
  · intro d
    exact d.rename (Ctx.restrict_morph hΔ)

/-- Lemma 3, existence form: the context and the judgment without `X` exist, and the
judgment holds there exactly when it holds in `Γ`, by derivations of the same height. -/
theorem Collapse.exact' (c : Collapse cr Γ X r S U) :
    ∃ Δ S' U', Γ.restrict (thinOf X).2 = some Δ ∧ S.unthin (thinOf X).2 = some S' ∧
      U.unthin (thinOf X).2 = some U' ∧ ∀ h, SubH h Γ S U ↔ SubH h Δ S' U' := by
  obtain ⟨Δ, hΔ⟩ := c.restrict_exists
  obtain ⟨S', hS⟩ := c.unthin_left
  obtain ⟨U', hU⟩ := c.unthin_right
  exact ⟨Δ, S', U', hΔ, hS, hU, c.exact hΔ hS hU⟩

end

/-! ### The annotation after a collapse -/

/-- The annotation restricted to the kept variables.  The ancestor relation is restricted,
which re-parents every kept variable to its nearest kept ancestor. -/
def Ann.restrict {m n : ℕ} (a : Ann n) (θ : Thin m n) : Ann m where
  cr := fun y => a.cr (θ.var y)
  anc := fun u v => a.anc (θ.var u) (θ.var v)
  dep := fun y => a.dep (θ.var y)
  anc_trans := fun h1 h2 => a.anc_trans h1 h2
  anc_dep := fun h => a.anc_dep h
  anc_chain := fun h1 h2 => by
    rcases a.anc_chain h1 h2 with e | e | e
    · exact Or.inl (θ.var_injective e)
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr e)
  anc_cr := fun h => a.anc_cr h
  dep_pos := fun h => a.dep_pos h

/-- Restricting a state along a thinning keeps the invariant. -/
theorem Inv.restrict {m n N : ℕ} {Γ : Ctx n} {a : Ann n} {θ : Thin m n} {Δ : Ctx m}
    {S U : Ty n} {S' U' : Ty m} (hΔ : Γ.restrict θ = some Δ) (hS : S.unthin θ = some S')
    (hU : U.unthin θ = some U') (h : Inv N Γ a S U) : Inv N Δ (a.restrict θ) S' U' := by
  have eS := Ty.unthin_rename hS
  have eU := Ty.unthin_rename hU
  have eΓ := Ctx.restrict_morph hΔ
  have occ : ∀ {T : Ty m} {y : BVar m}, T.Occ y → (T.rename θ.ren).Occ (θ.var y) :=
    fun ho => Ty.occ_rename.2 ⟨_, rfl, ho⟩
  subst eS eU
  constructor
  · rw [← Ty.nu_rename (f := θ.ren)]; exact h.nu_left
  · rw [← Ty.nu_rename (f := θ.ren)]; exact h.nu_right
  · intro y; rw [← Ty.nu_rename (f := θ.ren), ← eΓ y]; exact h.nu_ctx _
  · intro x y ho hy
    have := occ ho
    rw [← eΓ x] at this
    exact h.ctx_anc _ _ this hy
  · intro x hx ho
    have := h.dep_left _ hx (occ ho)
    rwa [Ty.nu_rename] at this
  · intro x hx ho
    have := h.dep_right _ hx (occ ho)
    rwa [Ty.nu_rename] at this
  · intro x y hx ho
    have o := occ ho
    rw [← eΓ y] at o
    have := h.dep_ctx _ _ hx o
    have e2 : (Δ.lookup y).nu = (Γ.lookup (θ.ren.var y)).nu := by rw [eΓ y, Ty.nu_rename]
    show (Δ.lookup y).nu + a.dep (θ.var x) ≤ N
    rw [e2]; exact this
  · intro x y hx hy h1 h2 h3 h4
    rcases h.shared _ _ hx hy (occ h1) (occ h2) (occ h3) (occ h4) with e | e | e
    · exact Or.inl (θ.var_injective e)
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr e)
  · intro x hx; exact h.dep_le _ hx

end Dsub
