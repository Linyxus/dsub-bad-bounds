import Resolution.Family

/-!
The concrete family `Φ L s`: every context of at most `L` variables whose types have size at
most `s`, each with the set of all types of size at most `s` over it.
-/

namespace Dsub

/-! ### Sizes and enumerations of types -/

/-- The number of constructors of a type. -/
def Ty.size {n : ℕ} : Ty n → ℕ
  | .top => 1
  | .bot => 1
  | .sel _ => 1
  | .bnd S U => S.size + U.size + 1
  | .all S T => S.size + T.size + 1

theorem Ty.size_pos {n : ℕ} (T : Ty n) : 1 ≤ T.size := by
  cases T <;> simp only [Ty.size] <;> omega

theorem Ty.size_rename {n m : ℕ} (T : Ty n) (f : Rename n m) : (T.rename f).size = T.size := by
  induction T generalizing m with
  | top => rfl
  | bot => rfl
  | sel x => rfl
  | bnd S U ihS ihU => simp only [Ty.rename, Ty.size, ihS, ihU]
  | all S T ihS ihT => simp only [Ty.rename, Ty.size, ihS, ihT]

/-- All types of size at most `s`, in every scope. -/
def tysList : ℕ → (n : ℕ) → List (Ty n)
  | 0, _ => []
  | s + 1, n =>
    (([Ty.top, Ty.bot] ++ (BVar.list n).map Ty.sel ++
      (tysList s n).flatMap (fun S => (tysList s n).map (Ty.bnd S)) ++
      (tysList s n).flatMap (fun S => (tysList s (n + 1)).map (Ty.all S)))).filter
      (fun T => T.size ≤ s + 1)

theorem mem_tysList : ∀ {s n : ℕ} {T : Ty n}, T ∈ tysList s n ↔ T.size ≤ s
  | 0, n, T => by simp only [tysList, List.not_mem_nil, false_iff]; have := T.size_pos; omega
  | s + 1, n, T => by
    simp only [tysList, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    intro h
    simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_flatMap,
      List.not_mem_nil, or_false]
    cases T with
    | top => exact Or.inl (Or.inl (Or.inl (Or.inl rfl)))
    | bot => exact Or.inl (Or.inl (Or.inl (Or.inr rfl)))
    | sel x => exact Or.inl (Or.inl (Or.inr ⟨x, BVar.mem_list x, rfl⟩))
    | bnd S U =>
      simp only [Ty.size] at h
      exact Or.inl (Or.inr ⟨S, mem_tysList.2 (by omega), U, mem_tysList.2 (by omega), rfl⟩)
    | all S U =>
      simp only [Ty.size] at h
      exact Or.inr ⟨S, mem_tysList.2 (by omega), U, mem_tysList.2 (by omega), rfl⟩

/-- The types of size at most `s` in scope `n`. -/
def tysUpTo (n s : ℕ) : Finset (Ty n) := (tysList s n).toFinset

theorem mem_tysUpTo {n s : ℕ} {T : Ty n} : T ∈ tysUpTo n s ↔ T.size ≤ s := by
  simp only [tysUpTo, List.mem_toFinset, mem_tysList]

/-! ### Contexts -/

deriving instance DecidableEq for Ctx

/-- Every type of the context, in its own scope, has size at most `s`. -/
def Ctx.Bounded (s : ℕ) : {n : ℕ} → Ctx n → Prop
  | _, .empty => True
  | _, .push Γ T => Γ.Bounded s ∧ T.size ≤ s

instance Ctx.decidableBounded (s : ℕ) : {n : ℕ} → (Γ : Ctx n) → Decidable (Γ.Bounded s)
  | _, .empty => isTrue trivial
  | _, .push Γ _ => @instDecidableAnd _ _ (Ctx.decidableBounded s Γ) (Nat.decLe _ _)

theorem Ctx.Bounded.lookup {s n : ℕ} {Γ : Ctx n} (h : Γ.Bounded s) (x : BVar n) :
    (Γ.lookup x).size ≤ s := by
  induction Γ with
  | empty => nomatch x
  | push Γ T ih =>
    cases x with
    | here => simp only [Ctx.lookup_here, Ty.weaken, Ty.size_rename]; exact h.2
    | there x => simp only [Ctx.lookup_there, Ty.weaken, Ty.size_rename]; exact ih h.1 x

/-- All contexts of `n` variables with types of size at most `s`. -/
def ctxList (s : ℕ) : (n : ℕ) → List (Ctx n)
  | 0 => [.empty]
  | n + 1 => (ctxList s n).flatMap (fun Γ => (tysList s n).map (.push Γ))

theorem mem_ctxList {s : ℕ} : ∀ {n : ℕ} {Γ : Ctx n}, Γ ∈ ctxList s n ↔ Γ.Bounded s
  | 0, .empty => by simp [ctxList, Ctx.Bounded]
  | n + 1, .push Γ T => by
    simp only [ctxList, List.mem_flatMap, List.mem_map, Ctx.push.injEq, Ctx.Bounded]
    constructor
    · rintro ⟨Γ', hΓ', T', hT', rfl, rfl⟩
      exact ⟨mem_ctxList.1 hΓ', mem_tysList.1 hT'⟩
    · rintro ⟨hΓ, hT⟩
      exact ⟨Γ, mem_ctxList.2 hΓ, T, mem_tysList.2 hT, rfl, rfl⟩

/-- The members of `Φ L s`: the contexts of at most `L` variables with types of size at most
`s`. -/
def members (L s : ℕ) : List ((n : ℕ) × Ctx n) :=
  (List.range (L + 1)).flatMap (fun n => (ctxList s n).map (fun Γ => ⟨n, Γ⟩))

theorem mem_members {L s n : ℕ} {Γ : Ctx n} :
    (⟨n, Γ⟩ : (n : ℕ) × Ctx n) ∈ members L s ↔ n ≤ L ∧ Γ.Bounded s := by
  simp only [members, List.mem_flatMap, List.mem_range, List.mem_map, Sigma.mk.injEq]
  constructor
  · rintro ⟨n', hn, Γ', hΓ, rfl, h⟩
    rw [heq_iff_eq] at h
    subst h
    exact ⟨by omega, mem_ctxList.1 hΓ⟩
  · rintro ⟨hn, hΓ⟩
    exact ⟨n, by omega, Γ, mem_ctxList.2 hΓ, rfl, HEq.rfl⟩

/-! ### The family -/

/-- The family of all contexts of at most `L` variables with types of size at most `s`, each
with the types of size at most `s`. -/
def Φ (L s : ℕ) : Family where
  size := (members L s).length
  dim i := ((members L s).get i).1
  ctx i := ((members L s).get i).2
  F _ := tysUpTo _ s

theorem Φ.member_bounds (L s : ℕ) (i : Fin (Φ L s).size) :
    (Φ L s).dim i ≤ L ∧ ((Φ L s).ctx i).Bounded s :=
  mem_members.1 (List.get_mem (members L s) i)

theorem Φ.mem_F {L s : ℕ} {i : Fin (Φ L s).size} {T : Ty ((Φ L s).dim i)} :
    T ∈ (Φ L s).F i ↔ T.size ≤ s :=
  mem_tysUpTo

/-- Every bounded context is a member. -/
theorem Φ.exists_member {L s n : ℕ} {Γ : Ctx n} (hn : n ≤ L) (hΓ : Γ.Bounded s) :
    ∃ i : Fin (Φ L s).size, (⟨(Φ L s).dim i, (Φ L s).ctx i⟩ : (n : ℕ) × Ctx n) = ⟨n, Γ⟩ := by
  obtain ⟨i, e⟩ := List.mem_iff_get.1 (mem_members.2 ⟨hn, hΓ⟩)
  exact ⟨i, e⟩

theorem Φ.wf {L s : ℕ} (hs : 1 ≤ s) : (Φ L s).WF where
  top_mem _ := Φ.mem_F.2 hs
  bot_mem _ := Φ.mem_F.2 hs
  lookup_mem i x := Φ.mem_F.2 ((Φ.member_bounds L s i).2.lookup x)
  closed _ L H h := by
    rw [Φ.mem_F] at h
    simp only [Ty.size] at h
    exact ⟨Φ.mem_F.2 (by omega), Φ.mem_F.2 (by omega)⟩

/-- A predicate on judgments, read on the members of `Φ L s`. -/
def Family.goodOf (Φ : Family) (G : Judgment → Prop) (i : Fin Φ.size) (P U : Ty (Φ.dim i)) :
    Prop :=
  G ⟨Φ.ctx i, P, U⟩

end Dsub
