import Resolution.PrimBasic

/-!
# Least fixpoints over a finite universe of codes

`lfpIter fires Mb m i` is the `i`-th iterate of the rule-firing operator over the universe
`{j < Mb m}`: `R₀ = []` and `R_{i+1}` is the list of `j < Mb m` with `fires m R_i j`.
`lfpList fires Mb m` is the iterate after `Mb m` steps. Both are primitive recursive when
`fires` and `Mb` are; when `fires` is monotone the iterates increase and `lfpList` is a fixed
point.
-/

namespace Dsub

section Fix

variable (fires : ℕ → List ℕ → ℕ → Bool) (Mb : ℕ → ℕ)

/-- The iterates of the rule-firing operator. -/
def lfpIter (m : ℕ) : ℕ → List ℕ
  | 0 => []
  | i + 1 => (List.range (Mb m)).filter (fires m (lfpIter m i))

/-- The iterate after `Mb m` steps: the least fixpoint when `fires` is monotone. -/
def lfpList (m : ℕ) : List ℕ := lfpIter fires Mb m (Mb m)

/-- `fires` is monotone in the list of derived codes, as a set. -/
def FiresMono : Prop :=
  ∀ m (R R' : List ℕ) j, (∀ x ∈ R, x ∈ R') → fires m R j = true → fires m R' j = true

variable {fires Mb}

@[simp] theorem lfpIter_zero (m : ℕ) : lfpIter fires Mb m 0 = [] := rfl

theorem lfpIter_succ (m i : ℕ) :
    lfpIter fires Mb m (i + 1) = (List.range (Mb m)).filter (fires m (lfpIter fires Mb m i)) :=
  rfl

theorem mem_lfpIter_succ {m i j : ℕ} :
    j ∈ lfpIter fires Mb m (i + 1) ↔ j < Mb m ∧ fires m (lfpIter fires Mb m i) j = true := by
  simp [lfpIter_succ]

theorem lfpIter_nodup (m i : ℕ) : (lfpIter fires Mb m i).Nodup := by
  cases i with
  | zero => simp
  | succ i => exact (List.nodup_range).filter _

theorem lfpIter_length_le (m i : ℕ) : (lfpIter fires Mb m i).length ≤ Mb m := by
  cases i with
  | zero => simp
  | succ i =>
    rw [lfpIter_succ]
    exact (List.length_filter_le _ _).trans (List.length_range).le

/-- Every derived code satisfies an invariant that the rules preserve. -/
theorem lfpIter_induction (P : ℕ → Prop) {m : ℕ}
    (h : ∀ (R : List ℕ) j, (∀ x ∈ R, P x) → j < Mb m → fires m R j = true → P j) :
    ∀ i, ∀ j ∈ lfpIter fires Mb m i, P j := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    intro j hj
    obtain ⟨hlt, hf⟩ := mem_lfpIter_succ.1 hj
    exact h _ j ih hlt hf

theorem lfpList_induction (P : ℕ → Prop) {m : ℕ}
    (h : ∀ (R : List ℕ) j, (∀ x ∈ R, P x) → j < Mb m → fires m R j = true → P j) :
    ∀ j ∈ lfpList fires Mb m, P j :=
  lfpIter_induction P h _

section Mono

variable (hmono : FiresMono fires)
include hmono

theorem lfpIter_mono_succ {m : ℕ} :
    ∀ i, ∀ x ∈ lfpIter fires Mb m i, x ∈ lfpIter fires Mb m (i + 1) := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    intro x hx
    obtain ⟨hlt, hf⟩ := mem_lfpIter_succ.1 hx
    exact mem_lfpIter_succ.2 ⟨hlt, hmono _ _ _ _ ih hf⟩

/-- Two consecutive iterates with the same members: from then on nothing changes. -/
theorem lfpIter_stable {m i : ℕ}
    (h : ∀ x, x ∈ lfpIter fires Mb m i ↔ x ∈ lfpIter fires Mb m (i + 1)) :
    ∀ k, i ≤ k → ∀ x, x ∈ lfpIter fires Mb m k ↔ x ∈ lfpIter fires Mb m (k + 1) := by
  intro k hk
  induction hk with
  | refl => exact h
  | @step k _ ih =>
    intro x
    rw [mem_lfpIter_succ, mem_lfpIter_succ]
    refine and_congr_right fun _ => ⟨fun hf => hmono _ _ _ _ (fun y hy => (ih y).1 hy) hf,
      fun hf => hmono _ _ _ _ (fun y hy => (ih y).2 hy) hf⟩

theorem lfpIter_progress {m : ℕ} : ∀ i,
    (∃ k < i, ∀ x, x ∈ lfpIter fires Mb m k ↔ x ∈ lfpIter fires Mb m (k + 1)) ∨
      i ≤ (lfpIter fires Mb m i).length := by
  intro i
  induction i with
  | zero => right; simp
  | succ i ih =>
    rcases ih with ⟨k, hk, he⟩ | hlen
    · exact Or.inl ⟨k, by omega, he⟩
    by_cases he : ∀ x, x ∈ lfpIter fires Mb m i ↔ x ∈ lfpIter fires Mb m (i + 1)
    · exact Or.inl ⟨i, by omega, he⟩
    right
    have hsub := lfpIter_mono_succ (Mb := Mb) hmono (m := m) i
    obtain ⟨x, hx⟩ : ∃ x, x ∈ lfpIter fires Mb m (i + 1) ∧ x ∉ lfpIter fires Mb m i := by
      by_contra hc
      simp only [not_exists, not_and, not_not] at hc
      exact he fun x => ⟨hsub x, hc x⟩
    have hnd : (x :: lfpIter fires Mb m i).Nodup :=
      List.nodup_cons.2 ⟨hx.2, lfpIter_nodup m i⟩
    have hs : x :: lfpIter fires Mb m i ⊆ lfpIter fires Mb m (i + 1) := by
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hx.1
      · exact hsub y hy
    have := (hnd.subperm hs).length_le
    simp only [List.length_cons] at this
    omega

/-- After `Mb m` steps the iterates have stabilised. -/
theorem lfpList_stable (m : ℕ) :
    ∀ x, x ∈ lfpList fires Mb m ↔ x ∈ lfpIter fires Mb m (Mb m + 1) := by
  rcases lfpIter_progress hmono (m := m) (Mb m + 1) with ⟨k, hk, he⟩ | hlen
  · exact lfpIter_stable hmono he (Mb m) (by omega)
  · have := lfpIter_length_le (fires := fires) (Mb := Mb) m (Mb m + 1)
    omega

/-- The fixpoint equation: a code is derived iff it is in the universe and some rule
concludes it from derived codes. -/
theorem mem_lfpList_iff {m j : ℕ} :
    j ∈ lfpList fires Mb m ↔ j < Mb m ∧ fires m (lfpList fires Mb m) j = true := by
  rw [lfpList_stable hmono m, mem_lfpIter_succ]
  rfl

/-- Closure: a code of the universe concluded from derived codes is derived. -/
theorem mem_lfpList_of_fires {m j : ℕ} (hj : j < Mb m) {R : List ℕ}
    (hR : ∀ x ∈ R, x ∈ lfpList fires Mb m) (hf : fires m R j = true) :
    j ∈ lfpList fires Mb m :=
  (mem_lfpList_iff hmono).2 ⟨hj, hmono _ _ _ _ hR hf⟩

end Mono

/-! ### Primitive recursion -/

open Primrec

theorem lfpIter_primrec (hf : Primrec fun p : ℕ × List ℕ × ℕ => fires p.1 p.2.1 p.2.2)
    (hM : Primrec Mb) : Primrec₂ (lfpIter fires Mb) := by
  have hg : Primrec₂ fun (m : ℕ) (p : ℕ × List ℕ) =>
      (List.range (Mb m)).filter (fires m p.2) :=
    PR.list_filter (list_range.comp (hM.comp fst))
      (hf.comp ((fst.comp fst).pair ((snd.comp (snd.comp fst)).pair snd)))
  refine (nat_rec (const []) hg).of_eq fun m i => ?_
  induction i with
  | zero => rfl
  | succ i ih => simp only [lfpIter_succ, ← ih]

theorem lfpList_primrec (hf : Primrec fun p : ℕ × List ℕ × ℕ => fires p.1 p.2.1 p.2.2)
    (hM : Primrec Mb) : Primrec (lfpList fires Mb) :=
  (lfpIter_primrec hf hM).comp .id hM

/-- Membership of a primitive recursive query in the fixpoint is primitive recursive. -/
theorem lfpList_mem_primrec (hf : Primrec fun p : ℕ × List ℕ × ℕ => fires p.1 p.2.1 p.2.2)
    (hM : Primrec Mb) {q : ℕ → ℕ} (hq : Primrec q) :
    Primrec fun m => decide (q m ∈ lfpList fires Mb m) :=
  PR.list_mem.comp (lfpList_primrec hf hM) hq

end Fix

end Dsub
