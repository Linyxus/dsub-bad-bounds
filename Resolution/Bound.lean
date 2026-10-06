import Resolution.BoundCode
import Mathlib.Combinatorics.Colex
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Tactic.Choose

/-!
Lemma 4 (PROOF.md §4): a state satisfying the invariant either has a collapse or has at
most `Bnd N s n₀` created variables, where `s` bounds the sizes of the types of the created
variables and the numbers of variables of the two terms, and `n₀` the number of base
variables.

The created variables form a forest: the parent of a created variable is its nearest
proper ancestor (`Ann.Par`).  The *label* of a variable is the code of its type with each
base variable replaced by its rank among the base variables and each created one by
`n₀ + dep` (`Ann.lab`): the created variables a type of a created variable mentions are its
ancestors (`ctx_anc`), which `dep` tells apart.  The *class* of a subtree (`Ann.cls`) is its
root's `dep` and label and the set of the classes of its children's subtrees.  Two distinct
siblings of the same class, the second of whose subtree the terms do not mention, give a
collapse: the subtree of the second, mapped into the subtree of the first top-down
(`Ann.twin`).  Otherwise each node has at most `clsBound + 2 s` children, and the forest,
of depth at most `N`, is bounded.
-/

namespace Dsub

namespace Ann

variable {n : ℕ} (a : Ann n)

/-- `w` lies in the subtree of `v`: it is `v` or a descendant of `v`. -/
def Desc (v w : BVar n) : Prop := w = v ∨ a.anc v w

/-- `c` is a created variable with parent `p`: `none` for a root, `some q` for a child of
`q` (an ancestor with no ancestor of `c` in between). -/
def Par : Option (BVar n) → BVar n → Prop
  | none, c => a.cr c ∧ ∀ u, ¬ a.anc u c
  | some q, c => a.anc q c ∧ ∀ u, a.anc q u → ¬ a.anc u c

variable {a}

theorem anc_irrefl {x : BVar n} : ¬ a.anc x x := fun h => lt_irrefl _ (a.anc_dep h)

theorem Desc.refl (v : BVar n) : a.Desc v v := Or.inl rfl

theorem Desc.trans_anc {v w z : BVar n} (h : a.Desc v w) (h' : a.anc w z) : a.anc v z := by
  rcases h with rfl | h
  · exact h'
  · exact a.anc_trans h h'

theorem anc_of_anc_desc {v w z : BVar n} (h : a.anc v w) (h' : a.Desc w z) : a.anc v z := by
  rcases h' with rfl | h'
  · exact h
  · exact a.anc_trans h h'

theorem Desc.cr {v w : BVar n} (hv : a.cr v) (h : a.Desc v w) : a.cr w := by
  rcases h with rfl | h
  · exact hv
  · exact (a.anc_cr h).2

theorem Par.cr {p : Option (BVar n)} {c : BVar n} (h : a.Par p c) : a.cr c := by
  cases p with
  | none => exact h.1
  | some q => exact (a.anc_cr h.1).2

/-- A proper ancestor of a variable is its parent or an ancestor of the parent. -/
theorem Par.anc_of {p : Option (BVar n)} {c y : BVar n} (h : a.Par p c) (hy : a.anc y c) :
    ∃ q, p = some q ∧ a.Desc y q := by
  cases p with
  | none => exact (h.2 y hy).elim
  | some q =>
    refine ⟨q, rfl, ?_⟩
    rcases a.anc_chain hy h.1 with e | e | e
    · exact Or.inl e.symm
    · exact Or.inr e
    · exact (h.2 y e hy).elim

/-- Siblings have the same proper ancestors. -/
theorem Par.anc_sibling {p : Option (BVar n)} {c c' y : BVar n} (h : a.Par p c)
    (h' : a.Par p c') (hy : a.anc y c) : a.anc y c' := by
  obtain ⟨q, rfl, hq⟩ := h.anc_of hy
  exact hq.trans_anc h'.1

/-- No sibling is an ancestor of another. -/
theorem Par.not_anc {p : Option (BVar n)} {c c' : BVar n} (h : a.Par p c) (h' : a.Par p c') :
    ¬ a.anc c c' := by
  intro e
  obtain ⟨q, rfl, hq⟩ := h'.anc_of e
  exact anc_irrefl (hq.trans_anc h.1)

/-- The subtrees of distinct siblings are disjoint. -/
theorem Par.desc_eq {p : Option (BVar n)} {c c' z : BVar n} (h : a.Par p c) (h' : a.Par p c')
    (hz : a.Desc c z) (hz' : a.Desc c' z) : c = c' := by
  rcases hz with e | hz <;> rcases hz' with e' | hz'
  · exact e.symm.trans e'
  · rw [e] at hz'; exact (h'.not_anc h hz').elim
  · rw [e'] at hz; exact (h.not_anc h' hz).elim
  · rcases a.anc_chain hz hz' with e | e | e
    · exact e
    · exact (h.not_anc h' e).elim
    · exact (h'.not_anc h e).elim

/-- Every descendant of `v` lies in the subtree of a child of `v`. -/
theorem exists_child {v w : BVar n} (h : a.anc v w) : ∃ c, a.Par (some v) c ∧ a.Desc c w := by
  classical
  obtain ⟨c, hc, hmin⟩ := Finset.exists_min_image
    (Finset.univ.filter (fun u => a.anc v u ∧ a.Desc u w)) a.dep
    ⟨w, Finset.mem_filter.2 ⟨Finset.mem_univ _, h, Desc.refl w⟩⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
  refine ⟨c, ⟨hc.1, fun u hu huc => ?_⟩, hc.2⟩
  have := hmin u (Finset.mem_filter.2 ⟨Finset.mem_univ _, hu, Or.inr (anc_of_anc_desc huc hc.2)⟩)
  have := a.anc_dep huc
  omega

/-- Every created variable lies in the subtree of a root. -/
theorem exists_root {w : BVar n} (h : a.cr w) : ∃ c, a.Par none c ∧ a.Desc c w := by
  classical
  obtain ⟨c, hc, hmin⟩ := Finset.exists_min_image
    (Finset.univ.filter (fun u => a.cr u ∧ a.Desc u w)) a.dep
    ⟨w, Finset.mem_filter.2 ⟨Finset.mem_univ _, h, Desc.refl w⟩⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
  refine ⟨c, ⟨hc.1, fun u huc => ?_⟩, hc.2⟩
  have := hmin u (Finset.mem_filter.2
    ⟨Finset.mem_univ _, (a.anc_cr huc).1, Or.inr (anc_of_anc_desc huc hc.2)⟩)
  have := a.anc_dep huc
  omega

/-! ### Classes of subtrees -/

variable (a) in
open Classical in
/-- The class of the subtree of `v`, to `k` levels: the `dep` and the label of `v`, and the
set of the classes of the subtrees of its children, to `k - 1` levels (as a sum of powers
of two). -/
noncomputable def cls (lab : BVar n → ℕ) : ℕ → BVar n → ℕ
  | 0, v => Nat.pair (a.dep v) (Nat.pair (lab v) 0)
  | k + 1, v => Nat.pair (a.dep v) (Nat.pair (lab v)
      (∑ i ∈ (Finset.univ.filter (a.Par (some v))).image (cls lab k), 2 ^ i))

/-- Subtrees of the same class, to enough levels: the second maps into the first, keeping
`dep` and labels, the root to the root, and ancestry within the subtree. -/
theorem twin {N : ℕ} (lab : BVar n → ℕ) (hdep : ∀ x, a.cr x → a.dep x ≤ N) :
    ∀ (k : ℕ) (v v' : BVar n), N ≤ a.dep v' + k → a.cls lab k v = a.cls lab k v' →
    ∃ r : BVar n → BVar n, r v' = v ∧
      (∀ w, a.Desc v' w → a.dep (r w) = a.dep w ∧ lab (r w) = lab w ∧ a.Desc v (r w)) ∧
      (∀ w y, a.Desc v' y → a.anc y w → a.anc (r y) (r w)) := by
  intro k
  induction k with
  | zero =>
    intro v v' hk h
    simp only [cls, Nat.pair_eq_pair] at h
    have leaf : ∀ w, ¬ a.anc v' w := fun w hw => by
      have := a.anc_dep hw
      have := hdep w (a.anc_cr hw).2
      omega
    refine ⟨fun _ => v, rfl, fun w hw => ?_, fun w y hy hyw => ?_⟩
    · rcases hw with rfl | hw
      · exact ⟨h.1, h.2.1, Desc.refl v⟩
      · exact (leaf w hw).elim
    · rcases hy with rfl | hy
      · exact (leaf w hyw).elim
      · exact (leaf y hy).elim
  | succ k ih =>
    intro v v' hk h
    classical
    simp only [cls, Nat.pair_eq_pair] at h
    obtain ⟨hd, hl, hs⟩ := h
    have himg := congrArg (fun t => t.bitIndices.toFinset) hs
    simp only [Finset.toFinset_bitIndices_sum_two_pow] at himg
    have hch : ∀ c', a.Par (some v') c' → ∃ c, a.Par (some v) c ∧ ∃ r : BVar n → BVar n,
        r c' = c ∧
        (∀ w, a.Desc c' w → a.dep (r w) = a.dep w ∧ lab (r w) = lab w ∧ a.Desc c (r w)) ∧
        (∀ w y, a.Desc c' y → a.anc y w → a.anc (r y) (r w)) := by
      intro c' hc'
      have hmem : a.cls lab k c' ∈
          (Finset.univ.filter (a.Par (some v))).image (a.cls lab k) := by
        rw [himg]
        exact Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hc'⟩)
      obtain ⟨c, hc, e⟩ := Finset.mem_image.1 hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
      have := a.anc_dep hc'.1
      exact ⟨c, hc, ih c c' (by omega) e⟩
    choose! cf hcf rf hrf using hch
    obtain ⟨r, hrdef⟩ : ∃ r : BVar n → BVar n, ∀ w, r w =
        if w = v' then v
        else if hw : ∃ c', a.Par (some v') c' ∧ a.Desc c' w then rf (Classical.choose hw) w
        else v := ⟨_, fun _ => rfl⟩
    have hr : ∀ c' w, a.Par (some v') c' → a.Desc c' w → r w = rf c' w := by
      intro c' w hc' hw
      have hne : w ≠ v' := by
        intro e
        rw [e] at hw
        exact anc_irrefl (anc_of_anc_desc hc'.1 hw)
      have hex : ∃ c', a.Par (some v') c' ∧ a.Desc c' w := ⟨c', hc', hw⟩
      rw [hrdef, ite_eq_right hne, dite_eq_left hex]
      have := Classical.choose_spec hex
      rw [Par.desc_eq this.1 hc' this.2 hw]
    refine ⟨r, by rw [hrdef, ite_eq_left rfl], fun w hw => ?_, fun w y hy hyw => ?_⟩
    · rcases hw with e | hw
      · rw [hrdef, ite_eq_left e, e]
        exact ⟨hd, hl, Desc.refl v⟩
      · obtain ⟨c', hc', hcw⟩ := exists_child hw
        obtain ⟨e1, e2, e3⟩ := (hrf c' hc').2.1 w hcw
        rw [hr c' w hc' hcw]
        exact ⟨e1, e2, Or.inr (anc_of_anc_desc (hcf c' hc').1 e3)⟩
    · have hw : a.anc v' w := hy.trans_anc hyw
      obtain ⟨c', hc', hcw⟩ := exists_child hw
      obtain ⟨h1, h2, h3⟩ := hrf c' hc'
      rw [hr c' w hc' hcw]
      rcases hy with e | hy
      · rw [hrdef, ite_eq_left e]
        exact anc_of_anc_desc (hcf c' hc').1 (h2 w hcw).2.2
      · have hcy : a.Desc c' y := by
          rcases hcw with e | hcw
          · rw [e] at hyw
            exact (hc'.2 y hy hyw).elim
          · rcases a.anc_chain hyw hcw with e | e | e
            · exact Or.inl e
            · exact (hc'.2 y hy e).elim
            · exact Or.inr e
        rw [hr c' y hc' hcy]
        exact h3 w y hcy hyw

end Ann

/-! ### Labels -/

section

open Classical

variable {n : ℕ}

/-- The index of a variable in the scope of labels: base variables by their rank among the
base variables, created ones after them, by `dep`. -/
noncomputable def Ann.idx (a : Ann n) (n₀ : ℕ) (y : BVar n) : ℕ :=
  if h : a.cr y then n₀ + a.dep y
  else (Fintype.equivFin {x // ¬ a.cr x} ⟨y, h⟩ : ℕ)

/-- The renaming into the scope of labels. -/
noncomputable def Ann.labVar (a : Ann n) (n₀ N : ℕ) : Rename n (n₀ + N + 1) :=
  ⟨fun y => BVar.ofNatD (n₀ + N) (a.idx n₀ y)⟩

/-- The label of a variable: the code of its type in the scope of labels. -/
noncomputable def Ann.lab (a : Ann n) (Γ : Ctx n) (n₀ N : ℕ) (w : BVar n) : ℕ :=
  ((Γ.lookup w).rename (a.labVar n₀ N)).code

/-- The renaming into the scope of labels is injective on the base variables and the
ancestors of any one variable. -/
theorem Ann.labVar_inj {a : Ann n} {n₀ N : ℕ} (hdep : ∀ x, a.cr x → a.dep x ≤ N)
    (hbase : (Finset.univ.filter fun x => ¬ a.cr x).card ≤ n₀) {z x y : BVar n}
    (hx : ¬ a.cr x ∨ a.anc x z) (hy : ¬ a.cr y ∨ a.anc y z)
    (h : (a.labVar n₀ N).var x = (a.labVar n₀ N).var y) : x = y := by
  have hlt : ∀ u (hu : ¬ a.cr u), (Fintype.equivFin {x // ¬ a.cr x} ⟨u, hu⟩ : ℕ) < n₀ := by
    intro u hu
    have h1 := (Fintype.equivFin {x // ¬ a.cr x} ⟨u, hu⟩).isLt
    have h2 : Fintype.card {x // ¬ a.cr x} = (Finset.univ.filter fun x => ¬ a.cr x).card :=
      Fintype.card_subtype _
    omega
  have hb : ∀ u, a.idx n₀ u ≤ n₀ + N := by
    intro u
    unfold Ann.idx
    split_ifs with hu
    · have := hdep u hu; omega
    · have := hlt u hu; omega
  have e := BVar.ofNatD_inj (hb x) (hb y) h
  unfold Ann.idx at e
  by_cases hcx : a.cr x <;> by_cases hcy : a.cr y
  · rw [dite_eq_left hcx, dite_eq_left hcy] at e
    have hd : a.dep x = a.dep y := by omega
    rcases a.anc_chain (hx.resolve_left (not_not.2 hcx)) (hy.resolve_left (not_not.2 hcy))
      with e' | e' | e'
    · exact e'
    · have := a.anc_dep e'; omega
    · have := a.anc_dep e'; omega
  · rw [dite_eq_left hcx, dite_eq_right hcy] at e
    have := hlt y hcy; omega
  · rw [dite_eq_right hcx, dite_eq_left hcy] at e
    have := hlt x hcx; omega
  · rw [dite_eq_right hcx, dite_eq_right hcy] at e
    exact congrArg Subtype.val ((Fintype.equivFin _).injective (Fin.ext e))

theorem Ann.lab_lt {a : Ann n} {Γ : Ctx n} {n₀ N s : ℕ} {w : BVar n}
    (hs : (Γ.lookup w).size ≤ s) : a.lab Γ n₀ N w < codeBound (n₀ + N + 1 + s) := by
  have := Ty.code_lt ((Γ.lookup w).rename (a.labVar n₀ N))
  rw [Ty.size_rename] at this
  exact lt_of_lt_of_le this (codeBound_mono (by omega))

/-! ### Twins give a collapse -/

theorem Ann.collapse_of_twins {N n₀ : ℕ} {Γ : Ctx n} {a : Ann n} {S U : Ty n}
    (hI : Inv N Γ a S U) (hbase : (Finset.univ.filter fun x => ¬ a.cr x).card ≤ n₀)
    {p : Option (BVar n)} {v v' : BVar n} (hv : a.Par p v) (hv' : a.Par p v') (hne : v ≠ v')
    (hcls : a.cls (a.lab Γ n₀ N) N v = a.cls (a.lab Γ n₀ N) N v')
    (hfree : ∀ w, a.Desc v' w → ¬ S.Occ w ∧ ¬ U.Occ w) :
    ∃ X r, Collapse a.cr Γ X r S U := by
  obtain ⟨r, hr0, hr1, hr2⟩ := Ann.twin (a.lab Γ n₀ N) hI.dep_le N v v' (by omega) hcls
  refine ⟨fun w => decide (a.Desc v' w), r, ?_⟩
  have hXc : ∀ w, a.Desc v' w → a.cr w := fun w hw => hw.cr hv'.cr
  have hRX : ∀ y, a.Desc v' y → (retr (fun w => decide (a.Desc v' w)) r).var y = r y :=
    fun y hy => by simp [retr, hy]
  have hRnX : ∀ y, ¬ a.Desc v' y → (retr (fun w => decide (a.Desc v' w)) r).var y = y :=
    fun y hy => by simp [retr, hy]
  constructor
  · exact ⟨v', by simp [Ann.Desc.refl]⟩
  · intro x hx; exact hXc x (by simpa using hx)
  · intro x hx; exact (hfree x (by simpa using hx)).1
  · intro x hx; exact (hfree x (by simpa using hx)).2
  · intro x hx y hy
    by_contra hyX
    have hyX' : a.Desc v' y := by simpa using hyX
    have hx' : a.Desc v' x := Or.inr (hyX'.trans_anc (hI.ctx_anc x y hy (hXc y hyX')))
    simp [hx'] at hx
  · intro w hw
    have hw' : a.Desc v' w := by simpa using hw
    refine ⟨?_, (hr1 w hw').2.2.cr hv.cr⟩
    simpa using fun h => hne (Ann.Par.desc_eq hv hv' (hr1 w hw').2.2 h)
  · intro w hw
    have hw' : a.Desc v' w := by simpa using hw
    set R := retr (fun w => decide (a.Desc v' w)) r
    have good : ∀ y, (Γ.lookup w).Occ y → ¬ a.cr (R.var y) ∨ a.anc (R.var y) (r w) := by
      intro y hy
      by_cases hcy : a.cr y
      · have hyw := hI.ctx_anc w y hy hcy
        by_cases hyX : a.Desc v' y
        · rw [hRX y hyX]
          exact Or.inr (hr2 w y hyX hyw)
        · rw [hRnX y hyX]
          right
          have hyv' : a.anc y v' := by
            rcases hw' with e | hw'
            · rw [e] at hyw; exact hyw
            · rcases a.anc_chain hyw hw' with e | e | e
              · exact (hyX (Or.inl e)).elim
              · exact e
              · exact (hyX (Or.inr e)).elim
          exact Ann.anc_of_anc_desc (Ann.Par.anc_sibling hv' hv hyv') (hr1 w hw').2.2
      · have hyX : ¬ a.Desc v' y := fun h => hcy (hXc y h)
        rw [hRnX y hyX]
        exact Or.inl hcy
    have good2 : ∀ y, (Γ.lookup (r w)).Occ y → ¬ a.cr y ∨ a.anc y (r w) := by
      intro y hy
      by_cases hcy : a.cr y
      · exact Or.inr (hI.ctx_anc _ y hy hcy)
      · exact Or.inl hcy
    have goodAll : ∀ y, ((Γ.lookup (r w)).Occ y ∨ ((Γ.lookup w).rename R).Occ y) →
        ¬ a.cr y ∨ a.anc y (r w) := by
      rintro y (hy | hy)
      · exact good2 y hy
      · obtain ⟨y', rfl, hy'⟩ := Ty.occ_rename.1 hy
        exact good y' hy'
    apply Ty.rename_injOn (f := a.labVar n₀ N)
    · intro x y hx hy e
      exact Ann.labVar_inj hI.dep_le hbase (goodAll x hx) (goodAll y hy) e
    · rw [Ty.rename_comp]
      have : (Γ.lookup w).rename (R.comp (a.labVar n₀ N)) =
          (Γ.lookup w).rename (a.labVar n₀ N) := by
        apply Ty.rename_congr
        intro y _
        simp only [Rename.comp_var]
        by_cases hyX : a.Desc v' y
        · rw [hRX y hyX]
          show BVar.ofNatD _ (a.idx n₀ (r y)) = BVar.ofNatD _ (a.idx n₀ y)
          unfold Ann.idx
          rw [dite_eq_left ((hr1 y hyX).2.2.cr hv.cr), dite_eq_left (hXc y hyX), (hr1 y hyX).1]
        · rw [hRnX y hyX]
      rw [this]
      exact Ty.code_injective (hr1 w hw').2.1

/-! ### Counting -/

/-- `clsStep N L K` bounds `pair d (pair l t)` for `d ≤ N`, `l < L` and `t < 2 ^ K`. -/
def clsStep (N L K : ℕ) : ℕ := (N + (L + 2 ^ K) ^ 2 + 1) ^ 2

/-- `clsBound N L k` bounds the classes to `k` levels. -/
def clsBound (N L : ℕ) : ℕ → ℕ
  | 0 => clsStep N L 0
  | k + 1 => clsStep N L (clsBound N L k)

/-- `treeBound b j` bounds the subtrees of height `≤ j` with branching `≤ b`. -/
def treeBound (b : ℕ) : ℕ → ℕ
  | 0 => 1
  | j + 1 => 1 + b * treeBound b j

/-- The bound of Lemma 4: `b` roots, each a subtree of height `< N`, with branching
`≤ b`, where `b` is the number of classes plus `2 s`. -/
def Bnd (N s n₀ : ℕ) : ℕ :=
  (clsBound N (codeBound (n₀ + N + 1 + s)) N + 2 * s) *
    treeBound (clsBound N (codeBound (n₀ + N + 1 + s)) N + 2 * s) N

theorem pair_pair_lt {N L K d l t : ℕ} (hd : d ≤ N) (hl : l < L) (ht : t < 2 ^ K) :
    Nat.pair d (Nat.pair l t) < clsStep N L K := by
  have h1 := Nat.pair_lt_max_add_one_sq l t
  have h2 : (max l t + 1) ^ 2 ≤ (L + 2 ^ K) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h3 := Nat.pair_lt_max_add_one_sq d (Nat.pair l t)
  have h4 : (max d (Nat.pair l t) + 1) ^ 2 ≤ (N + (L + 2 ^ K) ^ 2 + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  unfold clsStep
  omega

theorem Ann.cls_lt {a : Ann n} {N L : ℕ} (lab : BVar n → ℕ) (hdep : ∀ x, a.cr x → a.dep x ≤ N)
    (hlab : ∀ x, a.cr x → lab x < L) : ∀ k v, a.cr v → a.cls lab k v < clsBound N L k := by
  intro k
  induction k with
  | zero =>
    intro v hv
    exact pair_pair_lt (hdep v hv) (hlab v hv) (by simp)
  | succ k ih =>
    intro v hv
    refine pair_pair_lt (hdep v hv) (hlab v hv) (Nat.geomSum_lt (le_refl 2) ?_)
    intro i hi
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    exact ih c hc.cr

/-- Subtrees of height `≤ j` are bounded. -/
theorem Ann.desc_card {a : Ann n} {N b : ℕ} (hdep : ∀ x, a.cr x → a.dep x ≤ N)
    (hbr : ∀ p, (Finset.univ.filter (a.Par p)).card ≤ b) :
    ∀ j q, N ≤ a.dep q + j → (Finset.univ.filter (a.Desc q)).card ≤ treeBound b j := by
  intro j
  induction j with
  | zero =>
    intro q hq
    have : Finset.univ.filter (a.Desc q) ⊆ {q} := by
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      rcases hw with e | hw
      · simp [e]
      · have := a.anc_dep hw
        have := hdep w (a.anc_cr hw).2
        omega
    exact le_trans (Finset.card_le_card this) (by simp [treeBound])
  | succ j ih =>
    intro q hq
    have hsub : Finset.univ.filter (a.Desc q) ⊆ insert q
        ((Finset.univ.filter (a.Par (some q))).biUnion fun c => Finset.univ.filter (a.Desc c)) := by
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      rw [Finset.mem_insert, Finset.mem_biUnion]
      rcases hw with e | hw
      · exact Or.inl e
      · obtain ⟨c, hc, hcw⟩ := Ann.exists_child hw
        exact Or.inr ⟨c, Finset.mem_filter.2 ⟨Finset.mem_univ _, hc⟩,
          Finset.mem_filter.2 ⟨Finset.mem_univ _, hcw⟩⟩
    have hsum : ∑ c ∈ Finset.univ.filter (a.Par (some q)), (Finset.univ.filter (a.Desc c)).card ≤
        (Finset.univ.filter (a.Par (some q))).card * treeBound b j := by
      have := Finset.sum_le_card_nsmul (Finset.univ.filter (a.Par (some q)))
        (fun c => (Finset.univ.filter (a.Desc c)).card) (treeBound b j) (by
          intro c hc
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
          have := a.anc_dep hc.1
          exact ih c (by omega))
      simpa using this
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_insert_le q
      ((Finset.univ.filter (a.Par (some q))).biUnion fun c => Finset.univ.filter (a.Desc c))
    have h3 := Finset.card_biUnion_le (s := Finset.univ.filter (a.Par (some q)))
      (t := fun c => Finset.univ.filter (a.Desc c))
    have h4 := Nat.mul_le_mul_right (treeBound b j) (hbr (some q))
    simp only [treeBound]
    omega

/-- Without a collapse, every node has boundedly many children. -/
theorem Ann.branch {N s n₀ : ℕ} {Γ : Ctx n} {a : Ann n} {S U : Ty n} (hI : Inv N Γ a S U)
    (hsize : ∀ x, a.cr x → (Γ.lookup x).size ≤ s)
    (hS : (Finset.univ.filter fun x => S.Occ x).card ≤ s)
    (hU : (Finset.univ.filter fun x => U.Occ x).card ≤ s)
    (hbase : (Finset.univ.filter fun x => ¬ a.cr x).card ≤ n₀)
    (hnc : ¬ ∃ X r, Collapse a.cr Γ X r S U) (p : Option (BVar n)) :
    (Finset.univ.filter (a.Par p)).card ≤
      clsBound N (codeBound (n₀ + N + 1 + s)) N + 2 * s := by
  set C := Finset.univ.filter (a.Par p)
  let M : BVar n → Prop := fun c => ∃ x, a.Desc c x ∧ (S.Occ x ∨ U.Occ x)
  have hsplit := Finset.card_filter_add_card_filter_not (s := C) M
  have hmarked : (C.filter M).card ≤ 2 * s := by
    have hm : (Finset.univ.filter fun x => S.Occ x ∨ U.Occ x).card ≤ 2 * s := by
      rw [Finset.filter_or]
      have hS' : (Finset.univ.filter S.Occ).card ≤ s := hS
      have hU' : (Finset.univ.filter U.Occ).card ≤ s := hU
      have := Finset.card_union_le (Finset.univ.filter S.Occ) (Finset.univ.filter U.Occ)
      omega
    refine le_trans (Finset.card_le_card_of_injOn
      (fun c => if h : M c then Classical.choose h else c) ?_ ?_) hm
    · intro c hc
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, C, Finset.mem_filter,
        Finset.mem_univ, true_and] at hc
      simp only [dite_eq_left hc.2, Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and]
      exact (Classical.choose_spec hc.2).2
    · intro c hc c' hc' e
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, C, Finset.mem_filter,
        Finset.mem_univ, true_and] at hc hc'
      simp only [dite_eq_left hc.2, dite_eq_left hc'.2] at e
      have h1 := (Classical.choose_spec hc.2).1
      have h2 := (Classical.choose_spec hc'.2).1
      rw [e] at h1
      exact Ann.Par.desc_eq hc.1 hc'.1 h1 h2
  have hfree : (C.filter fun c => ¬ M c).card ≤ clsBound N (codeBound (n₀ + N + 1 + s)) N := by
    have hlt := Ann.cls_lt (a := a) (L := codeBound (n₀ + N + 1 + s)) (a.lab Γ n₀ N) hI.dep_le
      (fun x hx => Ann.lab_lt (hsize x hx))
    refine le_trans (Finset.card_le_card_of_injOn (a.cls (a.lab Γ n₀ N) N) ?_ ?_)
      (le_of_eq (Finset.card_range _))
    · intro c hc
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, C, Finset.mem_filter,
        Finset.mem_univ, true_and] at hc
      simp only [Finset.coe_range, Set.mem_Iio]
      exact hlt N c hc.1.cr
    · intro c hc c' hc' e
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, C, Finset.mem_filter,
        Finset.mem_univ, true_and] at hc hc'
      by_contra hne
      exact hnc (Ann.collapse_of_twins hI hbase hc.1 hc'.1 hne e
        (fun w hw => ⟨fun h => hc'.2 ⟨w, hw, Or.inl h⟩, fun h => hc'.2 ⟨w, hw, Or.inr h⟩⟩))
  omega

/-- Lemma 4: a state satisfying the invariant has at most `Bnd N s n₀` created variables or a
collapse. -/
theorem bound_or_collapse {n N s n₀ : ℕ} {Γ : Ctx n} {a : Ann n} {S U : Ty n}
    (hI : Inv N Γ a S U)
    (hsize : ∀ x, a.cr x → (Γ.lookup x).size ≤ s)
    (hS : (Finset.univ.filter fun x => S.Occ x).card ≤ s)
    (hU : (Finset.univ.filter fun x => U.Occ x).card ≤ s)
    (hbase : (Finset.univ.filter fun x => ¬ a.cr x).card ≤ n₀) :
    (Finset.univ.filter fun x => a.cr x).card ≤ Bnd N s n₀ ∨ ∃ X r, Collapse a.cr Γ X r S U := by
  by_cases hnc : ∃ X r, Collapse a.cr Γ X r S U
  · exact Or.inr hnc
  left
  have hbr := Ann.branch hI hsize hS hU hbase hnc
  set b := clsBound N (codeBound (n₀ + N + 1 + s)) N + 2 * s
  have hsub : (Finset.univ.filter fun x => a.cr x) ⊆
      (Finset.univ.filter (a.Par none)).biUnion fun c => Finset.univ.filter (a.Desc c) := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    obtain ⟨c, hc, hcw⟩ := Ann.exists_root hw
    exact Finset.mem_biUnion.2 ⟨c, Finset.mem_filter.2 ⟨Finset.mem_univ _, hc⟩,
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hcw⟩⟩
  have hsum : ∑ c ∈ Finset.univ.filter (a.Par none), (Finset.univ.filter (a.Desc c)).card ≤
      (Finset.univ.filter (a.Par none)).card * treeBound b N := by
    have := Finset.sum_le_card_nsmul (Finset.univ.filter (a.Par none))
      (fun c => (Finset.univ.filter (a.Desc c)).card) (treeBound b N)
      (fun c _ => Ann.desc_card hI.dep_le hbr N c (by omega))
    simpa using this
  have h1 := Finset.card_le_card hsub
  have h3 := Finset.card_biUnion_le (s := Finset.univ.filter (a.Par none))
    (t := fun c => Finset.univ.filter (a.Desc c))
  have h4 := Nat.mul_le_mul_right (treeBound b N) (hbr none)
  show _ ≤ b * treeBound b N
  omega

end

end Dsub
