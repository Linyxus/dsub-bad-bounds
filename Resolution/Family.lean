import Resolution.Thin
import Resolution.Height
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
Saturation over a finite family of contexts, with the `∀` rule.

A family is a finite list of members, each a context `Γ` over some scope together with a
finite set `F` of types over it (closed under the parts of declarations, holding `⊤`, `⊥` and
the types of all variables; `∀` types are allowed, their bodies need not be in `F`).  Each
member carries the two relations of `Resolution/Decide.lean`: judgments `B ⊆ F × ext F` and
summaries `S ⊆ F × F`.  The rules are those of `Decide.lean`, and one more for judgments, the
kernel rule: `∀(x:T)B₁ <: ∀(x:T)B₂` follows from a judgment `B₁'' <: B₂''` of a member `Γ''`
and a context morphism `f : Γ'' → Γ, x:T` taking `B₁''`, `B₂''` to `B₁`, `B₂`.

Saturation from nothing is sound for every family.  It is complete for the judgments singled
out by a predicate `Good` subject to the conditions `Norm`: good judgments only have good
premises, and every good `∀` step is matched by a judgment of a member, of no greater height.
-/

namespace Dsub

/-! ### Finitely many renamings -/

instance Rename.fintype (n m : ℕ) : Fintype (Rename n m) :=
  Fintype.ofEquiv (BVar n → BVar m)
    { toFun := fun g => ⟨g⟩, invFun := fun f => f.var, left_inv := fun _ => rfl,
      right_inv := fun _ => rfl }

instance Rename.decidableIsCtxMorph {n m : ℕ} (f : Rename n m) (Γ : Ctx n) (Δ : Ctx m) :
    Decidable (f.IsCtxMorph Γ Δ) := by
  unfold Rename.IsCtxMorph; infer_instance

/-! ### Families -/

/-- A finite family of contexts, each with a finite set of types over it. -/
structure Family where
  size : ℕ
  dim : Fin size → ℕ
  ctx : (i : Fin size) → Ctx (dim i)
  F : (i : Fin size) → Finset (Ty (dim i))

namespace Family

variable (Φ : Family)

/-- What the sets of types must hold. -/
structure WF : Prop where
  top_mem : ∀ i, Ty.top ∈ Φ.F i
  bot_mem : ∀ i, Ty.bot ∈ Φ.F i
  lookup_mem : ∀ i x, (Φ.ctx i).lookup x ∈ Φ.F i
  closed : ∀ i L H, Ty.bnd L H ∈ Φ.F i → L ∈ Φ.F i ∧ H ∈ Φ.F i

/-- For each member, judgments (`.1`) and summaries (`.2`). -/
abbrev Facts : Type :=
  (i : Fin Φ.size) → Finset (Ty (Φ.dim i) × Ty (Φ.dim i)) × Finset (Ty (Φ.dim i) × Ty (Φ.dim i))

variable {Φ}

/-- Pointwise inclusion of facts. -/
def Le (x y : Φ.Facts) : Prop := ∀ i, (x i).1 ⊆ (y i).1 ∧ (x i).2 ⊆ (y i).2

/-! ### The rules -/

/-- The kernel rule: `∀(x:T)B₁ <: ∀(x:T)B₂` in `Γ` from a judgment of some member mapped into
`Γ, x:T` by a context morphism. -/
def AllRule (x : Φ.Facts) {n : ℕ} (Γ : Ctx n) : Ty n → Ty n → Prop
  | .all T₁ B₁, .all T₂ B₂ => T₁ = T₂ ∧ ∃ j, ∃ p ∈ (x j).1, ∃ f : Rename (Φ.dim j) (n + 1),
      f.IsCtxMorph (Φ.ctx j) (Γ.push T₁) ∧ p.1.rename f = B₁ ∧ p.2.rename f = B₂
  | _, _ => False

instance (x : Φ.Facts) {n : ℕ} (Γ : Ctx n) (P W : Ty n) : Decidable (AllRule x Γ P W) := by
  cases P <;> cases W <;> simp only [AllRule] <;> infer_instance

theorem AllRule.iff {x : Φ.Facts} {n : ℕ} {Γ : Ctx n} {P W : Ty n} :
    AllRule x Γ P W ↔ ∃ T B₁ B₂, P = .all T B₁ ∧ W = .all T B₂ ∧
      ∃ j, ∃ p ∈ (x j).1, ∃ f : Rename (Φ.dim j) (n + 1),
        f.IsCtxMorph (Φ.ctx j) (Γ.push T) ∧ p.1.rename f = B₁ ∧ p.2.rename f = B₂ := by
  cases P <;> cases W <;> simp only [AllRule, reduceCtorEq, false_and, exists_false,
    and_false, Ty.all.injEq]
  constructor
  · rintro ⟨rfl, h⟩; exact ⟨_, _, _, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, h⟩
  · rintro ⟨_, _, _, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, h⟩; exact ⟨rfl, h⟩

theorem AllRule.mono {x y : Φ.Facts} (hxy : Le x y) {n : ℕ} {Γ : Ctx n} {P W : Ty n}
    (h : AllRule x Γ P W) : AllRule y Γ P W := by
  obtain ⟨T, B₁, B₂, rfl, rfl, j, p, hp, f, hf, e₁, e₂⟩ := AllRule.iff.1 h
  exact AllRule.iff.2 ⟨T, B₁, B₂, rfl, rfl, j, p, (hxy j).1 hp, f, hf, e₁, e₂⟩

/-- When the judgment `P <: W` of member `i` follows from the facts. -/
def FRuleB (x : Φ.Facts) (i : Fin Φ.size) (P W : Ty (Φ.dim i)) : Prop :=
  RuleB (Φ.ctx i) (Φ.F i) (x i).1 (x i).2 P W ∨ AllRule x (Φ.ctx i) P W

/-- When the summary `(P, T)` of member `i` follows from the facts. -/
def FRuleS (x : Φ.Facts) (i : Fin Φ.size) (P T : Ty (Φ.dim i)) : Prop :=
  RuleS (Φ.ctx i) (Φ.F i) (x i).1 (x i).2 P T

instance (x : Φ.Facts) (i : Fin Φ.size) (P W : Ty (Φ.dim i)) : Decidable (FRuleB x i P W) := by
  unfold FRuleB; infer_instance

instance (x : Φ.Facts) (i : Fin Φ.size) (P T : Ty (Φ.dim i)) : Decidable (FRuleS x i P T) := by
  unfold FRuleS; infer_instance

theorem FRuleB.mono {x y : Φ.Facts} (hxy : Le x y) {i : Fin Φ.size} {P W : Ty (Φ.dim i)}
    (h : FRuleB x i P W) : FRuleB y i P W :=
  h.imp (RuleB.mono (hxy i).1 (hxy i).2) (AllRule.mono hxy)

theorem FRuleS.mono {x y : Φ.Facts} (hxy : Le x y) {i : Fin Φ.size} {P T : Ty (Φ.dim i)}
    (h : FRuleS x i P T) : FRuleS y i P T :=
  RuleS.mono (hxy i).1 (hxy i).2 h

/-! ### Soundness of the rules -/

/-- The judgments hold and the summaries pop one level, in every member. -/
def Sound (x : Φ.Facts) : Prop := ∀ i, SoundB (Φ.ctx i) (x i).1 ∧ SoundS (Φ.ctx i) (x i).2

theorem AllRule.sound {x : Φ.Facts} (hx : Sound x) {n : ℕ} {Γ : Ctx n} {P W : Ty n}
    (h : AllRule x Γ P W) : Sub Γ P W := by
  obtain ⟨T, B₁, B₂, rfl, rfl, j, p, hp, f, hf, rfl, rfl⟩ := AllRule.iff.1 h
  exact .all (((hx j).1 p hp).rename hf)

theorem FRuleB.sound {x : Φ.Facts} (hx : Sound x) {i : Fin Φ.size} {P W : Ty (Φ.dim i)}
    (h : FRuleB x i P W) : Sub (Φ.ctx i) P W :=
  h.elim (RuleB.sound (hx i).1 (hx i).2) (AllRule.sound hx)

theorem FRuleS.sound {x : Φ.Facts} (hx : Sound x) {i : Fin Φ.size} {P T : Ty (Φ.dim i)}
    (h : FRuleS x i P T) :
    ∀ k W, Sub (Φ.ctx i) T (Ty.dN k W) → Sub (Φ.ctx i) P (Ty.dN (k + 1) W) :=
  RuleS.sound (hx i).1 (hx i).2 h

/-! ### Saturation by iteration -/

variable (Φ)

/-- One round of saturation over all members. -/
def step (x : Φ.Facts) : Φ.Facts := fun i =>
  ((Φ.F i ×ˢ ext (Φ.F i)).filter (fun p => FRuleB x i p.1 p.2),
   (Φ.F i ×ˢ Φ.F i).filter (fun p => FRuleS x i p.1 p.2))

/-- `i` rounds of saturation from nothing. -/
def iter : ℕ → Φ.Facts
  | 0 => fun _ => (∅, ∅)
  | i + 1 => Φ.step (iter i)

/-- The number of facts. -/
def count (x : Φ.Facts) : ℕ := ∑ i, ((x i).1.card + (x i).2.card)

/-- The number of possible facts: the most rounds saturation can take. -/
def bound : ℕ := ∑ i, Dsub.bound (Φ.F i)

variable {Φ}

theorem step_mono {x y : Φ.Facts} (h : Le x y) : Le (Φ.step x) (Φ.step y) := by
  intro i
  constructor
  · intro p hp
    simp only [step, Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.mono h⟩
  · intro p hp
    simp only [step, Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.mono h⟩

theorem iter_mono : ∀ i : ℕ, Le (Φ.iter i) (Φ.iter (i + 1))
  | 0 => fun _ => ⟨Finset.empty_subset _, Finset.empty_subset _⟩
  | i + 1 => step_mono (iter_mono i)

theorem size_step_le (x : Φ.Facts) : Φ.count (Φ.step x) ≤ Φ.bound := by
  simp only [count, step, bound, Dsub.bound]
  exact Finset.sum_le_sum fun i _ => Nat.add_le_add
    (Finset.card_le_card (Finset.filter_subset _ _))
    (Finset.card_le_card (Finset.filter_subset _ _))

theorem size_lt_of_le {x y : Φ.Facts} (hle : Le x y) (hne : x ≠ y) : Φ.count x < Φ.count y := by
  have hi : ∃ i, x i ≠ y i := by
    by_contra hc
    push Not at hc
    exact hne (funext hc)
  obtain ⟨i, hi⟩ := hi
  apply Finset.sum_lt_sum
  · intro j _
    exact Nat.add_le_add (Finset.card_le_card (hle j).1) (Finset.card_le_card (hle j).2)
  · refine ⟨i, Finset.mem_univ _, ?_⟩
    obtain ⟨m1, m2⟩ := hle i
    by_cases e1 : (x i).1 = (y i).1
    · have e2 : (x i).2 ≠ (y i).2 := fun e2 => hi (Prod.ext e1 e2)
      have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨m2, e2⟩)
      rw [e1]; omega
    · have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨m1, e1⟩)
      have := Finset.card_le_card m2
      omega

theorem iter_progress : ∀ i, Φ.iter i = Φ.iter (i + 1) ∨ i + 1 ≤ Φ.count (Φ.iter (i + 1))
  | 0 => by
    by_cases e : Φ.iter 0 = Φ.iter 1
    · exact Or.inl e
    · have := size_lt_of_le (iter_mono 0) e
      exact Or.inr (by omega)
  | i + 1 => by
    by_cases e : Φ.iter (i + 1) = Φ.iter (i + 2)
    · exact Or.inl e
    · have hlt := size_lt_of_le (iter_mono (i + 1)) e
      rcases iter_progress i with e' | h
      · exact absurd (show Φ.iter (i + 1) = Φ.iter (i + 2) from
          show Φ.step (Φ.iter i) = Φ.step (Φ.iter (i + 1)) by rw [← e']) e
      · exact Or.inr (by omega)

theorem iter_fixed : Φ.step (Φ.iter Φ.bound) = Φ.iter Φ.bound := by
  rcases iter_progress (Φ := Φ) Φ.bound with e | h
  · exact e.symm
  · have := size_step_le (Φ.iter Φ.bound)
    rw [show Φ.iter (Φ.bound + 1) = Φ.step (Φ.iter Φ.bound) from rfl] at h
    omega

theorem iter_sound : ∀ i, Sound (Φ.iter i)
  | 0 => fun _ => ⟨fun _ h => by simp [iter] at h, fun _ h => by simp [iter] at h⟩
  | i + 1 => by
    have hx := iter_sound i
    intro j
    constructor
    · intro p hp
      simp only [iter, step, Finset.mem_filter] at hp
      exact hp.2.sound hx
    · intro p hp
      simp only [iter, step, Finset.mem_filter] at hp
      exact hp.2.sound hx

variable (Φ)

/-- Saturation that stops at a fixed point, with at most `k` more rounds. -/
def saturate : ℕ → Φ.Facts → Φ.Facts
  | 0, x => x
  | k + 1, x => if Φ.step x = x then x else saturate k (Φ.step x)

/-- The saturated facts: saturation from nothing, for at most `bound` rounds. -/
def facts : Φ.Facts := Φ.saturate Φ.bound (Φ.iter 0)

variable {Φ}

theorem saturate_iter : ∀ k i, ∃ j,
    Φ.saturate k (Φ.iter i) = Φ.iter j ∧ (Φ.step (Φ.iter j) = Φ.iter j ∨ j = i + k)
  | 0, i => ⟨i, rfl, Or.inr rfl⟩
  | k + 1, i => by
    by_cases e : Φ.step (Φ.iter i) = Φ.iter i
    · exact ⟨i, by simp only [saturate, e, ite_true], Or.inl e⟩
    · obtain ⟨j, h1, h2⟩ := saturate_iter k (i + 1)
      refine ⟨j, ?_, ?_⟩
      · simp only [saturate, e, ite_false]; exact h1
      · rcases h2 with h2 | h2
        · exact Or.inl h2
        · exact Or.inr (by omega)

variable (Φ)

/-- Saturation from nothing reaches a fixed point, which is an iterate. -/
theorem facts_spec : ∃ j, Φ.facts = Φ.iter j ∧ Φ.step (Φ.iter j) = Φ.iter j := by
  obtain ⟨j, h1, h2⟩ := saturate_iter (Φ := Φ) Φ.bound 0
  refine ⟨j, h1, ?_⟩
  rcases h2 with h2 | h2
  · exact h2
  · rw [h2, Nat.zero_add]; exact iter_fixed

theorem facts_sound : Sound Φ.facts := by
  obtain ⟨j, e, -⟩ := Φ.facts_spec
  rw [e]; exact iter_sound j

/-- Decides the judgment `P <: U` of member `i`: is it a saturated fact? -/
def famDecide (i : Fin Φ.size) (P U : Ty (Φ.dim i)) : Bool :=
  decide ((P, U) ∈ (Φ.facts i).1)

theorem famDecide_sound {i : Fin Φ.size} {P U : Ty (Φ.dim i)} (h : Φ.famDecide i P U = true) :
    Sub (Φ.ctx i) P U :=
  (Φ.facts_sound i).1 _ (of_decide_eq_true h)

/-! ### Completeness -/

/-- The facts are closed under the rules, within the sets of types. -/
structure Saturated (x : Φ.Facts) : Prop where
  S_sub : ∀ i, ∀ p ∈ (x i).2, p.1 ∈ Φ.F i ∧ p.2 ∈ Φ.F i
  closedB : ∀ i, ∀ P ∈ Φ.F i, ∀ W ∈ ext (Φ.F i), FRuleB x i P W → (P, W) ∈ (x i).1
  closedS : ∀ i, ∀ P ∈ Φ.F i, ∀ T ∈ Φ.F i, FRuleS x i P T → (P, T) ∈ (x i).2

variable {Φ}

theorem saturated_of_fixed {x : Φ.Facts} (fix : Φ.step x = x) : Φ.Saturated x where
  S_sub i p hp := by
    rw [← fix] at hp
    simp only [step, Finset.mem_filter, Finset.mem_product] at hp
    exact hp.1
  closedB i P hP W hW hr := by
    rw [← fix]
    simp only [step, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hP, hW⟩, hr⟩
  closedS i P hP T hT hr := by
    rw [← fix]
    simp only [step, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hP, hT⟩, hr⟩

variable (Φ)

theorem facts_saturated : Φ.Saturated Φ.facts := by
  obtain ⟨j, e, fix⟩ := Φ.facts_spec
  rw [e]; exact saturated_of_fixed fix

/-- What completeness needs of a predicate `Good` on the judgments `Γᵢ ⊢ P <: Q` of the
members: the premises of the rules other than `∀` at a good judgment are good, and a good `∀`
step (the conclusion's two types in `F`), with a premise of height `h`, is matched by a good
judgment of some member, of height `h`, with its types in that member's `F` and `ext F`,
and mapped onto the premise by a context morphism. -/
structure Norm (Good : (i : Fin Φ.size) → Ty (Φ.dim i) → Ty (Φ.dim i) → Prop) : Prop where
  bnd : ∀ i S₁ U₁ S₂ U₂, Good i (.bnd S₁ U₁) (.bnd S₂ U₂) → Good i S₂ S₁ ∧ Good i U₁ U₂
  sel_lower : ∀ i S x, Good i S (.sel x) → Good i ((Φ.ctx i).lookup x) (.bnd S .top)
  sel_upper : ∀ i x U, Good i (.sel x) U → Good i ((Φ.ctx i).lookup x) (.bnd .bot U)
  bad_bounds : ∀ i S U x, Good i S U →
    Good i ((Φ.ctx i).lookup x) (.bnd S .top) ∧ Good i ((Φ.ctx i).lookup x) (.bnd .bot U)
  all : ∀ i T B₁ B₂ h, Ty.all T B₁ ∈ Φ.F i → Ty.all T B₂ ∈ Φ.F i →
    Good i (.all T B₁) (.all T B₂) → SubH h ((Φ.ctx i).push T) B₁ B₂ →
    ∃ j, ∃ B₁'' B₂'' : Ty (Φ.dim j), ∃ f : Rename (Φ.dim j) (Φ.dim i + 1),
      f.IsCtxMorph (Φ.ctx j) ((Φ.ctx i).push T) ∧ B₁''.rename f = B₁ ∧ B₂''.rename f = B₂ ∧
      B₁'' ∈ Φ.F j ∧ B₂'' ∈ ext (Φ.F j) ∧ SubH h (Φ.ctx j) B₁'' B₂'' ∧ Good j B₁'' B₂''

variable {Φ}

theorem WF.ext_closed (hw : Φ.WF) {i : Fin Φ.size} {L H : Ty (Φ.dim i)}
    (h : Ty.bnd L H ∈ ext (Φ.F i)) : L ∈ Φ.F i ∧ H ∈ Φ.F i := by
  rcases Finset.mem_union.1 h with h | h
  · exact hw.closed i L H h
  · obtain ⟨P, hP, e⟩ := Finset.mem_image.1 h
    simp only [Ty.bnd.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨hP, hw.top_mem i⟩

theorem all_mem_of_mem_ext {n : ℕ} {F : Finset (Ty n)} {T : Ty n} {B : Ty (n + 1)}
    (h : Ty.all T B ∈ ext F) : Ty.all T B ∈ F := by
  rcases Finset.mem_union.1 h with h | h
  · exact h
  · obtain ⟨P, -, e⟩ := Finset.mem_image.1 h
    cases e

theorem Saturated.chain_bot {x : Φ.Facts} (hw : Φ.WF) (hs : Φ.Saturated x) (i : Fin Φ.size) :
    ∀ k, Chain (x i).2 k .bot .bot
  | 0 => .zero _
  | k + 1 => .succ (hs.closedS i _ (hw.bot_mem i) _ (hw.bot_mem i) (Or.inr (Or.inl ⟨rfl, rfl⟩)))
      (hs.chain_bot hw i k)

/-- Saturated facts hold every good derivable judgment of every member, in the form of
`Sub.complete`: a judgment `P <: dN k W` is a chain of `k` summaries followed by a judgment. -/
theorem Saturated.complete {Good : (i : Fin Φ.size) → Ty (Φ.dim i) → Ty (Φ.dim i) → Prop}
    (hN : Φ.Norm Good) (hw : Φ.WF) {x : Φ.Facts} (hs : Φ.Saturated x) :
    ∀ h i P Q, SubH h (Φ.ctx i) P Q → Good i P Q → P ∈ Φ.F i →
      ∀ k W, W ∈ ext (Φ.F i) → Q = Ty.dN k W → ∃ R, Chain (x i).2 k P R ∧ (R, W) ∈ (x i).1 := by
  intro h
  induction h using Nat.strong_induction_on with
  | _ h ih =>
  intro i P Q D hg hP k W hW e
  cases D with
  | top =>
    cases k with
    | zero =>
      subst e
      exact ⟨_, .zero _, hs.closedB i _ hP _ hW (Or.inl (Or.inl rfl))⟩
    | succ k => simp at e
  | bot =>
    exact ⟨_, hs.chain_bot hw i k, hs.closedB i _ hP _ hW (Or.inl (Or.inr (Or.inl rfl)))⟩
  | refl_sel =>
    cases k with
    | zero =>
      subst e
      exact ⟨_, .zero _, hs.closedB i _ hP _ hW
        (Or.inl (Or.inr (Or.inr (Or.inl ⟨_, BVar.mem_list _, rfl, rfl⟩))))⟩
    | succ k => simp at e
  | @bnd _ h' _ S₁ U₁ S₂ U₂ D₁ D₂ =>
    have ih' := ih h' (Nat.lt_succ_self _)
    obtain ⟨hS₁, hU₁⟩ := hw.closed i _ _ hP
    obtain ⟨g₁, g₂⟩ := hN.bnd i _ _ _ _ hg
    cases k with
    | zero =>
      subst e
      obtain ⟨hS₂, hU₂⟩ := hw.ext_closed hW
      obtain ⟨R₁, c₁, h₁⟩ := ih' i _ _ D₁ g₁ hS₂ 0 S₁ (mem_ext_of_mem hS₁) rfl
      obtain ⟨R₂, c₂, h₂⟩ := ih' i _ _ D₂ g₂ hU₁ 0 U₂ (mem_ext_of_mem hU₂) rfl
      cases c₁; cases c₂
      exact ⟨_, .zero _, hs.closedB i _ hP _ hW (Or.inl (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨h₁, h₂⟩)))))⟩
    | succ k =>
      simp only [Ty.dN_succ, Ty.bnd.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      obtain ⟨R, c, hR⟩ := ih' i _ _ D₂ g₂ hU₁ k W hW rfl
      exact ⟨R, .succ (hs.closedS i _ hP _ hU₁ (Or.inl ⟨S₁, hS₁, rfl⟩)) c, hR⟩
  | @all _ h' _ T B₁ B₂ D' =>
    cases k with
    | zero =>
      subst e
      have hW' := all_mem_of_mem_ext hW
      obtain ⟨j, B₁'', B₂'', f, hf, e₁, e₂, m₁, m₂, D'', g''⟩ :=
        hN.all i T B₁ B₂ h' hP hW' hg D'
      obtain ⟨R, c, hR⟩ := ih h' (Nat.lt_succ_self _) j _ _ D'' g'' m₁ 0 B₂'' m₂ rfl
      cases c
      exact ⟨_, .zero _, hs.closedB i _ hP _ hW
        (Or.inr (AllRule.iff.2 ⟨T, B₁, B₂, rfl, rfl, j, _, hR, f, hf, e₁, e₂⟩))⟩
    | succ k => simp at e
  | @sel_lower _ h' _ _ y D' =>
    have g := hN.sel_lower i _ _ hg
    cases k with
    | zero =>
      subst e
      obtain ⟨R, c, hR⟩ := ih h' (Nat.lt_succ_self _) i _ _ D' g (hw.lookup_mem i y) 0 _
        (bnd_top_mem_ext hP) rfl
      cases c
      exact ⟨_, .zero _, hs.closedB i _ hP _ hW
        (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨y, BVar.mem_list y, rfl, hR⟩))))))⟩
    | succ k => simp at e
  | @sel_upper _ h' _ _ y D' =>
    have g := hN.sel_upper i _ _ hg
    subst e
    obtain ⟨R, c, hR⟩ := ih h' (Nat.lt_succ_self _) i _ _ D' g (hw.lookup_mem i y) (k + 1) W
      hW rfl
    obtain _ | ⟨h₁, c⟩ := c
    have hR₁ := (hs.S_sub i _ h₁).2
    cases k with
    | zero =>
      cases c
      exact ⟨_, .zero _, hs.closedB i _ hP _ hW (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl ⟨y, BVar.mem_list y, rfl, _, hR₁, h₁, hR⟩)))))))⟩
    | succ k =>
      obtain _ | ⟨h₂, c⟩ := c
      have hR₂ := (hs.S_sub i _ h₂).2
      exact ⟨_, .succ (hs.closedS i _ hP _ hR₂
        (Or.inr (Or.inr (Or.inl ⟨y, BVar.mem_list y, rfl, _, hR₁, h₁, h₂⟩)))) c, hR⟩
  | @bad_bounds _ h' _ _ _ y D₁ D₂ =>
    obtain ⟨g₁, g₂⟩ := hN.bad_bounds i _ _ y hg
    have ih' := ih h' (Nat.lt_succ_self _)
    subst e
    obtain ⟨R₀, c₀, h₀⟩ := ih' i _ _ D₁ g₁ (hw.lookup_mem i y) 0 _ (bnd_top_mem_ext hP) rfl
    cases c₀
    obtain ⟨R, c, hR⟩ := ih' i _ _ D₂ g₂ (hw.lookup_mem i y) (k + 1) W hW rfl
    obtain _ | ⟨h₁, c⟩ := c
    have hR₁ := (hs.S_sub i _ h₁).2
    cases k with
    | zero =>
      cases c
      exact ⟨_, .zero _, hs.closedB i _ hP _ hW (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr ⟨y, BVar.mem_list y, h₀, _, hR₁, h₁, hR⟩)))))))⟩
    | succ k =>
      obtain _ | ⟨h₂, c⟩ := c
      have hR₂ := (hs.S_sub i _ h₂).2
      exact ⟨_, .succ (hs.closedS i _ hP _ hR₂
        (Or.inr (Or.inr (Or.inr ⟨y, BVar.mem_list y, h₀, _, hR₁, h₁, h₂⟩)))) c, hR⟩

/-- The decision is complete on good judgments with their types in the member's sets. -/
theorem famDecide_complete {Good : (i : Fin Φ.size) → Ty (Φ.dim i) → Ty (Φ.dim i) → Prop}
    (hN : Φ.Norm Good) (hw : Φ.WF) {i : Fin Φ.size} {P U : Ty (Φ.dim i)} (hg : Good i P U)
    (hP : P ∈ Φ.F i) (hU : U ∈ ext (Φ.F i)) (D : Sub (Φ.ctx i) P U) :
    Φ.famDecide i P U = true := by
  obtain ⟨h, D⟩ := D.subH
  obtain ⟨R, c, hR⟩ := Φ.facts_saturated.complete hN hw h i P U D hg hP 0 U hU rfl
  cases c
  exact decide_eq_true hR

theorem famDecide_iff {Good : (i : Fin Φ.size) → Ty (Φ.dim i) → Ty (Φ.dim i) → Prop}
    (hN : Φ.Norm Good) (hw : Φ.WF) {i : Fin Φ.size} {P U : Ty (Φ.dim i)} (hg : Good i P U)
    (hP : P ∈ Φ.F i) (hU : U ∈ ext (Φ.F i)) :
    Φ.famDecide i P U = true ↔ Sub (Φ.ctx i) P U :=
  ⟨famDecide_sound Φ, famDecide_complete hN hw hg hP hU⟩

end Family

end Dsub
