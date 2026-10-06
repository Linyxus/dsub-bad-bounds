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
member carries the two relations of `Rules`: judgments `B ⊆ F × ext F` and
summaries `S ⊆ F × F`.  The rules are those of `Rules`, and one more for judgments, the
kernel rule: `∀(x:T)B₁ <: ∀(x:T)B₂` follows from a judgment `B₁'' <: B₂''` of a member `Γ''`
and a context morphism `f : Γ'' → Γ, x:T` taking `B₁''`, `B₂''` to `B₁`, `B₂`.

The rules are sound for every family.  Saturated facts are complete for the judgments singled
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

/-! ### Soundness of the rules -/

/-- The judgments hold and the summaries pop one level, in every member. -/
def Sound (x : Φ.Facts) : Prop := ∀ i, SoundB (Φ.ctx i) (x i).1 ∧ SoundS (Φ.ctx i) (x i).2

theorem AllRule.sound {x : Φ.Facts} (hx : Sound x) {n : ℕ} {Γ : Ctx n} {P W : Ty n}
    (h : AllRule x Γ P W) : Sub Γ P W := by
  obtain ⟨T, B₁, B₂, rfl, rfl, j, p, hp, f, hf, rfl, rfl⟩ := AllRule.iff.1 h
  exact .all (((hx j).1 p hp).rename hf)

variable (Φ)

/-! ### Completeness -/

/-- The facts are closed under the rules, within the sets of types. -/
structure Saturated (x : Φ.Facts) : Prop where
  S_sub : ∀ i, ∀ p ∈ (x i).2, p.1 ∈ Φ.F i ∧ p.2 ∈ Φ.F i
  closedB : ∀ i, ∀ P ∈ Φ.F i, ∀ W ∈ ext (Φ.F i), FRuleB x i P W → (P, W) ∈ (x i).1
  closedS : ∀ i, ∀ P ∈ Φ.F i, ∀ T ∈ Φ.F i, FRuleS x i P T → (P, T) ∈ (x i).2

variable {Φ}

variable (Φ)

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

/-- Saturated facts hold every good derivable judgment of every member: a judgment
`P <: dN k W` is a chain of `k` summaries followed by a judgment. -/
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

end Family

end Dsub
