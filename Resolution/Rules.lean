import Resolution.Lemmas
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union

/-!
The rules of saturation within one context.

Fix a finite set `F` of types, closed under parts, holding `⊤`, `⊥` and the types of all
variables, and let `F'` be `F` together with the `{A:P..⊤}` for `P ∈ F`.  Every judgment in a
derivation of a `∀`-free judgment over `F` has the form `P <: dN k W` with `P ∈ F` and
`W ∈ F'`: the left side stays in `F`, while the right side is a stack of `k` declarations
`{A:⊥..·}` above a base `W`.  The stack behaves as a counter: the bnd rule pops it,
`sel_upper` and `bad_bounds` push it.  So two finite relations are saturated together:

* `B ⊆ F × F'`: the judgments `P <: W` (counter zero);
* `S ⊆ F × F`: the summaries, `(P, R) ∈ S` when for all `k`, `W`,
  `R <: dN k W` gives `P <: dN (k+1) W` (one level popped).

This module states the rules that derive the two relations and proves them sound; the
`∀` rule, which links contexts, and completeness are in `Family`.
-/

namespace Dsub

/-! ### Finite sets of types -/

/-- All variables of a scope. -/
def BVar.list : (n : ℕ) → List (BVar n)
  | 0 => []
  | n + 1 => .here :: (BVar.list n).map .there

theorem BVar.mem_list : ∀ {n : ℕ} (x : BVar n), x ∈ BVar.list n
  | _, .here => by simp [BVar.list]
  | _, .there x => by simp [BVar.list, BVar.mem_list x]

/-- `F` together with the declarations `{A:P..⊤}` for `P ∈ F`. -/
def ext {n : ℕ} (F : Finset (Ty n)) : Finset (Ty n) :=
  F ∪ F.image (fun P => .bnd P .top)

theorem mem_ext_of_mem {n : ℕ} {F : Finset (Ty n)} {P : Ty n} (h : P ∈ F) : P ∈ ext F :=
  Finset.mem_union_left _ h

theorem bnd_top_mem_ext {n : ℕ} {F : Finset (Ty n)} {P : Ty n} (h : P ∈ F) :
    Ty.bnd P .top ∈ ext F :=
  Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)

/-! ### The rules of saturation -/

/-- The bnd rule at counter zero. -/
def BndRule {n : ℕ} (B : Finset (Ty n × Ty n)) : Ty n → Ty n → Prop
  | .bnd L H, .bnd S₂ U₂ => (S₂, L) ∈ B ∧ (H, U₂) ∈ B
  | _, _ => False

instance {n : ℕ} (B : Finset (Ty n × Ty n)) (P W : Ty n) : Decidable (BndRule B P W) := by
  cases P <;> cases W <;> simp only [BndRule] <;> infer_instance

theorem BndRule.iff {n : ℕ} {B : Finset (Ty n × Ty n)} {P W : Ty n} :
    BndRule B P W ↔ ∃ L H S₂ U₂, P = .bnd L H ∧ W = .bnd S₂ U₂ ∧ (S₂, L) ∈ B ∧ (H, U₂) ∈ B := by
  cases P <;> cases W <;> simp [BndRule]

/-- When `P <: W` follows from the judgments `B` and summaries `S`. -/
def RuleB {n : ℕ} (Γ : Ctx n) (F : Finset (Ty n)) (B S : Finset (Ty n × Ty n)) (P W : Ty n) : Prop :=
  W = .top ∨ P = .bot ∨ (∃ x ∈ BVar.list n, P = .sel x ∧ W = .sel x) ∨ BndRule B P W ∨
  (∃ x ∈ BVar.list n, W = .sel x ∧ (Γ.lookup x, .bnd P .top) ∈ B) ∨
  (∃ y ∈ BVar.list n, P = .sel y ∧ ∃ R ∈ F, (Γ.lookup y, R) ∈ S ∧ (R, W) ∈ B) ∨
  (∃ x ∈ BVar.list n, (Γ.lookup x, .bnd P .top) ∈ B ∧ ∃ R ∈ F, (Γ.lookup x, R) ∈ S ∧ (R, W) ∈ B)

/-- When the summary `(P, T)` follows from the judgments `B` and summaries `S`. -/
def RuleS {n : ℕ} (Γ : Ctx n) (F : Finset (Ty n)) (B S : Finset (Ty n × Ty n)) (P T : Ty n) : Prop :=
  (∃ L ∈ F, P = .bnd L T) ∨ (P = .bot ∧ T = .bot) ∨
  (∃ y ∈ BVar.list n, P = .sel y ∧ ∃ R ∈ F, (Γ.lookup y, R) ∈ S ∧ (R, T) ∈ S) ∨
  (∃ x ∈ BVar.list n, (Γ.lookup x, .bnd P .top) ∈ B ∧ ∃ R ∈ F, (Γ.lookup x, R) ∈ S ∧ (R, T) ∈ S)

instance {n : ℕ} (Γ : Ctx n) (F : Finset (Ty n)) (B S : Finset (Ty n × Ty n)) (P W : Ty n) :
    Decidable (RuleB Γ F B S P W) := by
  unfold RuleB; infer_instance

instance {n : ℕ} (Γ : Ctx n) (F : Finset (Ty n)) (B S : Finset (Ty n × Ty n)) (P T : Ty n) :
    Decidable (RuleS Γ F B S P T) := by
  unfold RuleS; infer_instance

theorem RuleB.mono {n : ℕ} {Γ : Ctx n} {F : Finset (Ty n)} {B S B' S' : Finset (Ty n × Ty n)} (hB : B ⊆ B') (hS : S ⊆ S') {P W : Ty n}
    (h : RuleB Γ F B S P W) : RuleB Γ F B' S' P W := by
  rcases h with h | h | h | h | ⟨x, hx, h1, h2⟩ | ⟨y, hy, h1, R, hR, h2, h3⟩ |
    ⟨x, hx, h1, R, hR, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · rw [BndRule.iff] at h
    obtain ⟨L, H, S₂, U₂, h1, h2, h3, h4⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inl (BndRule.iff.2 ⟨L, H, S₂, U₂, h1, h2, hB h3, hB h4⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨x, hx, h1, hB h2⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨y, hy, h1, R, hR, hS h2, hB h3⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨x, hx, hB h1, R, hR, hS h2, hB h3⟩)))))

theorem RuleS.mono {n : ℕ} {Γ : Ctx n} {F : Finset (Ty n)} {B S B' S' : Finset (Ty n × Ty n)} (hB : B ⊆ B') (hS : S ⊆ S') {P T : Ty n}
    (h : RuleS Γ F B S P T) : RuleS Γ F B' S' P T := by
  rcases h with h | h | ⟨y, hy, h1, R, hR, h2, h3⟩ | ⟨x, hx, h1, R, hR, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl ⟨y, hy, h1, R, hR, hS h2, hS h3⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨x, hx, hB h1, R, hR, hS h2, hS h3⟩))

/-! ### Soundness of the rules -/

/-- The judgments hold. -/
def SoundB {n : ℕ} (Γ : Ctx n) (B : Finset (Ty n × Ty n)) : Prop := ∀ p ∈ B, Sub Γ p.1 p.2

/-- The summaries hold: popping one level. -/
def SoundS {n : ℕ} (Γ : Ctx n) (S : Finset (Ty n × Ty n)) : Prop :=
  ∀ p ∈ S, ∀ k W, Sub Γ p.2 (Ty.dN k W) → Sub Γ p.1 (Ty.dN (k + 1) W)

theorem RuleB.sound {n : ℕ} {Γ : Ctx n} {F : Finset (Ty n)} {B S : Finset (Ty n × Ty n)} (hB : SoundB Γ B) (hS : SoundS Γ S)
    {P W : Ty n} (h : RuleB Γ F B S P W) : Sub Γ P W := by
  rcases h with rfl | rfl | ⟨x, -, rfl, rfl⟩ | h | ⟨x, -, rfl, h⟩ | ⟨y, -, rfl, R, -, h1, h2⟩ |
    ⟨x, -, h0, R, -, h1, h2⟩
  · exact .top _
  · exact .bot _
  · exact .refl_sel x
  · obtain ⟨L, H, S₂, U₂, rfl, rfl, h1, h2⟩ := BndRule.iff.1 h
    exact .bnd (hB _ h1) (hB _ h2)
  · exact .sel_lower x (hB _ h)
  · exact .sel_upper y (hS _ h1 0 W (hB _ h2))
  · exact .bad_bounds x (hB _ h0) (hS _ h1 0 W (hB _ h2))

theorem RuleS.sound {n : ℕ} {Γ : Ctx n} {F : Finset (Ty n)} {B S : Finset (Ty n × Ty n)} (hB : SoundB Γ B) (hS : SoundS Γ S)
    {P T : Ty n} (h : RuleS Γ F B S P T) :
    ∀ k W, Sub Γ T (Ty.dN k W) → Sub Γ P (Ty.dN (k + 1) W) := by
  intro k W hT
  rcases h with ⟨L, -, rfl⟩ | ⟨rfl, rfl⟩ | ⟨y, -, rfl, R, -, h1, h2⟩ | ⟨x, -, h0, R, -, h1, h2⟩
  · exact .bnd (.bot _) hT
  · exact .bot _
  · exact .sel_upper y (hS _ h1 (k + 1) W (hS _ h2 k W hT))
  · exact .bad_bounds x (hB _ h0) (hS _ h1 (k + 1) W (hS _ h2 k W hT))

/-! ### Chains of summaries -/

/-- `k` summaries in a row. -/
inductive Chain {n : ℕ} (S : Finset (Ty n × Ty n)) : ℕ → Ty n → Ty n → Prop where
  | zero (P : Ty n) : Chain S 0 P P
  | succ {k : ℕ} {P R T : Ty n} : (P, R) ∈ S → Chain S k R T → Chain S (k + 1) P T

end Dsub
