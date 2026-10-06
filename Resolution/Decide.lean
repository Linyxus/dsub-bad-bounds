import Resolution.Lemmas
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union

/-!
A decision procedure for the `∀`-free fragment.

Fix a finite set `F` of types, closed under parts, holding `⊤`, `⊥` and the types of all
variables, and let `F'` be `F` together with the `{A:P..⊤}` for `P ∈ F`.  Every judgment in a
derivation of a `∀`-free judgment over `F` has the form `P <: dN k W` with `P ∈ F` and
`W ∈ F'`: the left side stays in `F`, while the right side is a stack of `k` declarations
`{A:⊥..·}` above a base `W`.  The stack behaves as a counter: the bnd rule pops it,
`sel_upper` and `bad_bounds` push it.  So two finite relations are saturated together:

* `B ⊆ F × F'`: the judgments `P <: W` (counter zero);
* `S ⊆ F × F`: the summaries, `(P, R) ∈ S` when for all `k`, `W`,
  `R <: dN k W` gives `P <: dN (k+1) W` (one level popped).

Soundness holds for every context; completeness needs the context and the two types to be
`∀`-free.
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

/-- The parts of a type (not entering the bodies of `∀`). -/
def Ty.parts {n : ℕ} : Ty n → Finset (Ty n)
  | .top => {.top}
  | .bot => {.bot}
  | .sel x => {.sel x}
  | .bnd S U => insert (.bnd S U) (S.parts ∪ U.parts)
  | .all S T => insert (.all S T) S.parts

theorem Ty.mem_parts_self {n : ℕ} (T : Ty n) : T ∈ T.parts := by
  cases T <;> simp [Ty.parts]

theorem Ty.parts_closed {n : ℕ} {T L H : Ty n} (h : Ty.bnd L H ∈ T.parts) :
    L ∈ T.parts ∧ H ∈ T.parts := by
  induction T with
  | top => simp [Ty.parts] at h
  | bot => simp [Ty.parts] at h
  | sel x => simp [Ty.parts] at h
  | bnd S U ihS ihU =>
    simp only [Ty.parts, Finset.mem_insert, Finset.mem_union, Ty.bnd.injEq] at h ⊢
    rcases h with ⟨rfl, rfl⟩ | h | h
    · exact ⟨Or.inr (Or.inl (Ty.mem_parts_self _)), Or.inr (Or.inr (Ty.mem_parts_self _))⟩
    · exact ⟨Or.inr (Or.inl (ihS h).1), Or.inr (Or.inl (ihS h).2)⟩
    · exact ⟨Or.inr (Or.inr (ihU h).1), Or.inr (Or.inr (ihU h).2)⟩
  | all S T ihS _ =>
    simp only [Ty.parts, Finset.mem_insert, reduceCtorEq, false_or] at h ⊢
    exact ⟨Or.inr (ihS h).1, Or.inr (ihS h).2⟩

/-- The type mentions no `∀`. -/
def Ty.AllFree {n : ℕ} : Ty n → Prop
  | .top => True
  | .bot => True
  | .sel _ => True
  | .bnd S U => S.AllFree ∧ U.AllFree
  | .all _ _ => False

/-- The context mentions no `∀`. -/
def Ctx.AllFree : {n : ℕ} → Ctx n → Prop
  | _, .empty => True
  | _, .push Γ T => Γ.AllFree ∧ T.AllFree

theorem Ty.AllFree.rename {n m : ℕ} {T : Ty n} (h : T.AllFree) (f : Rename n m) :
    (T.rename f).AllFree := by
  induction T with
  | top => trivial
  | bot => trivial
  | sel x => trivial
  | bnd S U ihS ihU => exact ⟨ihS h.1 f, ihU h.2 f⟩
  | all S T => exact h.elim

theorem Ctx.AllFree.lookup {n : ℕ} {Γ : Ctx n} (h : Γ.AllFree) (x : BVar n) :
    (Γ.lookup x).AllFree := by
  induction Γ with
  | empty => nomatch x
  | push Γ T ih =>
    cases x with
    | here => exact h.2.rename _
    | there x => exact (ih h.1 x).rename _

theorem Ty.AllFree.parts {n : ℕ} {T P : Ty n} (h : T.AllFree) (hP : P ∈ T.parts) :
    P.AllFree := by
  induction T with
  | top => simp only [Ty.parts, Finset.mem_singleton] at hP; subst hP; trivial
  | bot => simp only [Ty.parts, Finset.mem_singleton] at hP; subst hP; trivial
  | sel x => simp only [Ty.parts, Finset.mem_singleton] at hP; subst hP; trivial
  | bnd S U ihS ihU =>
    simp only [Ty.parts, Finset.mem_insert, Finset.mem_union] at hP
    rcases hP with rfl | hP | hP
    · exact h
    · exact ihS h.1 hP
    · exact ihU h.2 hP
  | all S T => exact h.elim

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

/-! ### Completeness of saturation -/

/-- `k` summaries in a row. -/
inductive Chain {n : ℕ} (S : Finset (Ty n × Ty n)) : ℕ → Ty n → Ty n → Prop where
  | zero (P : Ty n) : Chain S 0 P P
  | succ {k : ℕ} {P R T : Ty n} : (P, R) ∈ S → Chain S k R T → Chain S (k + 1) P T

/-- `F` has what completeness needs, and `B`, `S` are saturated over it. -/
structure Saturated {n : ℕ} (Γ : Ctx n) (F : Finset (Ty n)) (B S : Finset (Ty n × Ty n)) : Prop where
  top_mem : Ty.top ∈ F
  bot_mem : Ty.bot ∈ F
  lookup_mem : ∀ x, Γ.lookup x ∈ F
  closed : ∀ L H, Ty.bnd L H ∈ F → L ∈ F ∧ H ∈ F
  allFree : ∀ T ∈ F, T.AllFree
  S_sub : ∀ p ∈ S, p.1 ∈ F ∧ p.2 ∈ F
  closedB : ∀ P ∈ F, ∀ W ∈ ext F, RuleB Γ F B S P W → (P, W) ∈ B
  closedS : ∀ P ∈ F, ∀ T ∈ F, RuleS Γ F B S P T → (P, T) ∈ S

theorem Saturated.ext_closed {n : ℕ} {Γ : Ctx n} {F : Finset (Ty n)} {B S : Finset (Ty n × Ty n)} (hs : Saturated Γ F B S)
    {L H : Ty n} (h : Ty.bnd L H ∈ ext F) : L ∈ F ∧ H ∈ F := by
  rcases Finset.mem_union.1 h with h | h
  · exact hs.closed L H h
  · obtain ⟨P, hP, e⟩ := Finset.mem_image.1 h
    simp only [Ty.bnd.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨hP, hs.top_mem⟩

theorem Saturated.chain_bot {n : ℕ} {Γ : Ctx n} {F : Finset (Ty n)} {B S : Finset (Ty n × Ty n)} (hs : Saturated Γ F B S) :
    ∀ k, Chain S k .bot .bot
  | 0 => .zero _
  | k + 1 => .succ (hs.closedS _ hs.bot_mem _ hs.bot_mem (Or.inr (Or.inl ⟨rfl, rfl⟩)))
      (hs.chain_bot k)

theorem Sub.complete {n : ℕ} {Γ : Ctx n} {P Q : Ty n} (D : Sub Γ P Q) :
    ∀ {F : Finset (Ty n)} {B S : Finset (Ty n × Ty n)}, Saturated Γ F B S → P ∈ F →
      ∀ k W, W ∈ ext F → Q = Ty.dN k W → ∃ R, Chain S k P R ∧ (R, W) ∈ B := by
  induction D with
  | top T =>
    intro F B S hs hP k W hW e
    cases k with
    | zero =>
      subst e
      exact ⟨T, .zero _, hs.closedB _ hP _ hW (Or.inl rfl)⟩
    | succ k => simp at e
  | bot T =>
    intro F B S hs hP k W hW e
    exact ⟨_, hs.chain_bot k, hs.closedB _ hP _ hW (Or.inr (Or.inl rfl))⟩
  | refl_sel x =>
    intro F B S hs hP k W hW e
    cases k with
    | zero =>
      subst e
      exact ⟨_, .zero _, hs.closedB _ hP _ hW
        (Or.inr (Or.inr (Or.inl ⟨x, BVar.mem_list x, rfl, rfl⟩)))⟩
    | succ k => simp at e
  | @bnd _ _ S₁ U₁ S₂ U₂ _ _ ihS ihU =>
    intro F B S hs hP k W hW e
    obtain ⟨hS₁, hU₁⟩ := hs.closed _ _ hP
    cases k with
    | zero =>
      subst e
      obtain ⟨hS₂, hU₂⟩ := hs.ext_closed hW
      obtain ⟨R₁, c₁, h₁⟩ := ihS hs hS₂ 0 S₁ (mem_ext_of_mem hS₁) rfl
      obtain ⟨R₂, c₂, h₂⟩ := ihU hs hU₁ 0 U₂ (mem_ext_of_mem hU₂) rfl
      cases c₁; cases c₂
      refine ⟨_, .zero _, hs.closedB _ hP _ hW ?_⟩
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h₁, h₂⟩)))
    | succ k =>
      simp only [Ty.dN_succ, Ty.bnd.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      obtain ⟨R, c, h⟩ := ihU hs hU₁ k W hW rfl
      exact ⟨R, .succ (hs.closedS _ hP _ hU₁ (Or.inl ⟨S₁, hS₁, rfl⟩)) c, h⟩
  | all _ _ =>
    intro F B S hs hP
    exact (hs.allFree _ hP).elim
  | @sel_lower _ _ P x _ ih =>
    intro F B S hs hP k W hW e
    cases k with
    | zero =>
      subst e
      obtain ⟨R, c, h⟩ := ih hs (hs.lookup_mem x) 0 _ (bnd_top_mem_ext hP) rfl
      cases c
      exact ⟨_, .zero _, hs.closedB _ hP _ hW
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨x, BVar.mem_list x, rfl, h⟩)))))⟩
    | succ k => simp at e
  | sel_upper y _ ih =>
    intro F B S hs hP k W hW e
    subst e
    obtain ⟨R, c, h⟩ := ih hs (hs.lookup_mem y) (k + 1) W hW rfl
    obtain _ | ⟨h₁, c⟩ := c
    have hR₁ := (hs.S_sub _ h₁).2
    cases k with
    | zero =>
      cases c
      exact ⟨_, .zero _, hs.closedB _ hP _ hW (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨y, BVar.mem_list y, rfl, _, hR₁, h₁, h⟩))))))⟩
    | succ k =>
      obtain _ | ⟨h₂, c⟩ := c
      have hR₂ := (hs.S_sub _ h₂).2
      exact ⟨R, .succ (hs.closedS _ hP _ hR₂
        (Or.inr (Or.inr (Or.inl ⟨y, BVar.mem_list y, rfl, _, hR₁, h₁, h₂⟩)))) c, h⟩
  | @bad_bounds _ _ P U x _ _ ih1 ih2 =>
    intro F B S hs hP k W hW e
    subst e
    obtain ⟨R₀, c₀, h₀⟩ := ih1 hs (hs.lookup_mem x) 0 _ (bnd_top_mem_ext hP) rfl
    cases c₀
    obtain ⟨R, c, h⟩ := ih2 hs (hs.lookup_mem x) (k + 1) W hW rfl
    obtain _ | ⟨h₁, c⟩ := c
    have hR₁ := (hs.S_sub _ h₁).2
    cases k with
    | zero =>
      cases c
      exact ⟨_, .zero _, hs.closedB _ hP _ hW (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr ⟨x, BVar.mem_list x, h₀, _, hR₁, h₁, h⟩))))))⟩
    | succ k =>
      obtain _ | ⟨h₂, c⟩ := c
      have hR₂ := (hs.S_sub _ h₂).2
      exact ⟨R, .succ (hs.closedS _ hP _ hR₂
        (Or.inr (Or.inr (Or.inr ⟨x, BVar.mem_list x, h₀, _, hR₁, h₁, h₂⟩)))) c, h⟩

/-! ### Saturation by iteration -/

/-- One round of saturation over `F`. -/
def step {n : ℕ} (Γ : Ctx n) (F : Finset (Ty n)) (x : Finset (Ty n × Ty n) × Finset (Ty n × Ty n)) :
    Finset (Ty n × Ty n) × Finset (Ty n × Ty n) :=
  ((F ×ˢ ext F).filter (fun p => RuleB Γ F x.1 x.2 p.1 p.2),
   (F ×ˢ F).filter (fun p => RuleS Γ F x.1 x.2 p.1 p.2))

/-- `i` rounds of saturation from nothing. -/
def iter {n : ℕ} (Γ : Ctx n) (F : Finset (Ty n)) : ℕ → Finset (Ty n × Ty n) × Finset (Ty n × Ty n)
  | 0 => (∅, ∅)
  | i + 1 => step Γ F (iter Γ F i)

theorem step_mono {n : ℕ} {Γ : Ctx n} {F : Finset (Ty n)} {x y : Finset (Ty n × Ty n) × Finset (Ty n × Ty n)} (h1 : x.1 ⊆ y.1)
    (h2 : x.2 ⊆ y.2) : (step Γ F x).1 ⊆ (step Γ F y).1 ∧ (step Γ F x).2 ⊆ (step Γ F y).2 := by
  constructor
  · intro p hp
    simp only [step, Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.mono h1 h2⟩
  · intro p hp
    simp only [step, Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.mono h1 h2⟩

theorem iter_mono {n : ℕ} {Γ : Ctx n} {F : Finset (Ty n)} : ∀ i : ℕ, (iter Γ F i).1 ⊆ (iter Γ F (i + 1)).1 ∧
    (iter Γ F i).2 ⊆ (iter Γ F (i + 1)).2
  | 0 => ⟨Finset.empty_subset _, Finset.empty_subset _⟩
  | i + 1 => step_mono (iter_mono i).1 (iter_mono i).2

/-- The size of a pair of relations. -/
def size {n : ℕ} (x : Finset (Ty n × Ty n) × Finset (Ty n × Ty n)) : ℕ := x.1.card + x.2.card

/-- The most rounds saturation can take. -/
def bound {n : ℕ} (F : Finset (Ty n)) : ℕ := (F ×ˢ ext F).card + (F ×ˢ F).card

theorem size_iter_le {n : ℕ} {Γ : Ctx n} {F : Finset (Ty n)} (i : ℕ) : size (iter Γ F (i + 1)) ≤ bound F := by
  simp only [size, iter, step, bound]
  exact Nat.add_le_add (Finset.card_le_card (Finset.filter_subset _ _))
    (Finset.card_le_card (Finset.filter_subset _ _))

theorem size_lt_of_ne {n : ℕ} {Γ : Ctx n} {F : Finset (Ty n)} (i : ℕ) (h : iter Γ F i ≠ iter Γ F (i + 1)) :
    size (iter Γ F i) < size (iter Γ F (i + 1)) := by
  obtain ⟨m1, m2⟩ := iter_mono (Γ := Γ) (F := F) i
  simp only [size]
  by_cases e1 : (iter Γ F i).1 = (iter Γ F (i + 1)).1
  · have e2 : (iter Γ F i).2 ≠ (iter Γ F (i + 1)).2 := fun e2 => h (Prod.ext e1 e2)
    have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨m2, e2⟩)
    rw [e1]; omega
  · have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨m1, e1⟩)
    have := Finset.card_le_card m2
    omega

theorem iter_progress {n : ℕ} {Γ : Ctx n} {F : Finset (Ty n)} : ∀ i, iter Γ F i = iter Γ F (i + 1) ∨ i + 1 ≤ size (iter Γ F (i + 1))
  | 0 => by
    by_cases e : iter Γ F 0 = iter Γ F 1
    · exact Or.inl e
    · have := size_lt_of_ne 0 e
      exact Or.inr (by omega)
  | i + 1 => by
    by_cases e : iter Γ F (i + 1) = iter Γ F (i + 2)
    · exact Or.inl e
    · have hlt := size_lt_of_ne (i + 1) e
      rcases iter_progress (Γ := Γ) (F := F) i with e' | h
      · exact absurd (show iter Γ F (i + 1) = iter Γ F (i + 2) from
          show step Γ F (iter Γ F i) = step Γ F (iter Γ F (i + 1)) by rw [← e']) e
      · exact Or.inr (by omega)

theorem iter_fixed {n : ℕ} {Γ : Ctx n} {F : Finset (Ty n)} : step Γ F (iter Γ F (bound F)) = iter Γ F (bound F) := by
  rcases iter_progress (Γ := Γ) (F := F) (bound F) with e | h
  · exact e.symm
  · have := size_iter_le (Γ := Γ) (F := F) (bound F)
    omega

theorem iter_sound {n : ℕ} {Γ : Ctx n} {F : Finset (Ty n)} : ∀ i, SoundB Γ (iter Γ F i).1 ∧ SoundS Γ (iter Γ F i).2
  | 0 => ⟨fun _ h => by simp [iter] at h, fun _ h => by simp [iter] at h⟩
  | i + 1 => by
    obtain ⟨hB, hS⟩ := iter_sound (Γ := Γ) (F := F) i
    constructor
    · intro p hp
      simp only [iter, step, Finset.mem_filter] at hp
      exact hp.2.sound hB hS
    · intro p hp
      simp only [iter, step, Finset.mem_filter] at hp
      exact hp.2.sound hB hS

/-! ### The procedure -/

/-- The types the procedure works over for `Γ ⊢ P <: U`. -/
def univF {n : ℕ} (Γ : Ctx n) (P U : Ty n) : Finset (Ty n) :=
  {.top, .bot} ∪ P.parts ∪ U.parts ∪ (BVar.list n).toFinset.biUnion (fun x => (Γ.lookup x).parts)

/-- Saturation that stops at a fixed point, with at most `k` more rounds. -/
def saturate {n : ℕ} (Γ : Ctx n) (F : Finset (Ty n)) :
    ℕ → Finset (Ty n × Ty n) × Finset (Ty n × Ty n) → Finset (Ty n × Ty n) × Finset (Ty n × Ty n)
  | 0, x => x
  | k + 1, x => if step Γ F x = x then x else saturate Γ F k (step Γ F x)

theorem saturate_iter {n : ℕ} {Γ : Ctx n} {F : Finset (Ty n)} : ∀ k i, ∃ j,
    saturate Γ F k (iter Γ F i) = iter Γ F j ∧
      (step Γ F (iter Γ F j) = iter Γ F j ∨ j = i + k)
  | 0, i => ⟨i, rfl, Or.inr rfl⟩
  | k + 1, i => by
    by_cases e : step Γ F (iter Γ F i) = iter Γ F i
    · exact ⟨i, by simp only [saturate, e, ite_true], Or.inl e⟩
    · obtain ⟨j, h1, h2⟩ := saturate_iter (Γ := Γ) (F := F) k (i + 1)
      refine ⟨j, ?_, ?_⟩
      · simp only [saturate, e, ite_false]; exact h1
      · rcases h2 with h2 | h2
        · exact Or.inl h2
        · exact Or.inr (by omega)

/-- Saturation from nothing reaches a fixed point, which is an iterate. -/
theorem saturate_spec {n : ℕ} (Γ : Ctx n) (F : Finset (Ty n)) : ∃ j,
    saturate Γ F (bound F) (∅, ∅) = iter Γ F j ∧ step Γ F (iter Γ F j) = iter Γ F j := by
  obtain ⟨j, h1, h2⟩ := saturate_iter (Γ := Γ) (F := F) (bound F) 0
  refine ⟨j, h1, ?_⟩
  rcases h2 with h2 | h2
  · exact h2
  · rw [h2, Nat.zero_add]; exact iter_fixed

/-- Decides `Γ ⊢ P <: U`: sound always, complete on `∀`-free judgments. -/
def decideFree {n : ℕ} (Γ : Ctx n) (P U : Ty n) : Bool :=
  decide ((P, U) ∈ (saturate Γ (univF Γ P U) (bound (univF Γ P U)) (∅, ∅)).1)

theorem decideFree_sound {n : ℕ} {Γ : Ctx n} {P U : Ty n} (h : decideFree Γ P U = true) :
    Sub Γ P U := by
  obtain ⟨j, e, _⟩ := saturate_spec Γ (univF Γ P U)
  have h' := of_decide_eq_true h
  rw [e] at h'
  exact (iter_sound _).1 _ h'

theorem univF_closed {n : ℕ} {Γ : Ctx n} {P U L H : Ty n}
    (h : Ty.bnd L H ∈ univF Γ P U) : L ∈ univF Γ P U ∧ H ∈ univF Γ P U := by
  simp only [univF, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_biUnion, List.mem_toFinset, reduceCtorEq, false_or] at h ⊢
  rcases h with (h | h) | ⟨x, hx, h⟩
  · exact ⟨Or.inl (Or.inl (Or.inr (Ty.parts_closed h).1)),
      Or.inl (Or.inl (Or.inr (Ty.parts_closed h).2))⟩
  · exact ⟨Or.inl (Or.inr (Ty.parts_closed h).1), Or.inl (Or.inr (Ty.parts_closed h).2)⟩
  · exact ⟨Or.inr ⟨x, hx, (Ty.parts_closed h).1⟩, Or.inr ⟨x, hx, (Ty.parts_closed h).2⟩⟩

theorem decideFree_complete {n : ℕ} {Γ : Ctx n} {P U : Ty n} (hΓ : Γ.AllFree)
    (hP : P.AllFree) (hU : U.AllFree) (h : Sub Γ P U) : decideFree Γ P U = true := by
  set F := univF Γ P U with hF
  obtain ⟨j, e, fix⟩ := saturate_spec Γ F
  set x := iter Γ F j
  have hs : Saturated Γ F x.1 x.2 := by
    refine ⟨?_, ?_, ?_, fun L H h => univF_closed h, ?_, ?_, ?_, ?_⟩
    · simp [F, univF]
    · simp [F, univF]
    · intro y
      simp only [F, univF, Finset.mem_union, Finset.mem_biUnion, List.mem_toFinset]
      exact Or.inr ⟨y, BVar.mem_list y, Ty.mem_parts_self _⟩
    · intro T hT
      simp only [F, univF, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        Finset.mem_biUnion, List.mem_toFinset] at hT
      rcases hT with (((rfl | rfl) | hT) | hT) | ⟨y, -, hT⟩
      · trivial
      · trivial
      · exact hP.parts hT
      · exact hU.parts hT
      · exact (hΓ.lookup y).parts hT
    · intro p hp
      rw [← fix] at hp
      simp only [step, Finset.mem_filter, Finset.mem_product] at hp
      exact hp.1
    · intro P' hP' W hW hr
      rw [← fix]
      simp only [step, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hP', hW⟩, hr⟩
    · intro P' hP' T hT hr
      rw [← fix]
      simp only [step, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hP', hT⟩, hr⟩
  have hPF : P ∈ F := by
    simp only [F, univF, Finset.mem_union]
    exact Or.inl (Or.inl (Or.inr (Ty.mem_parts_self P)))
  have hUF : U ∈ F := by
    simp only [F, univF, Finset.mem_union]
    exact Or.inl (Or.inr (Ty.mem_parts_self U))
  obtain ⟨R, c, hR⟩ := h.complete hs hPF 0 U (mem_ext_of_mem hUF) rfl
  cases c
  simp only [decideFree, ← hF, e]
  exact decide_eq_true hR

/-- On `∀`-free judgments, the procedure decides subtyping. -/
theorem decideFree_iff {n : ℕ} {Γ : Ctx n} {P U : Ty n} (hΓ : Γ.AllFree) (hP : P.AllFree)
    (hU : U.AllFree) : decideFree Γ P U = true ↔ Sub Γ P U :=
  ⟨decideFree_sound, decideFree_complete hΓ hP hU⟩

end Dsub
