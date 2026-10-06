import Resolution.FamilyEnum
import Resolution.PrimCtx

/-!
# The rule check on codes

Facts of the family `Φ L s` are coded by naturals: the judgment `P <: W` of a member `Γ` by
`bcodeC n Γ.code P.code W.code = Nat.pair 0 ⟨Γ, P, W⟩.code`, the summary `(P, T)` by
`scodeC … = Nat.pair 1 …`. A list `R` of codes is read as facts of every context `Γ`
(`BofR s R Γ`, `SofR s R Γ`) and of the family (`factsOf L s R`). `firesLS L s R c` holds iff `c`
codes a fact of the family that follows by one rule (`GRuleB`, `GRuleS`: the rules of
`Family.FRuleB`, `Family.FRuleS` read on `R`). It is primitive recursive.
-/

namespace Dsub

open Family

/-! ### Sizes on codes -/

/-- The size of the type with a given code. -/
def sizeC : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | m + 2 =>
    if m % 3 = 0 then 1
    else sizeC (Nat.unpair (m / 3)).1 + sizeC (Nat.unpair (m / 3)).2 + 1
termination_by m => m
decreasing_by all_goals first | exact unpair_fst_lt | exact unpair_snd_lt

theorem sizeC_code {n : ℕ} (T : Ty n) : sizeC T.code = T.size := by
  induction T with
  | top => rw [Ty.code, sizeC]; rfl
  | bot => rw [Ty.code, sizeC]; rfl
  | sel x =>
    rw [Ty.code_sel, sizeC]
    simp [Ty.size]
  | bnd S U ihS ihU =>
    rw [Ty.code_bnd, show 3 * Nat.pair S.code U.code + 3 = (3 * Nat.pair S.code U.code + 1) + 2 by
      omega, sizeC]
    have e1 : (3 * Nat.pair S.code U.code + 1) % 3 = 1 := by omega
    have e2 : (3 * Nat.pair S.code U.code + 1) / 3 = Nat.pair S.code U.code := by omega
    simp only [e1, e2, Nat.unpair_pair, ihS, ihU, Ty.size]; simp
  | all S T ihS ihT =>
    rw [Ty.code_all, show 3 * Nat.pair S.code T.code + 4 = (3 * Nat.pair S.code T.code + 2) + 2 by
      omega, sizeC]
    have e1 : (3 * Nat.pair S.code T.code + 2) % 3 = 2 := by omega
    have e2 : (3 * Nat.pair S.code T.code + 2) / 3 = Nat.pair S.code T.code := by omega
    simp only [e1, e2, Nat.unpair_pair, ihS, ihT, Ty.size]; simp

/-! ### Inversions on codes -/

@[simp] theorem tyTag_zero : tyTag 0 = 0 := by simp [tyTag]
@[simp] theorem tyTag_one : tyTag 1 = 1 := by simp [tyTag]

theorem Ty.code_eq_zero {n : ℕ} {T : Ty n} : T.code = 0 ↔ T = .top :=
  ⟨fun h => Ty.code_injective (h.trans rfl), fun h => h ▸ rfl⟩

theorem Ty.code_eq_one {n : ℕ} {T : Ty n} : T.code = 1 ↔ T = .bot :=
  ⟨fun h => Ty.code_injective (h.trans rfl), fun h => h ▸ rfl⟩

theorem tag_two {n : ℕ} {T : Ty n} : tyTag T.code = 2 ↔ ∃ x, T = .sel x := by
  cases T <;> simp

theorem tag_three {n : ℕ} {T : Ty n} : tyTag T.code = 3 ↔ ∃ L H, T = .bnd L H := by
  cases T <;> simp

theorem tag_four {n : ℕ} {T : Ty n} : tyTag T.code = 4 ↔ ∃ S B, T = .all S B := by
  cases T <;> simp

theorem bndC_top {n : ℕ} (P : Ty n) : bndC P.code 0 = (Ty.bnd P .top).code := rfl

theorem exists_range_iff {n : ℕ} {p : ℕ → Prop} :
    (∃ i ∈ List.range n, p i) ↔ ∃ x ∈ BVar.list n, p x.toNat := by
  simp only [List.mem_range]
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨BVar.ofLt n i hi, BVar.mem_list _, by rwa [BVar.toNat_ofLt]⟩
  · rintro ⟨x, -, h⟩
    exact ⟨x.toNat, x.toNat_lt, h⟩

/-! ### Bounded contexts on codes -/

/-- Every entry of the context with code `g` of scope `n` has size at most `s`. -/
def CtxBnd (s n g : ℕ) : Prop := ∀ i < n, sizeC (headC (tailC^[i] g)) ≤ s

instance (s n g : ℕ) : Decidable (CtxBnd s n g) := by unfold CtxBnd; infer_instance

/-- Whether every entry of a context code has size at most `s`. -/
def ctxBoundedC (s n g : ℕ) : Bool := decide (CtxBnd s n g)

theorem CtxBnd_succ {s n g : ℕ} :
    CtxBnd s (n + 1) g ↔ sizeC (headC g) ≤ s ∧ CtxBnd s n (tailC g) := by
  constructor
  · intro h
    refine ⟨h 0 (by omega), fun i hi => ?_⟩
    have := h (i + 1) (by omega)
    rwa [Function.iterate_succ_apply] at this
  · rintro ⟨h0, h⟩ i hi
    cases i with
    | zero => exact h0
    | succ i => rw [Function.iterate_succ_apply]; exact h i (by omega)

theorem ctxBoundedC_code {s n : ℕ} (Γ : Ctx n) : ctxBoundedC s n Γ.code = true ↔ Γ.Bounded s := by
  rw [ctxBoundedC, decide_eq_true_iff]
  induction Γ with
  | empty => simp [CtxBnd, Ctx.Bounded]
  | push Γ T ih =>
    rw [CtxBnd_succ, Ctx.code_push, headC_pushC, tailC_pushC, ih, sizeC_code, Ctx.Bounded]
    exact and_comm

/-! ### Facts as codes -/

/-- The code of the judgment `P <: W` of `Γ`. -/
def bcodeC (n g a b : ℕ) : ℕ := Nat.pair 0 (mkJ n g a b)
/-- The code of the summary `(P, T)` of `Γ`. -/
def scodeC (n g a b : ℕ) : ℕ := Nat.pair 1 (mkJ n g a b)

/-- The judgments of `Γ` recorded in `R`, within the types of size at most `s`. -/
def BofR (s : ℕ) (R : List ℕ) {n : ℕ} (Γ : Ctx n) : Finset (Ty n × Ty n) :=
  (tysUpTo n s ×ˢ ext (tysUpTo n s)).filter fun p => bcodeC n Γ.code p.1.code p.2.code ∈ R

/-- The summaries of `Γ` recorded in `R`, within the types of size at most `s`. -/
def SofR (s : ℕ) (R : List ℕ) {n : ℕ} (Γ : Ctx n) : Finset (Ty n × Ty n) :=
  (tysUpTo n s ×ˢ tysUpTo n s).filter fun p => scodeC n Γ.code p.1.code p.2.code ∈ R

/-- The facts of the family `Φ L s` recorded in `R`. -/
def factsOf (L s : ℕ) (R : List ℕ) : (Φ L s).Facts :=
  fun i => (BofR s R ((Φ L s).ctx i), SofR s R ((Φ L s).ctx i))

/-- The judgment rule of the family, read on `R`, at any context. -/
def GRuleB (L s : ℕ) (R : List ℕ) {n : ℕ} (Γ : Ctx n) (P W : Ty n) : Prop :=
  RuleB Γ (tysUpTo n s) (BofR s R Γ) (SofR s R Γ) P W ∨ AllRule (factsOf L s R) Γ P W

/-- The summary rule of the family, read on `R`, at any context. -/
def GRuleS (s : ℕ) (R : List ℕ) {n : ℕ} (Γ : Ctx n) (P T : Ty n) : Prop :=
  RuleS Γ (tysUpTo n s) (BofR s R Γ) (SofR s R Γ) P T

theorem mem_BofR {s : ℕ} {R : List ℕ} {n : ℕ} {Γ : Ctx n} {A B : Ty n} :
    (A, B) ∈ BofR s R Γ ↔
      A.size ≤ s ∧ B ∈ ext (tysUpTo n s) ∧ bcodeC n Γ.code A.code B.code ∈ R := by
  simp [BofR, mem_tysUpTo, and_assoc]

theorem mem_SofR {s : ℕ} {R : List ℕ} {n : ℕ} {Γ : Ctx n} {A B : Ty n} :
    (A, B) ∈ SofR s R Γ ↔ A.size ≤ s ∧ B.size ≤ s ∧ scodeC n Γ.code A.code B.code ∈ R := by
  simp [SofR, mem_tysUpTo, and_assoc]

theorem BofR_mono {s : ℕ} {R R' : List ℕ} (h : ∀ x ∈ R, x ∈ R') {n : ℕ} (Γ : Ctx n) :
    BofR s R Γ ⊆ BofR s R' Γ := by
  intro p hp
  obtain ⟨A, B⟩ := p
  rw [mem_BofR] at hp ⊢
  exact ⟨hp.1, hp.2.1, h _ hp.2.2⟩

theorem SofR_mono {s : ℕ} {R R' : List ℕ} (h : ∀ x ∈ R, x ∈ R') {n : ℕ} (Γ : Ctx n) :
    SofR s R Γ ⊆ SofR s R' Γ := by
  intro p hp
  obtain ⟨A, B⟩ := p
  rw [mem_SofR] at hp ⊢
  exact ⟨hp.1, hp.2.1, h _ hp.2.2⟩

theorem factsOf_mono {L s : ℕ} {R R' : List ℕ} (h : ∀ x ∈ R, x ∈ R') :
    Le (factsOf L s R) (factsOf L s R') :=
  fun _ => ⟨BofR_mono h _, SofR_mono h _⟩

theorem GRuleB.mono {L s : ℕ} {R R' : List ℕ} (h : ∀ x ∈ R, x ∈ R') {n : ℕ} {Γ : Ctx n}
    {P W : Ty n} (hr : GRuleB L s R Γ P W) : GRuleB L s R' Γ P W :=
  hr.imp (RuleB.mono (BofR_mono h Γ) (SofR_mono h Γ)) (AllRule.mono (factsOf_mono h))

theorem GRuleS.mono {s : ℕ} {R R' : List ℕ} (h : ∀ x ∈ R, x ∈ R') {n : ℕ} {Γ : Ctx n}
    {P T : Ty n} (hr : GRuleS s R Γ P T) : GRuleS s R' Γ P T :=
  RuleS.mono (BofR_mono h Γ) (SofR_mono h Γ) hr

/-- A recorded judgment of a bounded context is a recorded judgment of a member. -/
theorem exists_member_fact {L s n'' : ℕ} {Γ'' : Ctx n''} (hn : n'' ≤ L) (hΓ : Γ''.Bounded s)
    {R : List ℕ} {A B : Ty n''} (hAB : (A, B) ∈ BofR s R Γ'')
    (Q : (k : ℕ) → Ctx k → Ty k → Ty k → Prop) (hQ : Q n'' Γ'' A B) :
    ∃ j : Fin (Φ L s).size, ∃ p ∈ (factsOf L s R j).1, Q _ ((Φ L s).ctx j) p.1 p.2 := by
  obtain ⟨j, e⟩ := Φ.exists_member hn hΓ
  rw [Sigma.mk.inj_iff] at e
  obtain ⟨h1, h2⟩ := e
  subst h1
  have h2 := eq_of_heq h2
  subst h2
  exact ⟨j, (A, B), hAB, hQ⟩

/-! ### The checks on codes -/

/-- Whether a type code is in `ext` of the types of size at most `s`. -/
def extC (s b : ℕ) : Bool :=
  decide (sizeC b ≤ s) ||
    (decide (tyTag b = 3) && decide (tyArg₂ b = 0) && decide (sizeC (tyArg₁ b) ≤ s))

theorem extC_code {s n : ℕ} (B : Ty n) : extC s B.code = true ↔ B ∈ ext (tysUpTo n s) := by
  simp only [extC, ext, Finset.mem_union, Finset.mem_image, mem_tysUpTo, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, sizeC_code]
  apply or_congr Iff.rfl
  cases B with
  | bnd L H =>
    simp only [Ty.code_bnd', tyTag_bndC, tyArg₂_bndC, tyArg₁_bndC, sizeC_code, Ty.code_eq_zero,
      Ty.bnd.injEq, true_and]
    constructor
    · rintro ⟨rfl, h⟩; exact ⟨L, h, rfl, rfl⟩
    · rintro ⟨P, h, rfl, rfl⟩; exact ⟨rfl, h⟩
  | _ => simp

/-- Whether the judgment `a <: b` of the context `g` is recorded in `R`. -/
def memB (s : ℕ) (R : List ℕ) (n g a b : ℕ) : Bool :=
  decide (sizeC a ≤ s) && extC s b && decide (bcodeC n g a b ∈ R)

/-- Whether the summary `(a, b)` of the context `g` is recorded in `R`. -/
def memS (s : ℕ) (R : List ℕ) (n g a b : ℕ) : Bool :=
  decide (sizeC a ≤ s) && decide (sizeC b ≤ s) && decide (scodeC n g a b ∈ R)

theorem memB_code {s : ℕ} {R : List ℕ} {n : ℕ} (Γ : Ctx n) (A B : Ty n) :
    memB s R n Γ.code A.code B.code = true ↔ (A, B) ∈ BofR s R Γ := by
  simp only [memB, Bool.and_eq_true, decide_eq_true_eq, sizeC_code, extC_code, mem_BofR,
    and_assoc]

theorem memS_code {s : ℕ} {R : List ℕ} {n : ℕ} (Γ : Ctx n) (A B : Ty n) :
    memS s R n Γ.code A.code B.code = true ↔ (A, B) ∈ SofR s R Γ := by
  simp only [memS, Bool.and_eq_true, decide_eq_true_eq, sizeC_code, mem_SofR, and_assoc]

/-- Whether some recorded summary `(a, r)` of the context `g` has `k r`. -/
def viaS (s : ℕ) (R : List ℕ) (n g a : ℕ) (k : ℕ → Bool) : Bool :=
  R.any fun e => validC n (jRight (Nat.unpair e).2) && memS s R n g a (jRight (Nat.unpair e).2) &&
    k (jRight (Nat.unpair e).2)

theorem viaS_code {s : ℕ} {R : List ℕ} {n : ℕ} (Γ : Ctx n) (A : Ty n) (k : ℕ → Bool) :
    viaS s R n Γ.code A.code k = true ↔ ∃ R' : Ty n, (A, R') ∈ SofR s R Γ ∧ k R'.code = true := by
  simp only [viaS, List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨e, -, ⟨hv, hm⟩, hk⟩
    obtain ⟨R', hR'⟩ := validC_iff.1 hv
    rw [← hR', memS_code] at hm
    rw [← hR'] at hk
    exact ⟨R', hm, hk⟩
  · rintro ⟨R', hm, hk⟩
    refine ⟨scodeC n Γ.code A.code R'.code, (mem_SofR.1 hm).2.2, ?_⟩
    simp only [scodeC, Nat.unpair_pair, jRight_mkJ]
    exact ⟨⟨validC_code R', (memS_code Γ A R').2 hm⟩, hk⟩

/-- The rules of `RuleB` on codes. -/
def ruleBaseC (s : ℕ) (R : List ℕ) (n g p w : ℕ) : Bool :=
  decide (w = 0) || (decide (p = 1) || ((decide (tyTag p = 2) && decide (p = w)) ||
  ((decide (tyTag p = 3) && decide (tyTag w = 3) && memB s R n g (tyArg₁ w) (tyArg₁ p) &&
    memB s R n g (tyArg₂ p) (tyArg₂ w)) ||
  ((decide (tyTag w = 2) && memB s R n g (lookupC g (tyArg₁ w)) (bndC p 0)) ||
  ((decide (tyTag p = 2) &&
    viaS s R n g (lookupC g (tyArg₁ p)) (fun r => memB s R n g r w)) ||
  ((List.range n).any fun x => memB s R n g (lookupC g x) (bndC p 0) &&
    viaS s R n g (lookupC g x) (fun r => memB s R n g r w)))))))

/-- The `∀` rule on codes: a recorded judgment `a <: b` of a bounded context `g''` of at most
`L` variables, mapped by a context morphism `fl : g'' → g, x:T` onto the bodies. -/
def allPremC (L s : ℕ) (R : List ℕ) (n g p w e : ℕ) : Bool :=
  decide ((Nat.unpair e).1 = 0) && jValidC (Nat.unpair e).2 &&
    decide (jScope (Nat.unpair e).2 ≤ L) &&
    ctxBoundedC s (jScope (Nat.unpair e).2) (jCtx (Nat.unpair e).2) &&
    memB s R (jScope (Nat.unpair e).2) (jCtx (Nat.unpair e).2) (jLeft (Nat.unpair e).2)
      (jRight (Nat.unpair e).2) &&
    (renListsC (jScope (Nat.unpair e).2) (n + 1)).any fun fl =>
      morphC (jCtx (Nat.unpair e).2) (jScope (Nat.unpair e).2) (pushC g (tyArg₁ p)) fl &&
        decide (renC fl (jLeft (Nat.unpair e).2) = tyArg₂ p) &&
        decide (renC fl (jRight (Nat.unpair e).2) = tyArg₂ w)

/-- The `∀` rule on codes. -/
def allCheckC (L s : ℕ) (R : List ℕ) (n g p w : ℕ) : Bool :=
  decide (tyTag p = 4) && decide (tyTag w = 4) && decide (tyArg₁ p = tyArg₁ w) &&
    R.any (allPremC L s R n g p w)

/-- The judgment rules on codes. -/
def ruleBC (L s : ℕ) (R : List ℕ) (n g p w : ℕ) : Bool :=
  ruleBaseC s R n g p w || allCheckC L s R n g p w

/-- The summary rules on codes. -/
def ruleSC (s : ℕ) (R : List ℕ) (n g p t : ℕ) : Bool :=
  (decide (tyTag p = 3) && decide (sizeC (tyArg₁ p) ≤ s) && decide (tyArg₂ p = t)) ||
  ((decide (p = 1) && decide (t = 1)) ||
  ((decide (tyTag p = 2) &&
    viaS s R n g (lookupC g (tyArg₁ p)) (fun r => memS s R n g r t)) ||
  ((List.range n).any fun x => memB s R n g (lookupC g x) (bndC p 0) &&
    viaS s R n g (lookupC g x) (fun r => memS s R n g r t))))

/-- The rule check: `c` codes a fact of the family `Φ L s` that follows from `R` by one rule. -/
def firesLS (L s : ℕ) (R : List ℕ) (c : ℕ) : Bool :=
  jValidC (Nat.unpair c).2 && decide (jScope (Nat.unpair c).2 ≤ L) &&
    ctxBoundedC s (jScope (Nat.unpair c).2) (jCtx (Nat.unpair c).2) &&
    decide (sizeC (jLeft (Nat.unpair c).2) ≤ s) &&
    ((decide ((Nat.unpair c).1 = 0) && extC s (jRight (Nat.unpair c).2) &&
        ruleBC L s R (jScope (Nat.unpair c).2) (jCtx (Nat.unpair c).2) (jLeft (Nat.unpair c).2)
          (jRight (Nat.unpair c).2)) ||
      (decide ((Nat.unpair c).1 = 1) && decide (sizeC (jRight (Nat.unpair c).2) ≤ s) &&
        ruleSC s R (jScope (Nat.unpair c).2) (jCtx (Nat.unpair c).2) (jLeft (Nat.unpair c).2)
          (jRight (Nat.unpair c).2)))

/-! ### Correctness of the checks -/

section Correct

variable {L s : ℕ} {R : List ℕ} {n : ℕ} (Γ : Ctx n)

/-- The two rules through a summary: a variable's type has a recorded summary `(Γ(y), R')`
followed by `Q R'`. -/
theorem viaS_lookup_code (y : BVar n) {k : ℕ → Bool} {Q : Ty n → Prop}
    (hk : ∀ R' : Ty n, k R'.code = true ↔ Q R') :
    viaS s R n Γ.code (lookupC Γ.code y.toNat) k = true ↔
      ∃ R' ∈ tysUpTo n s, (Γ.lookup y, R') ∈ SofR s R Γ ∧ Q R' := by
  rw [lookupC_code, viaS_code]
  constructor
  · rintro ⟨R', hm, hq⟩
    exact ⟨R', mem_tysUpTo.2 (mem_SofR.1 hm).2.1, hm, (hk R').1 hq⟩
  · rintro ⟨R', -, hm, hq⟩
    exact ⟨R', hm, (hk R').2 hq⟩

theorem upper_code (P : Ty n) {k : ℕ → Bool} {Q : Ty n → Prop}
    (hk : ∀ R' : Ty n, k R'.code = true ↔ Q R') :
    (decide (tyTag P.code = 2) &&
      viaS s R n Γ.code (lookupC Γ.code (tyArg₁ P.code)) k) = true ↔
      ∃ y ∈ BVar.list n, P = .sel y ∧
        ∃ R' ∈ tysUpTo n s, (Γ.lookup y, R') ∈ SofR s R Γ ∧ Q R' := by
  rw [Bool.and_eq_true, decide_eq_true_eq, tag_two]
  constructor
  · rintro ⟨⟨y, rfl⟩, h⟩
    rw [Ty.code_sel', tyArg₁_selC, viaS_lookup_code Γ y hk] at h
    exact ⟨y, BVar.mem_list y, rfl, h⟩
  · rintro ⟨y, -, rfl, h⟩
    rw [Ty.code_sel', tyArg₁_selC, viaS_lookup_code Γ y hk]
    exact ⟨⟨y, rfl⟩, h⟩

theorem bb_code (P : Ty n) {k : ℕ → Bool} {Q : Ty n → Prop}
    (hk : ∀ R' : Ty n, k R'.code = true ↔ Q R') :
    ((List.range n).any fun x => memB s R n Γ.code (lookupC Γ.code x) (bndC P.code 0) &&
      viaS s R n Γ.code (lookupC Γ.code x) k) = true ↔
      ∃ x ∈ BVar.list n, (Γ.lookup x, .bnd P .top) ∈ BofR s R Γ ∧
        ∃ R' ∈ tysUpTo n s, (Γ.lookup x, R') ∈ SofR s R Γ ∧ Q R' := by
  rw [List.any_eq_true, exists_range_iff]
  refine exists_congr fun x => and_congr Iff.rfl ?_
  rw [Bool.and_eq_true, viaS_lookup_code Γ x hk, lookupC_code, bndC_top, memB_code]

theorem ruleBaseC_code (P W : Ty n) :
    ruleBaseC s R n Γ.code P.code W.code = true ↔
      RuleB Γ (tysUpTo n s) (BofR s R Γ) (SofR s R Γ) P W := by
  have hk : ∀ R' : Ty n, memB s R n Γ.code R'.code W.code = true ↔ (R', W) ∈ BofR s R Γ :=
    fun R' => memB_code Γ R' W
  simp only [ruleBaseC, Bool.or_eq_true, RuleB]
  refine or_congr ?_ (or_congr ?_ (or_congr ?_ (or_congr ?_ (or_congr ?_
    (or_congr (upper_code Γ P hk) (bb_code Γ P hk))))))
  · rw [decide_eq_true_eq, Ty.code_eq_zero]
  · rw [decide_eq_true_eq, Ty.code_eq_one]
  · rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, tag_two,
      Ty.code_injective.eq_iff]
    constructor
    · rintro ⟨⟨x, rfl⟩, rfl⟩; exact ⟨x, BVar.mem_list x, rfl, rfl⟩
    · rintro ⟨x, -, rfl, rfl⟩; exact ⟨⟨x, rfl⟩, rfl⟩
  · simp only [Bool.and_eq_true, decide_eq_true_eq, BndRule.iff]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      obtain ⟨L', H, rfl⟩ := tag_three.1 h1
      obtain ⟨S₂, U₂, rfl⟩ := tag_three.1 h2
      simp only [Ty.code_bnd', tyArg₁_bndC, tyArg₂_bndC, memB_code] at h3 h4
      exact ⟨_, _, _, _, rfl, rfl, h3, h4⟩
    · rintro ⟨L', H, S₂, U₂, rfl, rfl, h3, h4⟩
      simp only [Ty.code_bnd', tyArg₁_bndC, tyArg₂_bndC, tyTag_bndC, memB_code]
      exact ⟨⟨⟨trivial, trivial⟩, h3⟩, h4⟩
  · rw [Bool.and_eq_true, decide_eq_true_eq, tag_two]
    constructor
    · rintro ⟨⟨x, rfl⟩, h⟩
      rw [Ty.code_sel', tyArg₁_selC, lookupC_code, bndC_top, memB_code] at h
      exact ⟨x, BVar.mem_list x, rfl, h⟩
    · rintro ⟨x, -, rfl, h⟩
      rw [Ty.code_sel', tyArg₁_selC, lookupC_code, bndC_top, memB_code]
      exact ⟨⟨x, rfl⟩, h⟩

theorem ruleSC_code (P T : Ty n) :
    ruleSC s R n Γ.code P.code T.code = true ↔ GRuleS s R Γ P T := by
  have hk : ∀ R' : Ty n, memS s R n Γ.code R'.code T.code = true ↔ (R', T) ∈ SofR s R Γ :=
    fun R' => memS_code Γ R' T
  simp only [ruleSC, Bool.or_eq_true, GRuleS, RuleS]
  refine or_congr ?_ (or_congr ?_ (or_congr (upper_code Γ P hk) (bb_code Γ P hk)))
  · simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      obtain ⟨L', H, rfl⟩ := tag_three.1 h1
      simp only [Ty.code_bnd', tyArg₁_bndC, tyArg₂_bndC, sizeC_code] at h2 h3
      exact ⟨L', mem_tysUpTo.2 h2, by rw [Ty.code_injective h3]⟩
    · rintro ⟨L', hL, rfl⟩
      simp only [Ty.code_bnd', tyArg₁_bndC, tyArg₂_bndC, tyTag_bndC, sizeC_code]
      exact ⟨⟨trivial, mem_tysUpTo.1 hL⟩, trivial⟩
  · rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, Ty.code_eq_one, Ty.code_eq_one]

theorem allCheckC_code (P W : Ty n) :
    allCheckC L s R n Γ.code P.code W.code = true ↔ AllRule (factsOf L s R) Γ P W := by
  rw [AllRule.iff]
  simp only [allCheckC, allPremC, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
  constructor
  · rintro ⟨⟨⟨h4p, h4w⟩, hT⟩, e, he, ⟨⟨⟨⟨h0, hv⟩, hL⟩, hb⟩, hm⟩, fl, hfl, ⟨hmor, e1⟩, e2⟩
    obtain ⟨T₁, B₁, rfl⟩ := tag_four.1 h4p
    obtain ⟨T₂, B₂, rfl⟩ := tag_four.1 h4w
    simp only [Ty.code_all', tyArg₁_allC, tyArg₂_allC] at hT e1 e2 hmor
    have hT' : T₁ = T₂ := Ty.code_injective hT
    subst hT'
    obtain ⟨⟨Γ'', A, B⟩, hJ⟩ := jValidC_iff.1 hv
    rw [← hJ] at hL hb hm hfl hmor e1 e2
    simp only [Judgment.code_eq, jScope_mkJ, jCtx_mkJ, jLeft_mkJ, jRight_mkJ] at hL hb hm hfl hmor e1 e2
    rw [ctxBoundedC_code] at hb
    rw [memB_code] at hm
    obtain ⟨f, rfl⟩ := mem_renListsC_iff.1 hfl
    rw [show pushC Γ.code T₁.code = (Γ.push T₁).code from rfl, morphC_iff] at hmor
    rw [renC_code] at e1 e2
    refine ⟨T₁, B₁, B₂, rfl, rfl, ?_⟩
    exact exists_member_fact hL hb hm
      (fun k Γ'' A B => ∃ f : Rename k (n + 1), f.IsCtxMorph Γ'' (Γ.push T₁) ∧
        A.rename f = B₁ ∧ B.rename f = B₂)
      ⟨f, hmor, Ty.code_injective e1, Ty.code_injective e2⟩
  · rintro ⟨T, B₁, B₂, rfl, rfl, j, p, hp, f, hf, e1, e2⟩
    simp only [Ty.code_all', tyArg₁_allC, tyArg₂_allC, tyTag_allC]
    obtain ⟨hdim, hbnd⟩ := Φ.member_bounds L s j
    refine ⟨⟨⟨trivial, trivial⟩, trivial⟩, bcodeC _ ((Φ L s).ctx j).code p.1.code p.2.code,
      (mem_BofR.1 hp).2.2, ?_⟩
    simp only [bcodeC, Nat.unpair_pair, jScope_mkJ, jCtx_mkJ, jLeft_mkJ, jRight_mkJ]
    refine ⟨⟨⟨⟨⟨trivial, jValidC_code ⟨(Φ L s).ctx j, p.1, p.2⟩⟩, hdim⟩,
      (ctxBoundedC_code _).2 hbnd⟩, (memB_code _ p.1 p.2).2 hp⟩, f.toList,
      mem_renListsC_iff.2 ⟨f, rfl⟩, ⟨?_, ?_⟩, ?_⟩
    · rw [show pushC Γ.code T.code = (Γ.push T).code from rfl, morphC_iff]; exact hf
    · rw [renC_code, e1]
    · rw [renC_code, e2]

theorem ruleBC_code (P W : Ty n) :
    ruleBC L s R n Γ.code P.code W.code = true ↔ GRuleB L s R Γ P W := by
  rw [ruleBC, Bool.or_eq_true, ruleBaseC_code, allCheckC_code]; rfl

end Correct

/-- The check on the code of a judgment. -/
theorem firesLS_bcode {L s : ℕ} {R : List ℕ} {n : ℕ} (Γ : Ctx n) (P W : Ty n) :
    firesLS L s R (bcodeC n Γ.code P.code W.code) = true ↔
      n ≤ L ∧ Γ.Bounded s ∧ P.size ≤ s ∧ W ∈ ext (tysUpTo n s) ∧ GRuleB L s R Γ P W := by
  have hv : jValidC (mkJ n Γ.code P.code W.code) = true := jValidC_code ⟨Γ, P, W⟩
  simp only [firesLS, bcodeC, Nat.unpair_pair, jScope_mkJ, jCtx_mkJ, jLeft_mkJ, jRight_mkJ, hv,
    Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, ctxBoundedC_code, sizeC_code,
    extC_code, ruleBC_code, true_and, zero_ne_one, false_and, or_false]
  tauto

/-- The check on the code of a summary. -/
theorem firesLS_scode {L s : ℕ} {R : List ℕ} {n : ℕ} (Γ : Ctx n) (P T : Ty n) :
    firesLS L s R (scodeC n Γ.code P.code T.code) = true ↔
      n ≤ L ∧ Γ.Bounded s ∧ P.size ≤ s ∧ T.size ≤ s ∧ GRuleS s R Γ P T := by
  have hv : jValidC (mkJ n Γ.code P.code T.code) = true := jValidC_code ⟨Γ, P, T⟩
  simp only [firesLS, scodeC, Nat.unpair_pair, jScope_mkJ, jCtx_mkJ, jLeft_mkJ, jRight_mkJ, hv,
    Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, ctxBoundedC_code, sizeC_code,
    ruleSC_code, true_and, one_ne_zero, false_and, false_or]
  tauto

/-- Only codes of judgments and summaries fire. -/
theorem firesLS_cases {L s : ℕ} {R : List ℕ} {c : ℕ} (h : firesLS L s R c = true) :
    ∃ (n : ℕ) (Γ : Ctx n) (P W : Ty n),
      c = bcodeC n Γ.code P.code W.code ∨ c = scodeC n Γ.code P.code W.code := by
  simp only [firesLS, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hv, -⟩, -⟩, -⟩, h⟩ := h
  obtain ⟨⟨Γ, P, W⟩, hJ⟩ := jValidC_iff.1 hv
  refine ⟨_, Γ, P, W, ?_⟩
  have hc := (Nat.pair_unpair c).symm
  rw [← hJ, Judgment.code_eq] at hc
  rcases h with ⟨⟨h0, -⟩, -⟩ | ⟨⟨h1, -⟩, -⟩
  · left; rw [hc, h0]; rfl
  · right; rw [hc, h1]; rfl

theorem firesLS_mono {L s : ℕ} {R R' : List ℕ} (h : ∀ x ∈ R, x ∈ R') {c : ℕ}
    (hf : firesLS L s R c = true) : firesLS L s R' c = true := by
  obtain ⟨n, Γ, P, W, rfl | rfl⟩ := firesLS_cases hf
  · rw [firesLS_bcode] at hf ⊢
    exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.mono h⟩
  · rw [firesLS_scode] at hf ⊢
    exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.mono h⟩

end Dsub
