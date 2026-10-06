import Resolution.PrimCodes
import Resolution.PrimFix

/-!
# Codes of contexts and judgments

`tailC`/`headC` take a context code apart, `pushC` builds one, `lookupC g x` is the code of
`Γ.lookup x` when `g = Γ.code`, `ctxValidC n g` decides whether `g` is the code of a context of
scope `n`, and `morphC g'' n'' g' fl` decides whether the renaming with list `fl` is a context
morphism from the context with code `g''` (scope `n''`) to the one with code `g'`. Judgment
codes are taken apart by `jScope`, `jCtx`, `jLeft`, `jRight` and checked by `jValidC`. Type
codes are taken apart by `tyTag`, `tyArg₁`, `tyArg₂`. All are primitive recursive.
-/

namespace Dsub

/-! ### Contexts -/

/-- The code of the context without its last entry. -/
def tailC (g : ℕ) : ℕ := (Nat.unpair (g - 1)).1

/-- The code of the last entry of a context. -/
def headC (g : ℕ) : ℕ := (Nat.unpair (g - 1)).2

/-- The code of `Γ.push T`. -/
def pushC (g t : ℕ) : ℕ := Nat.pair g t + 1

@[simp] theorem Ctx.code_push {n : ℕ} (Γ : Ctx n) (T : Ty n) :
    (Γ.push T).code = pushC Γ.code T.code := rfl

@[simp] theorem tailC_pushC (g t : ℕ) : tailC (pushC g t) = g := by
  simp [tailC, pushC]

@[simp] theorem headC_pushC (g t : ℕ) : headC (pushC g t) = t := by
  simp [headC, pushC]

/-- The code of the type of variable `x`, weakened into the scope of the whole context. -/
def lookupC (g x : ℕ) : ℕ := weakenC^[x + 1] (headC (tailC^[x] g))

theorem lookupC_code {n : ℕ} (Γ : Ctx n) (x : BVar n) :
    lookupC Γ.code x.toNat = (Γ.lookup x).code := by
  induction Γ with
  | empty => cases x
  | push Γ T ih =>
    cases x with
    | here => simp [lookupC, BVar.toNat, weakenC_code]
    | there x =>
      show weakenC^[x.toNat + 1 + 1] (headC (tailC^[x.toNat + 1] (pushC Γ.code T.code))) = _
      rw [Function.iterate_succ_apply' weakenC (x.toNat + 1), Function.iterate_succ_apply tailC,
        tailC_pushC]
      change weakenC (lookupC Γ.code x.toNat) = _
      rw [ih, weakenC_code]; rfl

/-- `g` is the code of a context of scope `n`, as a proposition. -/
def CtxOK (n g : ℕ) : Prop :=
  tailC^[n] g = 0 ∧ ∀ i < n, tailC^[i] g ≠ 0 ∧ needC (headC (tailC^[i] g)) ≤ n - 1 - i

instance (n g : ℕ) : Decidable (CtxOK n g) := by unfold CtxOK; infer_instance

theorem CtxOK_zero {g : ℕ} : CtxOK 0 g ↔ g = 0 := by simp [CtxOK]

theorem CtxOK_succ {n g : ℕ} :
    CtxOK (n + 1) g ↔ g ≠ 0 ∧ needC (headC g) ≤ n ∧ CtxOK n (tailC g) := by
  simp only [CtxOK, Function.iterate_succ_apply]
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨(h 0 (by omega)).1, by simpa using (h 0 (by omega)).2, h0, fun i hi => ?_⟩
    have := h (i + 1) (by omega)
    simp only [Function.iterate_succ_apply] at this
    exact ⟨this.1, by omega⟩
  · rintro ⟨hg, hh, h0, h⟩
    refine ⟨h0, fun i hi => ?_⟩
    cases i with
    | zero => exact ⟨hg, by simpa using hh⟩
    | succ i =>
      simp only [Function.iterate_succ_apply]
      have := h i (by omega)
      exact ⟨this.1, by omega⟩

theorem Ctx.decode_isSome_iff : ∀ (n g : ℕ), (Ctx.decode n g).isSome ↔ CtxOK n g
  | 0, 0 => by simp [Ctx.decode, CtxOK_zero]
  | 0, _ + 1 => by simp [Ctx.decode, CtxOK_zero]
  | _ + 1, 0 => by simp [Ctx.decode, CtxOK_succ]
  | n + 1, g + 1 => by
    rw [CtxOK_succ, Ctx.decode]
    have h1 := Ctx.decode_isSome_iff n (Nat.unpair g).1
    have h2 := Ty.decode_isSome_iff (Nat.unpair g).2 n
    simp only [headC, tailC, Nat.add_sub_cancel] at h1 h2 ⊢
    rw [← h1, ← h2]
    cases Ctx.decode n (Nat.unpair g).1 <;> cases Ty.decode n (Nat.unpair g).2 <;> simp

theorem Ctx.code_of_decode : ∀ {n g : ℕ} {Γ : Ctx n}, Ctx.decode n g = some Γ → Γ.code = g
  | 0, 0, Γ, h => by simp only [Ctx.decode, Option.some.injEq] at h; subst h; rfl
  | 0, _ + 1, _, h => by simp [Ctx.decode] at h
  | _ + 1, 0, _, h => by simp [Ctx.decode] at h
  | n + 1, g + 1, Γ, h => by
    simp only [Ctx.decode, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨Δ, hΔ, T, hT, rfl⟩ := h
    rw [Ctx.code_push, Ctx.code_of_decode hΔ, Ty.code_of_decode _ hT, pushC, Nat.pair_unpair]

theorem Ctx.decode_eq_some_iff {n g : ℕ} {Γ : Ctx n} : Ctx.decode n g = some Γ ↔ Γ.code = g :=
  ⟨Ctx.code_of_decode, fun h => h ▸ Ctx.decode_code Γ⟩

/-- Whether `g` is the code of a context of scope `n`. -/
def ctxValidC (n g : ℕ) : Bool := decide (CtxOK n g)

theorem ctxValidC_iff {n g : ℕ} : ctxValidC n g = true ↔ ∃ Γ : Ctx n, Γ.code = g := by
  rw [ctxValidC, decide_eq_true_iff, ← Ctx.decode_isSome_iff, Option.isSome_iff_exists]
  simp only [Ctx.decode_eq_some_iff]

theorem ctxValidC_code {n : ℕ} (Γ : Ctx n) : ctxValidC n Γ.code = true :=
  ctxValidC_iff.2 ⟨Γ, rfl⟩

/-! ### Context morphisms -/

/-- Whether the renaming with list `fl` maps the context with code `g''` and scope `n''` into
the context with code `g'`: `Γ'(f x) = Γ''(x)[f]` for every `x`. -/
def morphC (g'' n'' g' : ℕ) (fl : List ℕ) : Bool :=
  (List.range n'').all fun i => lookupC g' (fl.getD i 0) == renC fl (lookupC g'' i)

theorem morphC_iff {n'' n' : ℕ} (Γ'' : Ctx n'') (Γ' : Ctx n') (f : Rename n'' n') :
    morphC Γ''.code n'' Γ'.code f.toList = true ↔ f.IsCtxMorph Γ'' Γ' := by
  have key : ∀ x : BVar n'',
      (lookupC Γ'.code (f.toList.getD x.toNat 0) == renC f.toList (lookupC Γ''.code x.toNat))
        = true ↔ Γ'.lookup (f.var x) = (Γ''.lookup x).rename f := by
    intro x
    rw [Rename.toList_getD, lookupC_code, lookupC_code, renC_code, beq_iff_eq]
    exact Ty.code_injective.eq_iff
  simp only [morphC, List.all_eq_true, List.mem_range, Rename.IsCtxMorph]
  constructor
  · intro h x
    exact (key x).1 (h _ x.toNat_lt)
  · intro h i hi
    have := (key (BVar.ofLt n'' i hi)).2 (h _)
    rwa [BVar.toNat_ofLt] at this

/-! ### Judgments -/

/-- The code of a judgment from the codes of its parts. -/
def mkJ (n g s u : ℕ) : ℕ := Nat.pair n (Nat.pair g (Nat.pair s u))

/-- The scope of a judgment code. -/
def jScope (m : ℕ) : ℕ := (Nat.unpair m).1
/-- The context code of a judgment code. -/
def jCtx (m : ℕ) : ℕ := (Nat.unpair (Nat.unpair m).2).1
/-- The code of the left type of a judgment code. -/
def jLeft (m : ℕ) : ℕ := (Nat.unpair (Nat.unpair (Nat.unpair m).2).2).1
/-- The code of the right type of a judgment code. -/
def jRight (m : ℕ) : ℕ := (Nat.unpair (Nat.unpair (Nat.unpair m).2).2).2

theorem Judgment.code_eq (j : Judgment) : j.code = mkJ j.n j.Γ.code j.S.code j.U.code := rfl

@[simp] theorem jScope_mkJ (n g s u : ℕ) : jScope (mkJ n g s u) = n := by simp [jScope, mkJ]
@[simp] theorem jCtx_mkJ (n g s u : ℕ) : jCtx (mkJ n g s u) = g := by simp [jCtx, mkJ]
@[simp] theorem jLeft_mkJ (n g s u : ℕ) : jLeft (mkJ n g s u) = s := by simp [jLeft, mkJ]
@[simp] theorem jRight_mkJ (n g s u : ℕ) : jRight (mkJ n g s u) = u := by simp [jRight, mkJ]

theorem mkJ_parts (m : ℕ) : mkJ (jScope m) (jCtx m) (jLeft m) (jRight m) = m := by
  simp [mkJ, jScope, jCtx, jLeft, jRight, Nat.pair_unpair]

theorem Judgment.code_injective : Function.Injective Judgment.code := by
  intro j k h
  have := Judgment.decode_code j
  rw [h, Judgment.decode_code] at this
  exact (Option.some.inj this).symm

/-- Whether `m` is the code of a judgment. -/
def jValidC (m : ℕ) : Bool :=
  ctxValidC (jScope m) (jCtx m) && validC (jScope m) (jLeft m) && validC (jScope m) (jRight m)

theorem jValidC_code (j : Judgment) : jValidC j.code = true := by
  rw [jValidC, Judgment.code_eq, jScope_mkJ, jCtx_mkJ, jLeft_mkJ, jRight_mkJ, ctxValidC_code,
    validC_code, validC_code]; rfl

theorem jValidC_iff {m : ℕ} : jValidC m = true ↔ ∃ j : Judgment, j.code = m := by
  constructor
  · simp only [jValidC, Bool.and_eq_true, ctxValidC_iff, validC_iff]
    rintro ⟨⟨⟨Γ, hΓ⟩, ⟨S, hS⟩⟩, ⟨U, hU⟩⟩
    exact ⟨⟨Γ, S, U⟩, by rw [Judgment.code_eq]; simp only [hΓ, hS, hU]; exact mkJ_parts m⟩
  · rintro ⟨j, rfl⟩
    exact jValidC_code j

theorem jValidC_of_decode_isSome {m : ℕ} (h : (Judgment.decode m).isSome) : jValidC m = true := by
  simp only [jValidC, Bool.and_eq_true, ctxValidC, validC, decide_eq_true_eq,
    ← Ctx.decode_isSome_iff, ← Ty.decode_isSome_iff]
  unfold Judgment.decode Judgment.decodeAt at h
  unfold jScope jCtx jLeft jRight
  revert h
  cases Ctx.decode (Nat.unpair m).1 (Nat.unpair (Nat.unpair m).2).1 <;>
    cases Ty.decode (Nat.unpair m).1 (Nat.unpair (Nat.unpair (Nat.unpair m).2).2).1 <;>
    cases Ty.decode (Nat.unpair m).1 (Nat.unpair (Nat.unpair (Nat.unpair m).2).2).2 <;> simp

theorem Judgment.code_of_decode {m : ℕ} {j : Judgment} (h : Judgment.decode m = some j) :
    j.code = m := by
  obtain ⟨k, rfl⟩ := jValidC_iff.1 (jValidC_of_decode_isSome (m := m) (by simp [h]))
  rw [Judgment.decode_code, Option.some.injEq] at h
  rw [h]

theorem Judgment.decode_eq_some_iff {m : ℕ} {j : Judgment} :
    Judgment.decode m = some j ↔ j.code = m :=
  ⟨Judgment.code_of_decode, fun h => h ▸ Judgment.decode_code j⟩

/-! ### Type codes taken apart -/

/-- The constructor of a type code: `0` top, `1` bot, `2` sel, `3` bnd, `4` all. -/
def tyTag (c : ℕ) : ℕ := if c < 2 then c else (c - 2) % 3 + 2
/-- The variable index of a `sel` code, and the first component of a `bnd` or `all` code. -/
def tyArg₁ (c : ℕ) : ℕ := if (c - 2) % 3 = 0 then (c - 2) / 3 else (Nat.unpair ((c - 2) / 3)).1
/-- The second component of a `bnd` or `all` code. -/
def tyArg₂ (c : ℕ) : ℕ := (Nat.unpair ((c - 2) / 3)).2

/-- The code of `bnd` from the codes of its parts. -/
def bndC (s u : ℕ) : ℕ := 3 * Nat.pair s u + 3
/-- The code of `all` from the codes of its parts. -/
def allC (s t : ℕ) : ℕ := 3 * Nat.pair s t + 4
/-- The code of `sel` from the index of its variable. -/
def selC (x : ℕ) : ℕ := 3 * x + 2

@[simp] theorem Ty.code_top' {n : ℕ} : (Ty.top : Ty n).code = 0 := rfl
@[simp] theorem Ty.code_bot' {n : ℕ} : (Ty.bot : Ty n).code = 1 := rfl
@[simp] theorem Ty.code_sel' {n : ℕ} (x : BVar n) : (Ty.sel x).code = selC x.toNat := rfl
@[simp] theorem Ty.code_bnd' {n : ℕ} (S U : Ty n) :
    (Ty.bnd S U).code = bndC S.code U.code := rfl
@[simp] theorem Ty.code_all' {n : ℕ} (S : Ty n) (T : Ty (n + 1)) :
    (Ty.all S T).code = allC S.code T.code := rfl

@[simp] theorem tyTag_selC (x : ℕ) : tyTag (selC x) = 2 := by simp [tyTag, selC]
@[simp] theorem tyTag_bndC (s u : ℕ) : tyTag (bndC s u) = 3 := by simp [tyTag, bndC]
@[simp] theorem tyTag_allC (s t : ℕ) : tyTag (allC s t) = 4 := by simp [tyTag, allC]
@[simp] theorem tyArg₁_selC (x : ℕ) : tyArg₁ (selC x) = x := by simp [tyArg₁, selC]
@[simp] theorem tyArg₁_bndC (s u : ℕ) : tyArg₁ (bndC s u) = s := by
  simp [tyArg₁, bndC, show (3 * Nat.pair s u + 1) / 3 = Nat.pair s u by omega]
@[simp] theorem tyArg₂_bndC (s u : ℕ) : tyArg₂ (bndC s u) = u := by
  simp [tyArg₂, bndC, show (3 * Nat.pair s u + 1) / 3 = Nat.pair s u by omega]
@[simp] theorem tyArg₁_allC (s t : ℕ) : tyArg₁ (allC s t) = s := by
  simp [tyArg₁, allC, show (3 * Nat.pair s t + 2) / 3 = Nat.pair s t by omega]
@[simp] theorem tyArg₂_allC (s t : ℕ) : tyArg₂ (allC s t) = t := by
  simp [tyArg₂, allC, show (3 * Nat.pair s t + 2) / 3 = Nat.pair s t by omega]

/-! ### Primitive recursion -/

open Primrec

theorem tailC_primrec : Primrec tailC := fst.comp (unpair.comp (nat_sub.comp .id (const 1)))
theorem headC_primrec : Primrec headC := snd.comp (unpair.comp (nat_sub.comp .id (const 1)))
theorem pushC_primrec : Primrec₂ pushC := succ.comp₂ Primrec₂.natPair

theorem lookupC_primrec : Primrec₂ lookupC := by
  have h1 : Primrec₂ fun g x : ℕ => tailC^[x] g :=
    (nat_iterate snd fst (tailC_primrec.comp snd).to₂).to₂
  exact (nat_iterate (succ.comp snd) (headC_primrec.comp h1) (weakenC_primrec.comp snd).to₂).to₂

theorem ctxValidC_primrec : Primrec₂ ctxValidC := by
  have hit : Primrec₂ fun g x : ℕ => tailC^[x] g :=
    (nat_iterate snd fst (tailC_primrec.comp snd).to₂).to₂
  have hall : Primrec fun p : ℕ × ℕ =>
      (List.range p.1).all fun i =>
        !(tailC^[i] p.2 == 0) && validC (p.1 - 1 - i) (headC (tailC^[i] p.2)) :=
    PR.list_all (list_range.comp fst)
      (Primrec.and.comp (Primrec.not.comp (Primrec.beq.comp (hit.comp (snd.comp fst) snd)
        (const 0)))
        (validC_primrec.comp (nat_sub.comp (nat_sub.comp (fst.comp fst) (const 1)) snd)
          (headC_primrec.comp (hit.comp (snd.comp fst) snd)))).to₂
  refine (Primrec.and.comp (Primrec.beq.comp (hit.comp snd fst) (const 0)) hall).of_eq
    fun p => ?_
  rw [Bool.eq_iff_iff]
  simp only [ctxValidC, CtxOK, validC, Bool.and_eq_true, beq_iff_eq,
    List.all_eq_true, List.mem_range, Bool.not_eq_true', beq_eq_false_iff_ne, decide_eq_true_eq]
  exact decide_eq_true_iff.symm

theorem morphC_primrec :
    Primrec fun p : ℕ × ℕ × ℕ × List ℕ => morphC p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  let P := ℕ × ℕ × ℕ × List ℕ
  have hg'' : Primrec fun q : P × ℕ => q.1.1 := fst.comp fst
  have hg' : Primrec fun q : P × ℕ => q.1.2.2.1 := fst.comp (snd.comp (snd.comp fst))
  have hfl : Primrec fun q : P × ℕ => q.1.2.2.2 := snd.comp (snd.comp (snd.comp fst))
  exact PR.list_all (list_range.comp (fst.comp snd))
    (Primrec.beq.comp (lookupC_primrec.comp hg' ((list_getD 0).comp hfl snd))
      (renC_primrec.comp hfl (lookupC_primrec.comp hg'' snd))).to₂

theorem mkJ_primrec : Primrec fun p : ℕ × ℕ × ℕ × ℕ => mkJ p.1 p.2.1 p.2.2.1 p.2.2.2 :=
  Primrec₂.natPair.comp fst (Primrec₂.natPair.comp (fst.comp snd)
    (Primrec₂.natPair.comp (fst.comp (snd.comp snd)) (snd.comp (snd.comp snd))))

theorem jScope_primrec : Primrec jScope := fst.comp unpair
theorem jCtx_primrec : Primrec jCtx := fst.comp (unpair.comp (snd.comp unpair))
theorem jLeft_primrec : Primrec jLeft :=
  fst.comp (unpair.comp (snd.comp (unpair.comp (snd.comp unpair))))
theorem jRight_primrec : Primrec jRight :=
  snd.comp (unpair.comp (snd.comp (unpair.comp (snd.comp unpair))))

theorem jValidC_primrec : Primrec jValidC :=
  Primrec.and.comp (Primrec.and.comp (ctxValidC_primrec.comp jScope_primrec jCtx_primrec)
    (validC_primrec.comp jScope_primrec jLeft_primrec))
    (validC_primrec.comp jScope_primrec jRight_primrec)

theorem tyTag_primrec : Primrec tyTag :=
  Primrec.ite (nat_lt.comp .id (const 2)) .id
    (nat_add.comp (nat_mod.comp (nat_sub.comp .id (const 2)) (const 3)) (const 2))

theorem tyArg₁_primrec : Primrec tyArg₁ :=
  Primrec.ite (Primrec.eq.comp (nat_mod.comp (nat_sub.comp .id (const 2)) (const 3)) (const 0))
    (nat_div.comp (nat_sub.comp .id (const 2)) (const 3))
    (fst.comp (unpair.comp (nat_div.comp (nat_sub.comp .id (const 2)) (const 3))))

theorem tyArg₂_primrec : Primrec tyArg₂ :=
  snd.comp (unpair.comp (nat_div.comp (nat_sub.comp .id (const 2)) (const 3)))

theorem bndC_primrec : Primrec₂ bndC :=
  nat_add.comp (nat_mul.comp (const 3) Primrec₂.natPair) (const 3)
/-! ### Decision procedures -/

/-- A predicate decided by a primitive recursive Boolean function is computable. -/
theorem computablePred_of_primrec {p : ℕ → Prop} {f : ℕ → Bool} (hf : Primrec f)
    (h : ∀ m, p m ↔ f m = true) : ComputablePred p :=
  ComputablePred.computable_iff.2 ⟨f, hf.to_comp, funext fun m => propext (h m)⟩

end Dsub
