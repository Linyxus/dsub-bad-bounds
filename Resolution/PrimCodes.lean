import Dsub
import Resolution.Syntax
import Resolution.PrimBasic

/-!
# Codes of variables and types

`needC c` is the least scope in which the code `c` names a type (every code names a type in
a large enough scope), so `validC n c = decide (needC c ≤ n)` decides whether `c` is the code
of a type of scope `n`. `renSC fl s c` renames the type with code `c` by the map
`i ↦ fl.getD i (i + s)` on variable indices, lifted under binders; `renC fl` is the case of a
list of images `fl` and `weakenC` the case of `Rename.succ`. All are primitive recursive.
-/

namespace Dsub

/-! ### Variables -/

theorem BVar.toNat_lt : ∀ {n : ℕ} (x : BVar n), x.toNat < n
  | _, .here => Nat.succ_pos _
  | _, .there x => Nat.succ_lt_succ (BVar.toNat_lt x)

theorem BVar.toNat_injective {n : ℕ} : Function.Injective (BVar.toNat (n := n)) := by
  intro x y h
  have := BVar.ofNat_toNat x
  rw [h, BVar.ofNat_toNat] at this
  exact (Option.some.inj this).symm

/-- The variable with a given index below the scope. -/
def BVar.ofLt : (n i : ℕ) → i < n → BVar n
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _ => .here
  | n + 1, i + 1, h => .there (BVar.ofLt n i (Nat.lt_of_succ_lt_succ h))

@[simp] theorem BVar.toNat_ofLt : ∀ (n i : ℕ) (h : i < n), (BVar.ofLt n i h).toNat = i
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _ => rfl
  | n + 1, i + 1, h => by
    simp only [BVar.ofLt, BVar.toNat, BVar.toNat_ofLt n i]

@[simp] theorem BVar.ofLt_toNat {n : ℕ} (x : BVar n) : BVar.ofLt n x.toNat x.toNat_lt = x :=
  BVar.toNat_injective (BVar.toNat_ofLt _ _ _)

theorem BVar.ofNat_isSome : ∀ (n i : ℕ), (BVar.ofNat n i).isSome ↔ i < n
  | 0, _ => by simp [BVar.ofNat]
  | _ + 1, 0 => by simp [BVar.ofNat]
  | n + 1, i + 1 => by simp [BVar.ofNat, BVar.ofNat_isSome n i]

theorem BVar.toNat_of_ofNat : ∀ {n i : ℕ} {x : BVar n}, BVar.ofNat n i = some x → x.toNat = i
  | 0, _, _, h => by simp [BVar.ofNat] at h
  | _ + 1, 0, x, h => by simp only [BVar.ofNat, Option.some.injEq] at h; subst h; rfl
  | n + 1, i + 1, x, h => by
    simp only [BVar.ofNat, Option.map_eq_some_iff] at h
    obtain ⟨y, hy, rfl⟩ := h
    simp [BVar.toNat, BVar.toNat_of_ofNat hy]

/-! ### Codes of types -/

theorem Ty.code_injective {n : ℕ} : Function.Injective (Ty.code (n := n)) := by
  intro S T h
  have := Ty.decode_code S
  rw [h, Ty.decode_code] at this
  exact (Option.some.inj this).symm

theorem Ty.code_sel {n : ℕ} (x : BVar n) : (Ty.sel x).code = 3 * x.toNat + 2 := rfl
theorem Ty.code_bnd {n : ℕ} (S U : Ty n) :
    (Ty.bnd S U).code = 3 * Nat.pair S.code U.code + 3 := rfl
theorem Ty.code_all {n : ℕ} (S : Ty n) (T : Ty (n + 1)) :
    (Ty.all S T).code = 3 * Nat.pair S.code T.code + 4 := rfl

theorem unpair_fst_lt {m : ℕ} : (Nat.unpair (m / 3)).1 < m + 2 := by
  have := Nat.unpair_left_le (m / 3); omega

theorem unpair_snd_lt {m : ℕ} : (Nat.unpair (m / 3)).2 < m + 2 := by
  have := Nat.unpair_right_le (m / 3); omega

/-- The least scope in which a code names a type. -/
def needC : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | m + 2 =>
    if m % 3 = 0 then m / 3 + 1
    else if m % 3 = 1 then max (needC (Nat.unpair (m / 3)).1) (needC (Nat.unpair (m / 3)).2)
    else max (needC (Nat.unpair (m / 3)).1) (needC (Nat.unpair (m / 3)).2 - 1)
termination_by m => m
decreasing_by all_goals first | exact unpair_fst_lt | exact unpair_snd_lt

theorem Ty.decode_isSome_iff : ∀ (c n : ℕ), (Ty.decode n c).isSome ↔ needC c ≤ n := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  intro n
  match c with
  | 0 => rw [Ty.decode, needC]; simp
  | 1 => rw [Ty.decode, needC]; simp
  | m + 2 =>
    have ha := ih _ (unpair_fst_lt (m := m))
    have hb := ih _ (unpair_snd_lt (m := m))
    rw [Ty.decode, needC]
    split_ifs with h0 h1
    · simp [BVar.ofNat_isSome]; omega
    · rw [Nat.max_le, ← ha, ← hb]
      cases Ty.decode n (Nat.unpair (m / 3)).1 <;> cases Ty.decode n (Nat.unpair (m / 3)).2 <;>
        simp
    · have hb' := hb (n + 1)
      rw [Nat.max_le, ← ha, show needC (Nat.unpair (m / 3)).2 - 1 ≤ n ↔
        needC (Nat.unpair (m / 3)).2 ≤ n + 1 by omega, ← hb']
      cases Ty.decode n (Nat.unpair (m / 3)).1 <;>
        cases Ty.decode (n + 1) (Nat.unpair (m / 3)).2 <;> simp

theorem Ty.code_of_decode : ∀ (c : ℕ) {n : ℕ} {T : Ty n}, Ty.decode n c = some T → T.code = c := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  intro n T h
  match c with
  | 0 => rw [Ty.decode] at h; cases h; rfl
  | 1 => rw [Ty.decode] at h; cases h; rfl
  | m + 2 =>
    rw [Ty.decode] at h
    split_ifs at h with h0 h1
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨x, hx, rfl⟩ := h
      rw [Ty.code_sel, BVar.toNat_of_ofNat hx]; omega
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨S, hS, U, hU, rfl⟩ := h
      rw [Ty.code_bnd, ih _ unpair_fst_lt hS, ih _ unpair_snd_lt hU, Nat.pair_unpair]; omega
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨S, hS, U, hU, rfl⟩ := h
      rw [Ty.code_all, ih _ unpair_fst_lt hS, ih _ unpair_snd_lt hU, Nat.pair_unpair]; omega

theorem Ty.decode_eq_some_iff {n c : ℕ} {T : Ty n} : Ty.decode n c = some T ↔ T.code = c :=
  ⟨Ty.code_of_decode c, fun h => h ▸ Ty.decode_code T⟩

/-- Whether a code names a type of scope `n`. -/
def validC (n c : ℕ) : Bool := decide (needC c ≤ n)

theorem validC_iff {n c : ℕ} : validC n c = true ↔ ∃ T : Ty n, T.code = c := by
  rw [validC, decide_eq_true_iff, ← Ty.decode_isSome_iff, Option.isSome_iff_exists]
  simp only [Ty.decode_eq_some_iff]

theorem validC_code {n : ℕ} (T : Ty n) : validC n T.code = true := validC_iff.2 ⟨T, rfl⟩

/-! ### Renaming on codes -/

/-- The image of the variable index `i` under the map `i ↦ fl.getD i (i + s)` lifted under
`k` binders. -/
def renVar (fl : List ℕ) (s k i : ℕ) : ℕ :=
  if i < k then i else fl.getD (i - k) (i - k + s) + k

theorem renVar_zero_succ {fl : List ℕ} {s k : ℕ} : renVar fl s (k + 1) 0 = 0 := by
  simp [renVar]

theorem renVar_succ_succ {fl : List ℕ} {s k i : ℕ} :
    renVar fl s (k + 1) (i + 1) = renVar fl s k i + 1 := by
  unfold renVar
  by_cases h : i < k
  · simp [h]
  · simp only [h, ite_false, show ¬ i + 1 < k + 1 by omega, Nat.add_sub_add_right]; omega

/-- The table of a renaming at code `c`: entry `k` is the code of the renamed type under `k`
binders, for `k ≤ D`. -/
def renTab (fl : List ℕ) (s D : ℕ) : ℕ → List ℕ
  | 0 => (List.range (D + 1)).map fun _ => 0
  | 1 => (List.range (D + 1)).map fun _ => 1
  | m + 2 => (List.range (D + 1)).map fun k =>
    if m % 3 = 0 then 3 * renVar fl s k (m / 3) + 2
    else if m % 3 = 1 then
      3 * Nat.pair ((renTab fl s D (Nat.unpair (m / 3)).1).getD k 0)
        ((renTab fl s D (Nat.unpair (m / 3)).2).getD k 0) + 3
    else
      3 * Nat.pair ((renTab fl s D (Nat.unpair (m / 3)).1).getD k 0)
        ((renTab fl s D (Nat.unpair (m / 3)).2).getD (k + 1) 0) + 4
termination_by m => m
decreasing_by all_goals first | exact unpair_fst_lt | exact unpair_snd_lt

theorem renTab_spec {fl : List ℕ} {s D : ℕ} : ∀ {n m : ℕ} (T : Ty n) (f : Rename n m) (k : ℕ),
    (∀ x : BVar n, (f.var x).toNat = renVar fl s k x.toNat) → k + T.code ≤ D →
    (renTab fl s D T.code).getD k 0 = (T.rename f).code := by
  intro n m T
  induction T generalizing m with
  | top => intro f k _ hk; rw [Ty.code, renTab, getD_map_range _ _ (by omega)]; rfl
  | bot => intro f k _ hk; rw [Ty.code, renTab, getD_map_range _ _ (by omega)]; rfl
  | sel x =>
    intro f k hf hk
    rw [Ty.code_sel] at hk ⊢
    rw [renTab, getD_map_range _ _ (by omega)]
    simp only [Nat.mul_mod_right, ite_true, Nat.mul_div_cancel_left _ (by omega : 0 < 3),
      Ty.rename_sel, Ty.code_sel, hf]
  | bnd S U ihS ihU =>
    intro f k hf hk
    rw [Ty.code_bnd] at hk ⊢
    have hS := Nat.left_le_pair S.code U.code
    have hU := Nat.right_le_pair S.code U.code
    rw [show 3 * Nat.pair S.code U.code + 3 = (3 * Nat.pair S.code U.code + 1) + 2 by omega,
      renTab, getD_map_range _ _ (by omega)]
    have e1 : (3 * Nat.pair S.code U.code + 1) % 3 = 1 := by omega
    have e2 : (3 * Nat.pair S.code U.code + 1) / 3 = Nat.pair S.code U.code := by omega
    simp only [e1, e2, Nat.unpair_pair, show (1 : ℕ) ≠ 0 by omega, ite_false, ite_true,
      ihS f k hf (by omega), ihU f k hf (by omega), Ty.rename_bnd, Ty.code_bnd]
  | all S T ihS ihT =>
    intro f k hf hk
    rw [Ty.code_all] at hk ⊢
    have hS := Nat.left_le_pair S.code T.code
    have hT := Nat.right_le_pair S.code T.code
    rw [show 3 * Nat.pair S.code T.code + 4 = (3 * Nat.pair S.code T.code + 2) + 2 by omega,
      renTab, getD_map_range _ _ (by omega)]
    have e1 : (3 * Nat.pair S.code T.code + 2) % 3 = 2 := by omega
    have e2 : (3 * Nat.pair S.code T.code + 2) / 3 = Nat.pair S.code T.code := by omega
    have hf' : ∀ x : BVar (_ + 1), (f.lift.var x).toNat = renVar fl s (k + 1) x.toNat := by
      intro x
      cases x with
      | here => show 0 = renVar fl s (k + 1) 0; rw [renVar_zero_succ]
      | there x => rw [Rename.lift_there]; simp only [BVar.toNat, renVar_succ_succ, hf]
    simp only [e1, e2, Nat.unpair_pair, show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega,
      ite_false, ihS f k hf (by omega), ihT f.lift (k + 1) hf' (by omega), Ty.rename_all,
      Ty.code_all]

/-- Renaming on codes by the map `i ↦ fl.getD i (i + s)`. -/
def renSC (fl : List ℕ) (s c : ℕ) : ℕ := (renTab fl s c c).getD 0 0

theorem renSC_code {fl : List ℕ} {s : ℕ} {n m : ℕ} (T : Ty n) (f : Rename n m)
    (hf : ∀ x : BVar n, (f.var x).toNat = fl.getD x.toNat (x.toNat + s)) :
    renSC fl s T.code = (T.rename f).code :=
  renTab_spec T f 0 (fun x => by simp [renVar, hf]) (by omega)

/-- Renaming on codes by a list of images. -/
def renC (fl : List ℕ) (c : ℕ) : ℕ := renSC fl 0 c

/-- Weakening on codes. -/
def weakenC (c : ℕ) : ℕ := renSC [] 1 c

theorem weakenC_code {n : ℕ} (T : Ty n) : weakenC T.code = T.weaken.code :=
  renSC_code T Rename.succ fun x => by simp [BVar.toNat]

/-! ### Renamings as lists -/

/-- The list of the images of the variable indices `0, …, n - 1`. -/
def Rename.toList {n m : ℕ} (f : Rename n m) : List ℕ :=
  (List.range n).map fun i => if h : i < n then (f.var (BVar.ofLt n i h)).toNat else 0

@[simp] theorem Rename.length_toList {n m : ℕ} (f : Rename n m) : f.toList.length = n := by
  simp [Rename.toList]

theorem Rename.toList_getD {n m : ℕ} (f : Rename n m) (x : BVar n) (d : ℕ) :
    f.toList.getD x.toNat d = (f.var x).toNat := by
  rw [Rename.toList, getD_map_range _ _ x.toNat_lt, dif_pos x.toNat_lt, BVar.ofLt_toNat]

theorem Rename.toList_lt {n m : ℕ} (f : Rename n m) : ∀ i ∈ f.toList, i < m := by
  intro i hi
  simp only [Rename.toList, List.mem_map, List.mem_range] at hi
  obtain ⟨j, hj, rfl⟩ := hi
  rw [dif_pos hj]; exact BVar.toNat_lt _

theorem Rename.toList_injective {n m : ℕ} : Function.Injective (Rename.toList (n := n) (m := m)) := by
  intro f g h
  apply Rename.ext
  intro x
  apply BVar.toNat_injective
  rw [← Rename.toList_getD f x 0, ← Rename.toList_getD g x 0, h]

/-- The renaming with a given list of images. -/
def Rename.ofList {n m : ℕ} (l : List ℕ) (h : ∀ i < n, l.getD i 0 < m) : Rename n m where
  var x := BVar.ofLt m (l.getD x.toNat 0) (h _ x.toNat_lt)

@[simp] theorem Rename.ofList_var_toNat {n m : ℕ} (l : List ℕ) (h : ∀ i < n, l.getD i 0 < m)
    (x : BVar n) : ((Rename.ofList l h).var x).toNat = l.getD x.toNat 0 := by
  simp [Rename.ofList]

theorem Rename.toList_ofList {n m : ℕ} (l : List ℕ) (h : ∀ i < n, l.getD i 0 < m)
    (hl : l.length = n) : (Rename.ofList l h).toList = l := by
  apply List.ext_getElem (by simp [hl])
  intro i h1 h2
  simp only [Rename.toList, List.getElem_map, List.getElem_range]
  rw [dif_pos (by simpa using h1), Rename.ofList_var_toNat, BVar.toNat_ofLt]
  simp [List.getD_eq_getElem?_getD, h2]

theorem Rename.ofList_toList {n m : ℕ} (f : Rename n m)
    (h : ∀ i < n, f.toList.getD i 0 < m) : Rename.ofList f.toList h = f :=
  Rename.toList_injective (Rename.toList_ofList _ _ (by simp))

theorem Rename.getD_lt_of_mem {n m : ℕ} {l : List ℕ} (hl : l.length = n)
    (hm : ∀ i ∈ l, i < m) : ∀ i < n, l.getD i 0 < m := by
  intro i hi
  have h2 : i < l.length := by omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]
  exact hm _ (List.getElem_mem _)

/-- A list is the list of a renaming from scope `n` to scope `m` iff it has `n` entries, each
below `m`. -/
theorem Rename.exists_toList_iff {n m : ℕ} {l : List ℕ} :
    (∃ f : Rename n m, f.toList = l) ↔ l.length = n ∧ ∀ i ∈ l, i < m := by
  constructor
  · rintro ⟨f, rfl⟩; exact ⟨by simp, f.toList_lt⟩
  · rintro ⟨hl, hm⟩
    exact ⟨Rename.ofList l (Rename.getD_lt_of_mem hl hm), Rename.toList_ofList _ _ hl⟩

theorem renC_code {n m : ℕ} (T : Ty n) (f : Rename n m) :
    renC f.toList T.code = (T.rename f).code :=
  renSC_code T f fun x => by rw [Rename.toList_getD]

/-- The lists of length `n` with entries below `m`: the lists of the renamings from scope `n`
to scope `m`. -/
def renListsC (n m : ℕ) : List (List ℕ) :=
  Nat.rec [[]] (fun _ L => L.flatMap fun l => (List.range m).map fun i => i :: l) n

theorem mem_renListsC {n m : ℕ} {l : List ℕ} :
    l ∈ renListsC n m ↔ l.length = n ∧ ∀ i ∈ l, i < m := by
  induction n generalizing l with
  | zero =>
    show l ∈ [[]] ↔ _
    simp only [List.mem_singleton, List.length_eq_zero_iff]
    exact ⟨fun h => ⟨h, by simp [h]⟩, fun h => h.1⟩
  | succ n ih =>
    simp only [renListsC] at ih ⊢
    simp only [List.mem_flatMap, List.mem_map, List.mem_range, ih]
    constructor
    · rintro ⟨l', ⟨hl, hm⟩, i, hi, rfl⟩
      refine ⟨by simp [hl], ?_⟩
      intro j hj
      rcases List.mem_cons.1 hj with rfl | hj
      · exact hi
      · exact hm j hj
    · intro ⟨hl, hm⟩
      match l, hl with
      | i :: l', hl =>
        exact ⟨l', ⟨by simpa using hl, fun j hj => hm j (List.mem_cons_of_mem _ hj)⟩, i,
          hm i List.mem_cons_self, rfl⟩

theorem mem_renListsC_iff {n m : ℕ} {l : List ℕ} :
    l ∈ renListsC n m ↔ ∃ f : Rename n m, f.toList = l := by
  rw [mem_renListsC, Rename.exists_toList_iff]

/-! ### Primitive recursion -/

open Primrec

/-- One step of `needC`, reading earlier values from a list. -/
def needStep (c : ℕ) (l : List ℕ) : ℕ :=
  if c < 2 then 0
  else if (c - 2) % 3 = 0 then (c - 2) / 3 + 1
  else if (c - 2) % 3 = 1 then
    max (l.getD (Nat.unpair ((c - 2) / 3)).1 0) (l.getD (Nat.unpair ((c - 2) / 3)).2 0)
  else max (l.getD (Nat.unpair ((c - 2) / 3)).1 0) (l.getD (Nat.unpair ((c - 2) / 3)).2 0 - 1)

theorem needStep_eq (c : ℕ) : needStep c ((List.range c).map needC) = needC c := by
  match c with
  | 0 => rw [needC]; rfl
  | 1 => rw [needC]; rfl
  | m + 2 =>
    have h2 : ¬ m + 2 < 2 := by omega
    rw [needC, needStep]
    simp only [h2, ↓reduceIte, Nat.add_sub_cancel, getD_map_range _ _ unpair_fst_lt,
      getD_map_range _ _ unpair_snd_lt]

theorem needStep_primrec : Primrec₂ needStep := by
  have hm : Primrec fun p : ℕ × List ℕ => p.1 - 2 := nat_sub.comp fst (const 2)
  have hq : Primrec fun p : ℕ × List ℕ => (p.1 - 2) / 3 := nat_div.comp hm (const 3)
  have hr : Primrec fun p : ℕ × List ℕ => (p.1 - 2) % 3 := nat_mod.comp hm (const 3)
  have ha : Primrec fun p : ℕ × List ℕ => p.2.getD (Nat.unpair ((p.1 - 2) / 3)).1 0 :=
    (list_getD 0).comp snd (fst.comp (unpair.comp hq))
  have hb : Primrec fun p : ℕ × List ℕ => p.2.getD (Nat.unpair ((p.1 - 2) / 3)).2 0 :=
    (list_getD 0).comp snd (snd.comp (unpair.comp hq))
  exact (Primrec.ite (nat_lt.comp fst (const 2)) (const 0)
    (Primrec.ite (Primrec.eq.comp hr (const 0)) (succ.comp hq)
      (Primrec.ite (Primrec.eq.comp hr (const 1)) (nat_max.comp ha hb)
        (nat_max.comp ha (nat_sub.comp hb (const 1)))))).of_eq fun _ => rfl

theorem needC_primrec : Primrec needC := by
  have := nat_strong_rec (fun (_ : Unit) c => needC c)
    (g := fun _ l => some (needStep l.length l))
    (option_some.comp (needStep_primrec.comp (list_length.comp snd) snd)).to₂
    (fun _ c => by simp [needStep_eq])
  exact this.comp (const ()) .id

theorem validC_primrec : Primrec₂ validC :=
  (nat_le.decide.comp (needC_primrec.comp snd) fst).of_eq fun _ => rfl

/-- One step of `renTab`, reading earlier tables from a list. -/
def renStep (fl : List ℕ) (s D c : ℕ) (l : List (List ℕ)) : List ℕ :=
  (List.range (D + 1)).map fun k =>
    if c < 2 then c
    else if (c - 2) % 3 = 0 then 3 * renVar fl s k ((c - 2) / 3) + 2
    else if (c - 2) % 3 = 1 then
      3 * Nat.pair ((l.getD (Nat.unpair ((c - 2) / 3)).1 []).getD k 0)
        ((l.getD (Nat.unpair ((c - 2) / 3)).2 []).getD k 0) + 3
    else
      3 * Nat.pair ((l.getD (Nat.unpair ((c - 2) / 3)).1 []).getD k 0)
        ((l.getD (Nat.unpair ((c - 2) / 3)).2 []).getD (k + 1) 0) + 4

theorem renStep_eq (fl : List ℕ) (s D c : ℕ) :
    renStep fl s D c ((List.range c).map (renTab fl s D)) = renTab fl s D c := by
  match c with
  | 0 => rw [renTab]; rfl
  | 1 => rw [renTab]; rfl
  | m + 2 =>
    have h2 : ¬ m + 2 < 2 := by omega
    rw [renTab, renStep]
    simp only [h2, ↓reduceIte, Nat.add_sub_cancel,
      getD_map_range _ _ unpair_fst_lt, getD_map_range _ _ unpair_snd_lt]

theorem renVar_primrec : Primrec fun p : List ℕ × ℕ × ℕ × ℕ => renVar p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  have hk : Primrec fun p : List ℕ × ℕ × ℕ × ℕ => p.2.2.1 := fst.comp (snd.comp snd)
  have hi : Primrec fun p : List ℕ × ℕ × ℕ × ℕ => p.2.2.2 := snd.comp (snd.comp snd)
  have hd : Primrec fun p : List ℕ × ℕ × ℕ × ℕ => p.2.2.2 - p.2.2.1 := nat_sub.comp hi hk
  exact (Primrec.ite (nat_lt.comp hi hk) hi
    (nat_add.comp ((list_getD' fst hd (nat_add.comp hd (fst.comp snd)))) hk)).of_eq
    fun _ => rfl
where
  list_getD' {α : Type} [Primcodable α] {f : α → List ℕ} {g h : α → ℕ} (hf : Primrec f)
      (hg : Primrec g) (hh : Primrec h) : Primrec fun a => (f a).getD (g a) (h a) := by
    have := option_getD.comp (list_getElem?.comp hf hg) hh
    exact this.of_eq fun a => by rw [List.getD_eq_getElem?_getD]

theorem renStep_primrec :
    Primrec fun p : (List ℕ × ℕ × ℕ) × ℕ × List (List ℕ) =>
      renStep p.1.1 p.1.2.1 p.1.2.2 p.2.1 p.2.2 := by
  -- the inner function, of `(p, k)`
  let P := (List ℕ × ℕ × ℕ) × ℕ × List (List ℕ)
  have hc : Primrec fun q : P × ℕ => q.1.2.1 := fst.comp (snd.comp fst)
  have hl : Primrec fun q : P × ℕ => q.1.2.2 := snd.comp (snd.comp fst)
  have hk : Primrec fun q : P × ℕ => q.2 := snd
  have hm : Primrec fun q : P × ℕ => q.1.2.1 - 2 := nat_sub.comp hc (const 2)
  have hq : Primrec fun q : P × ℕ => (q.1.2.1 - 2) / 3 := nat_div.comp hm (const 3)
  have hr : Primrec fun q : P × ℕ => (q.1.2.1 - 2) % 3 := nat_mod.comp hm (const 3)
  have ha : Primrec fun q : P × ℕ => q.1.2.2.getD (Nat.unpair ((q.1.2.1 - 2) / 3)).1 [] :=
    (list_getD []).comp hl (fst.comp (unpair.comp hq))
  have hb : Primrec fun q : P × ℕ => q.1.2.2.getD (Nat.unpair ((q.1.2.1 - 2) / 3)).2 [] :=
    (list_getD []).comp hl (snd.comp (unpair.comp hq))
  have hv : Primrec fun q : P × ℕ => renVar q.1.1.1 q.1.1.2.1 q.2 ((q.1.2.1 - 2) / 3) :=
    renVar_primrec.comp ((fst.comp (fst.comp fst)).pair
      ((fst.comp (snd.comp (fst.comp fst))).pair (hk.pair hq)))
  have h3 : ∀ {f : P × ℕ → ℕ}, Primrec f → ∀ e, Primrec fun q => 3 * f q + e :=
    fun hf e => nat_add.comp (nat_mul.comp (const 3) hf) (const e)
  have inner : Primrec₂ fun (p : P) (k : ℕ) =>
      if p.2.1 < 2 then p.2.1
      else if (p.2.1 - 2) % 3 = 0 then 3 * renVar p.1.1 p.1.2.1 k ((p.2.1 - 2) / 3) + 2
      else if (p.2.1 - 2) % 3 = 1 then
        3 * Nat.pair ((p.2.2.getD (Nat.unpair ((p.2.1 - 2) / 3)).1 []).getD k 0)
          ((p.2.2.getD (Nat.unpair ((p.2.1 - 2) / 3)).2 []).getD k 0) + 3
      else
        3 * Nat.pair ((p.2.2.getD (Nat.unpair ((p.2.1 - 2) / 3)).1 []).getD k 0)
          ((p.2.2.getD (Nat.unpair ((p.2.1 - 2) / 3)).2 []).getD (k + 1) 0) + 4 :=
    Primrec.ite (nat_lt.comp hc (const 2)) hc
      (Primrec.ite (Primrec.eq.comp hr (const 0)) (h3 hv 2)
        (Primrec.ite (Primrec.eq.comp hr (const 1))
          (h3 (Primrec₂.natPair.comp ((list_getD 0).comp ha hk) ((list_getD 0).comp hb hk)) 3)
          (h3 (Primrec₂.natPair.comp ((list_getD 0).comp ha hk)
            ((list_getD 0).comp hb (succ.comp hk))) 4)))
  exact (list_map (list_range.comp (succ.comp (snd.comp (snd.comp fst)))) inner).of_eq
    fun _ => rfl

theorem renTab_primrec :
    Primrec₂ fun (a : List ℕ × ℕ × ℕ) (c : ℕ) => renTab a.1 a.2.1 a.2.2 c :=
  nat_strong_rec _ (g := fun a l => some (renStep a.1 a.2.1 a.2.2 l.length l))
    (option_some.comp (renStep_primrec.comp (fst.pair ((list_length.comp snd).pair snd)))).to₂
    (fun a c => by simp [renStep_eq])

theorem renSC_primrec : Primrec fun p : List ℕ × ℕ × ℕ => renSC p.1 p.2.1 p.2.2 :=
  ((list_getD 0).comp (renTab_primrec.comp (fst.pair ((fst.comp snd).pair (snd.comp snd)))
    (snd.comp snd)) (const 0)).of_eq fun _ => rfl

theorem renC_primrec : Primrec₂ renC :=
  renSC_primrec.comp (fst.pair ((const 0).pair snd))

theorem weakenC_primrec : Primrec weakenC :=
  renSC_primrec.comp ((const []).pair ((const 1).pair .id))

theorem renListsC_primrec : Primrec₂ renListsC := by
  have hg : Primrec₂ fun (m : ℕ) (p : ℕ × List (List ℕ)) =>
      p.2.flatMap fun l => (List.range m).map fun i => i :: l :=
    list_flatMap (snd.comp snd)
      (list_map (list_range.comp (fst.comp fst)) (list_cons.comp snd (snd.comp fst)).to₂).to₂
  exact ((nat_rec (const [[]]) hg).comp snd fst).to₂.of_eq fun n m => rfl

end Dsub
