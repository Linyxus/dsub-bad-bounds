import Resolution.PrimFires
import Resolution.PrimFix

/-!
# Deciding subtyping by saturation on codes

With the bounds `L = Lf m` (scope) and `s = sf m` (size) computed from the input code `m`, the
derived codes `lfpM Lf sf m` are the least fixpoint of `firesLS L s` over the codes below
`MbLS L s`, which bounds every fact code of the family `Φ L s`. Every derived code is sound
(`lfpM_sound`), and the derived codes, read as facts, are saturated for `Φ L s`
(`lfpM_saturated`), so `Family.Saturated.complete` applies. Hence, when the query satisfies
the hypotheses `QueryOK` (bounds and a `Norm` predicate holding at it),
`Subtyping m ↔ jValidC m ∧ Nat.pair 0 m ∈ lfpM Lf sf m`, and subtyping is computable when
`Lf`, `sf` are primitive recursive.
-/

namespace Dsub

open Family

/-! ### Bounds on codes -/

theorem pair_mono {a b c d : ℕ} (h1 : a ≤ c) (h2 : b ≤ d) : Nat.pair a b ≤ Nat.pair c d := by
  have l : Nat.pair a b ≤ Nat.pair c b := by
    rcases h1.lt_or_eq with h | rfl
    · exact (Nat.pair_lt_pair_left b h).le
    · exact le_rfl
  have r : Nat.pair c b ≤ Nat.pair c d := by
    rcases h2.lt_or_eq with h | rfl
    · exact (Nat.pair_lt_pair_right c h).le
    · exact le_rfl
  exact l.trans r

/-- A bound on the codes of the types `T : Ty n` with `n + T.size ≤ k`. -/
def tyCB : ℕ → ℕ
  | 0 => 1
  | k + 1 => 3 * Nat.pair (tyCB k) (tyCB k) + 3 * k + 5

theorem tyCB_le_succ (k : ℕ) : tyCB k ≤ tyCB (k + 1) := by
  show tyCB k ≤ 3 * Nat.pair (tyCB k) (tyCB k) + 3 * k + 5
  have := Nat.left_le_pair (tyCB k) (tyCB k); omega

theorem tyCB_mono : Monotone tyCB := monotone_nat_of_le_succ tyCB_le_succ

theorem one_le_tyCB : ∀ k, 1 ≤ tyCB k
  | 0 => le_rfl
  | k + 1 => le_trans (one_le_tyCB k) (tyCB_le_succ k)

theorem code_le_tyCB : ∀ {n : ℕ} (T : Ty n), T.code ≤ tyCB (n + T.size)
  | _, .top => Nat.zero_le _
  | _, .bot => one_le_tyCB _
  | n, .sel x => by
    have := x.toNat_lt
    simp only [Ty.size, Ty.code_sel, tyCB]; omega
  | n, .bnd S U => by
    have ihS := code_le_tyCB S
    have ihU := code_le_tyCB U
    simp only [Ty.size]
    rw [show n + (S.size + U.size + 1) = (n + S.size + U.size) + 1 by omega, tyCB, Ty.code_bnd]
    have := pair_mono (ihS.trans (tyCB_mono (show n + S.size ≤ n + S.size + U.size by omega)))
      (ihU.trans (tyCB_mono (show n + U.size ≤ n + S.size + U.size by omega)))
    omega
  | n, .all S T => by
    have ihS := code_le_tyCB S
    have ihT := code_le_tyCB T
    have := S.size_pos
    simp only [Ty.size]
    rw [show n + (S.size + T.size + 1) = (n + S.size + T.size) + 1 by omega, tyCB, Ty.code_all]
    have := pair_mono (ihS.trans (tyCB_mono (show n + S.size ≤ n + S.size + T.size by omega)))
      (ihT.trans (tyCB_mono (show n + 1 + T.size ≤ n + S.size + T.size by omega)))
    omega

/-- A bound on the codes of the contexts of `n` variables with types of size at most `s`. -/
def ctxCB (s : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => Nat.pair (ctxCB s n) (tyCB (n + s)) + 1

theorem ctxCB_mono (s : ℕ) : Monotone (ctxCB s) := monotone_nat_of_le_succ fun n => by
  show ctxCB s n ≤ Nat.pair (ctxCB s n) (tyCB (n + s)) + 1
  have := Nat.left_le_pair (ctxCB s n) (tyCB (n + s)); omega

theorem code_le_ctxCB {s : ℕ} : ∀ {n : ℕ} (Γ : Ctx n), Γ.Bounded s → Γ.code ≤ ctxCB s n
  | _, .empty, _ => le_rfl
  | n + 1, .push Γ T, h => by
    rw [Ctx.code_push, pushC, ctxCB]
    have := pair_mono (code_le_ctxCB Γ h.1)
      ((code_le_tyCB T).trans (tyCB_mono (show n + T.size ≤ n + s by have := h.2; omega)))
    omega

/-- A bound on the fact codes of the family `Φ L s`. -/
def MbLS (L s : ℕ) : ℕ :=
  Nat.pair 1 (Nat.pair L (Nat.pair (ctxCB s L) (Nat.pair (tyCB (L + s + 2)) (tyCB (L + s + 2))))) + 1

theorem fact_lt_MbLS {L s t n : ℕ} (ht : t ≤ 1) (hn : n ≤ L) {Γ : Ctx n} (hΓ : Γ.Bounded s)
    {P W : Ty n} (hP : P.size ≤ s + 2) (hW : W.size ≤ s + 2) :
    Nat.pair t (mkJ n Γ.code P.code W.code) < MbLS L s := by
  have hP' : P.code ≤ tyCB (L + s + 2) := (code_le_tyCB P).trans (tyCB_mono (by omega))
  have hW' : W.code ≤ tyCB (L + s + 2) := (code_le_tyCB W).trans (tyCB_mono (by omega))
  exact Nat.lt_succ_of_le (pair_mono ht (pair_mono hn (pair_mono
    ((code_le_ctxCB Γ hΓ).trans (ctxCB_mono s hn)) (pair_mono hP' hW'))))

theorem size_le_of_mem_ext {n s : ℕ} {W : Ty n} (h : W ∈ ext (tysUpTo n s)) : W.size ≤ s + 2 := by
  rcases Finset.mem_union.1 h with h | h
  · have := mem_tysUpTo.1 h; omega
  · obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 h
    have := mem_tysUpTo.1 hP
    simp only [Ty.size]; omega

/-! ### Primitive recursion -/

section PR

open Primrec

variable {α : Type} [Primcodable α]

/-- One step of `sizeC`, reading earlier values from a list. -/
def sizeStep (c : ℕ) (l : List ℕ) : ℕ :=
  if c < 2 then 1
  else if (c - 2) % 3 = 0 then 1
  else l.getD (Nat.unpair ((c - 2) / 3)).1 0 + l.getD (Nat.unpair ((c - 2) / 3)).2 0 + 1

theorem sizeStep_eq (c : ℕ) : sizeStep c ((List.range c).map sizeC) = sizeC c := by
  match c with
  | 0 => rw [sizeC]; rfl
  | 1 => rw [sizeC]; rfl
  | m + 2 =>
    have h2 : ¬ m + 2 < 2 := by omega
    rw [sizeC, sizeStep]
    simp only [h2, ↓reduceIte, Nat.add_sub_cancel, getD_map_range _ _ unpair_fst_lt,
      getD_map_range _ _ unpair_snd_lt]

theorem sizeC_primrec : Primrec sizeC := by
  have hstep : Primrec₂ sizeStep := by
    have hm : Primrec fun p : ℕ × List ℕ => p.1 - 2 := nat_sub.comp fst (const 2)
    have hq : Primrec fun p : ℕ × List ℕ => (p.1 - 2) / 3 := nat_div.comp hm (const 3)
    have hr : Primrec fun p : ℕ × List ℕ => (p.1 - 2) % 3 := nat_mod.comp hm (const 3)
    have ha : Primrec fun p : ℕ × List ℕ => p.2.getD (Nat.unpair ((p.1 - 2) / 3)).1 0 :=
      (list_getD 0).comp snd (fst.comp (unpair.comp hq))
    have hb : Primrec fun p : ℕ × List ℕ => p.2.getD (Nat.unpair ((p.1 - 2) / 3)).2 0 :=
      (list_getD 0).comp snd (snd.comp (unpair.comp hq))
    exact (Primrec.ite (nat_lt.comp fst (const 2)) (const 1)
      (Primrec.ite (Primrec.eq.comp hr (const 0)) (const 1)
        (succ.comp (nat_add.comp ha hb)))).of_eq fun _ => rfl
  have := nat_strong_rec (fun (_ : Unit) c => sizeC c)
    (g := fun _ l => some (sizeStep l.length l))
    (option_some.comp (hstep.comp (list_length.comp snd) snd)).to₂
    (fun _ c => by simp [sizeStep_eq])
  exact this.comp (const ()) .id

theorem tyCB_primrec : Primrec tyCB := by
  have hf : Primrec₂ fun (k IH : ℕ) => 3 * Nat.pair IH IH + 3 * k + 5 :=
    nat_add.comp (nat_add.comp (nat_mul.comp (const 3) (Primrec₂.natPair.comp snd snd))
      (nat_mul.comp (const 3) fst)) (const 5)
  refine (nat_rec₁ 1 hf).of_eq fun k => ?_
  induction k with
  | zero => rfl
  | succ k ih => simp only [tyCB, ← ih]

theorem ctxCB_primrec : Primrec₂ ctxCB := by
  have hg : Primrec₂ fun (s : ℕ) (p : ℕ × ℕ) => Nat.pair p.2 (tyCB (p.1 + s)) + 1 :=
    succ.comp (Primrec₂.natPair.comp (snd.comp snd)
      (tyCB_primrec.comp (nat_add.comp (fst.comp snd) fst)))
  refine (nat_rec (const 0) hg).of_eq fun s n => ?_
  induction n with
  | zero => rfl
  | succ n ih => simp only [ctxCB, ← ih]

theorem MbLS_primrec : Primrec₂ MbLS := by
  have hT : Primrec fun p : ℕ × ℕ => tyCB (p.1 + p.2 + 2) :=
    tyCB_primrec.comp (nat_add.comp (nat_add.comp fst snd) (const 2))
  exact succ.comp (Primrec₂.natPair.comp (const 1) (Primrec₂.natPair.comp fst
    (Primrec₂.natPair.comp (ctxCB_primrec.comp snd fst) (Primrec₂.natPair.comp hT hT))))

theorem extC_primrec : Primrec₂ extC :=
  Primrec.or.comp (nat_le.decide.comp (sizeC_primrec.comp snd) fst)
    (Primrec.and.comp (Primrec.and.comp (Primrec.eq.decide.comp (tyTag_primrec.comp snd) (const 3))
      (Primrec.eq.decide.comp (tyArg₂_primrec.comp snd) (const 0)))
      (nat_le.decide.comp (sizeC_primrec.comp (tyArg₁_primrec.comp snd)) fst))

theorem ctxBoundedC_primrec :
    Primrec fun p : ℕ × ℕ × ℕ => ctxBoundedC p.1 p.2.1 p.2.2 := by
  have hit : Primrec₂ fun g x : ℕ => tailC^[x] g :=
    (nat_iterate snd fst (tailC_primrec.comp snd).to₂).to₂
  have hall : Primrec fun p : ℕ × ℕ × ℕ =>
      (List.range p.2.1).all fun i => decide (sizeC (headC (tailC^[i] p.2.2)) ≤ p.1) :=
    PR.list_all (list_range.comp (fst.comp snd))
      (nat_le.decide.comp (sizeC_primrec.comp (headC_primrec.comp
        (hit.comp (snd.comp (snd.comp fst)) snd))) (fst.comp fst)).to₂
  refine hall.of_eq fun p => ?_
  rw [Bool.eq_iff_iff, ctxBoundedC, decide_eq_true_iff, CtxBnd]
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq]

section Comp

variable {s R n g a b : α → _} 

theorem bcodeC_comp {n g a b : α → ℕ} (hn : Primrec n) (hg : Primrec g) (ha : Primrec a)
    (hb : Primrec b) : Primrec fun q => bcodeC (n q) (g q) (a q) (b q) :=
  Primrec₂.natPair.comp (const 0) (mkJ_primrec.comp (hn.pair (hg.pair (ha.pair hb))))

theorem scodeC_comp {n g a b : α → ℕ} (hn : Primrec n) (hg : Primrec g) (ha : Primrec a)
    (hb : Primrec b) : Primrec fun q => scodeC (n q) (g q) (a q) (b q) :=
  Primrec₂.natPair.comp (const 1) (mkJ_primrec.comp (hn.pair (hg.pair (ha.pair hb))))

theorem memB_comp {s n g a b : α → ℕ} {R : α → List ℕ} (hs : Primrec s) (hR : Primrec R)
    (hn : Primrec n) (hg : Primrec g) (ha : Primrec a) (hb : Primrec b) :
    Primrec fun q => memB (s q) (R q) (n q) (g q) (a q) (b q) :=
  Primrec.and.comp (Primrec.and.comp (nat_le.decide.comp (sizeC_primrec.comp ha) hs)
    (extC_primrec.comp hs hb)) (PR.list_mem.comp hR (bcodeC_comp hn hg ha hb))

theorem memS_comp {s n g a b : α → ℕ} {R : α → List ℕ} (hs : Primrec s) (hR : Primrec R)
    (hn : Primrec n) (hg : Primrec g) (ha : Primrec a) (hb : Primrec b) :
    Primrec fun q => memS (s q) (R q) (n q) (g q) (a q) (b q) :=
  Primrec.and.comp (Primrec.and.comp (nat_le.decide.comp (sizeC_primrec.comp ha) hs)
    (nat_le.decide.comp (sizeC_primrec.comp hb) hs)) (PR.list_mem.comp hR (scodeC_comp hn hg ha hb))

theorem viaS_comp {s n g a : α → ℕ} {R : α → List ℕ} {k : α → ℕ → Bool} (hs : Primrec s)
    (hR : Primrec R) (hn : Primrec n) (hg : Primrec g) (ha : Primrec a) (hk : Primrec₂ k) :
    Primrec fun q => viaS (s q) (R q) (n q) (g q) (a q) (k q) := by
  have hr : Primrec fun p : α × ℕ => jRight (Nat.unpair p.2).2 :=
    jRight_primrec.comp (snd.comp (unpair.comp snd))
  exact PR.list_any hR (Primrec.and.comp (Primrec.and.comp (validC_primrec.comp (hn.comp fst) hr)
    (memS_comp (hs.comp fst) (hR.comp fst) (hn.comp fst) (hg.comp fst) (ha.comp fst) hr))
    (hk.comp fst hr)).to₂

theorem ruleBaseC_comp {s n g p w : α → ℕ} {R : α → List ℕ} (hs : Primrec s) (hR : Primrec R)
    (hn : Primrec n) (hg : Primrec g) (hp : Primrec p) (hw : Primrec w) :
    Primrec fun q => ruleBaseC (s q) (R q) (n q) (g q) (p q) (w q) := by
  have eqN : ∀ {f h : α → ℕ}, Primrec f → Primrec h → Primrec fun q => decide (f q = h q) :=
    fun hf hh => Primrec.eq.decide.comp hf hh
  have hkB : Primrec₂ fun q r => memB (s q) (R q) (n q) (g q) r (w q) :=
    (memB_comp (hs.comp fst) (hR.comp fst) (hn.comp fst) (hg.comp fst) snd (hw.comp fst)).to₂
  have hbnd : Primrec fun q => bndC (p q) 0 := bndC_primrec.comp hp (const 0)
  have hbb : Primrec fun q => (List.range (n q)).any fun x =>
      memB (s q) (R q) (n q) (g q) (lookupC (g q) x) (bndC (p q) 0) &&
        viaS (s q) (R q) (n q) (g q) (lookupC (g q) x) (fun r => memB (s q) (R q) (n q) (g q) r (w q)) := by
    have hl : Primrec fun z : α × ℕ => lookupC (g z.1) z.2 := lookupC_primrec.comp (hg.comp fst) snd
    exact PR.list_any (list_range.comp hn) (Primrec.and.comp
      (memB_comp (hs.comp fst) (hR.comp fst) (hn.comp fst) (hg.comp fst) hl (hbnd.comp fst))
      (viaS_comp (hs.comp fst) (hR.comp fst) (hn.comp fst) (hg.comp fst) hl
        (hkB.comp (fst.comp fst) snd).to₂)).to₂
  exact Primrec.or.comp (eqN hw (const 0)) (Primrec.or.comp (eqN hp (const 1))
    (Primrec.or.comp (Primrec.and.comp (eqN (tyTag_primrec.comp hp) (const 2)) (eqN hp hw))
    (Primrec.or.comp (Primrec.and.comp (Primrec.and.comp (Primrec.and.comp
      (eqN (tyTag_primrec.comp hp) (const 3)) (eqN (tyTag_primrec.comp hw) (const 3)))
      (memB_comp hs hR hn hg (tyArg₁_primrec.comp hw) (tyArg₁_primrec.comp hp)))
      (memB_comp hs hR hn hg (tyArg₂_primrec.comp hp) (tyArg₂_primrec.comp hw)))
    (Primrec.or.comp (Primrec.and.comp (eqN (tyTag_primrec.comp hw) (const 2))
      (memB_comp hs hR hn hg (lookupC_primrec.comp hg (tyArg₁_primrec.comp hw)) hbnd))
    (Primrec.or.comp (Primrec.and.comp (eqN (tyTag_primrec.comp hp) (const 2))
      (viaS_comp hs hR hn hg (lookupC_primrec.comp hg (tyArg₁_primrec.comp hp)) hkB))
      hbb)))))

theorem ruleSC_comp {s n g p w : α → ℕ} {R : α → List ℕ} (hs : Primrec s) (hR : Primrec R)
    (hn : Primrec n) (hg : Primrec g) (hp : Primrec p) (hw : Primrec w) :
    Primrec fun q => ruleSC (s q) (R q) (n q) (g q) (p q) (w q) := by
  have eqN : ∀ {f h : α → ℕ}, Primrec f → Primrec h → Primrec fun q => decide (f q = h q) :=
    fun hf hh => Primrec.eq.decide.comp hf hh
  have hkS : Primrec₂ fun q r => memS (s q) (R q) (n q) (g q) r (w q) :=
    (memS_comp (hs.comp fst) (hR.comp fst) (hn.comp fst) (hg.comp fst) snd (hw.comp fst)).to₂
  have hbnd : Primrec fun q => bndC (p q) 0 := bndC_primrec.comp hp (const 0)
  have hbb : Primrec fun q => (List.range (n q)).any fun x =>
      memB (s q) (R q) (n q) (g q) (lookupC (g q) x) (bndC (p q) 0) &&
        viaS (s q) (R q) (n q) (g q) (lookupC (g q) x) (fun r => memS (s q) (R q) (n q) (g q) r (w q)) := by
    have hl : Primrec fun z : α × ℕ => lookupC (g z.1) z.2 := lookupC_primrec.comp (hg.comp fst) snd
    exact PR.list_any (list_range.comp hn) (Primrec.and.comp
      (memB_comp (hs.comp fst) (hR.comp fst) (hn.comp fst) (hg.comp fst) hl (hbnd.comp fst))
      (viaS_comp (hs.comp fst) (hR.comp fst) (hn.comp fst) (hg.comp fst) hl
        (hkS.comp (fst.comp fst) snd).to₂)).to₂
  exact Primrec.or.comp (Primrec.and.comp (Primrec.and.comp
      (eqN (tyTag_primrec.comp hp) (const 3))
      (nat_le.decide.comp (sizeC_primrec.comp (tyArg₁_primrec.comp hp)) hs))
      (eqN (tyArg₂_primrec.comp hp) hw))
    (Primrec.or.comp (Primrec.and.comp (eqN hp (const 1)) (eqN hw (const 1)))
    (Primrec.or.comp (Primrec.and.comp (eqN (tyTag_primrec.comp hp) (const 2))
      (viaS_comp hs hR hn hg (lookupC_primrec.comp hg (tyArg₁_primrec.comp hp)) hkS))
      hbb))

theorem allPremC_comp {L s n g p w e : α → ℕ} {R : α → List ℕ} (hL : Primrec L) (hs : Primrec s)
    (hR : Primrec R) (hn : Primrec n) (hg : Primrec g) (hp : Primrec p) (hw : Primrec w)
    (he : Primrec e) :
    Primrec fun q => allPremC (L q) (s q) (R q) (n q) (g q) (p q) (w q) (e q) := by
  have eqN : ∀ {β : Type} [Primcodable β] {f h : β → ℕ}, Primrec f → Primrec h →
      Primrec fun q => decide (f q = h q) :=
    fun hf hh => Primrec.eq.decide.comp hf hh
  have hj : Primrec fun q => (Nat.unpair (e q)).2 := snd.comp (unpair.comp he)
  have hsc := jScope_primrec.comp hj
  have hct := jCtx_primrec.comp hj
  have hle := jLeft_primrec.comp hj
  have hri := jRight_primrec.comp hj
  have hfl : Primrec₂ fun q (fl : List ℕ) =>
      morphC (jCtx (Nat.unpair (e q)).2) (jScope (Nat.unpair (e q)).2) (pushC (g q) (tyArg₁ (p q))) fl &&
        decide (renC fl (jLeft (Nat.unpair (e q)).2) = tyArg₂ (p q)) &&
        decide (renC fl (jRight (Nat.unpair (e q)).2) = tyArg₂ (w q)) :=
    (Primrec.and.comp (Primrec.and.comp
      (morphC_primrec.comp ((hct.comp fst).pair ((hsc.comp fst).pair
        ((pushC_primrec.comp (hg.comp fst) (tyArg₁_primrec.comp (hp.comp fst))).pair snd))))
      (eqN (renC_primrec.comp snd (hle.comp fst)) (tyArg₂_primrec.comp (hp.comp fst))))
      (eqN (renC_primrec.comp snd (hri.comp fst)) (tyArg₂_primrec.comp (hw.comp fst)))).to₂
  exact Primrec.and.comp (Primrec.and.comp (Primrec.and.comp (Primrec.and.comp (Primrec.and.comp
    (eqN (fst.comp (unpair.comp he)) (const 0)) (jValidC_primrec.comp hj))
    (nat_le.decide.comp hsc hL))
    (ctxBoundedC_primrec.comp (hs.pair (hsc.pair hct))))
    (memB_comp hs hR hsc hct hle hri))
    (PR.list_any (renListsC_primrec.comp hsc (succ.comp hn)) hfl)

theorem allCheckC_comp {L s n g p w : α → ℕ} {R : α → List ℕ} (hL : Primrec L) (hs : Primrec s)
    (hR : Primrec R) (hn : Primrec n) (hg : Primrec g) (hp : Primrec p) (hw : Primrec w) :
    Primrec fun q => allCheckC (L q) (s q) (R q) (n q) (g q) (p q) (w q) := by
  have eqN : ∀ {f h : α → ℕ}, Primrec f → Primrec h → Primrec fun q => decide (f q = h q) :=
    fun hf hh => Primrec.eq.decide.comp hf hh
  exact Primrec.and.comp (Primrec.and.comp (Primrec.and.comp
    (eqN (tyTag_primrec.comp hp) (const 4)) (eqN (tyTag_primrec.comp hw) (const 4)))
    (eqN (tyArg₁_primrec.comp hp) (tyArg₁_primrec.comp hw)))
    (PR.list_any hR (allPremC_comp (hL.comp fst) (hs.comp fst) (hR.comp fst) (hn.comp fst)
      (hg.comp fst) (hp.comp fst) (hw.comp fst) snd).to₂)

theorem firesLS_comp {L s c : α → ℕ} {R : α → List ℕ} (hL : Primrec L) (hs : Primrec s)
    (hR : Primrec R) (hc : Primrec c) :
    Primrec fun q => firesLS (L q) (s q) (R q) (c q) := by
  have eqN : ∀ {f h : α → ℕ}, Primrec f → Primrec h → Primrec fun q => decide (f q = h q) :=
    fun hf hh => Primrec.eq.decide.comp hf hh
  have hj : Primrec fun q => (Nat.unpair (c q)).2 := snd.comp (unpair.comp hc)
  have ht : Primrec fun q => (Nat.unpair (c q)).1 := fst.comp (unpair.comp hc)
  have hsc := jScope_primrec.comp hj
  have hct := jCtx_primrec.comp hj
  have hle := jLeft_primrec.comp hj
  have hri := jRight_primrec.comp hj
  exact Primrec.and.comp (Primrec.and.comp (Primrec.and.comp (Primrec.and.comp
    (jValidC_primrec.comp hj) (nat_le.decide.comp hsc hL))
    (ctxBoundedC_primrec.comp (hs.pair (hsc.pair hct))))
    (nat_le.decide.comp (sizeC_primrec.comp hle) hs))
    (Primrec.or.comp
      (Primrec.and.comp (Primrec.and.comp (eqN ht (const 0)) (extC_primrec.comp hs hri))
        (Primrec.or.comp (ruleBaseC_comp hs hR hsc hct hle hri)
          (allCheckC_comp hL hs hR hsc hct hle hri)))
      (Primrec.and.comp (Primrec.and.comp (eqN ht (const 1))
        (nat_le.decide.comp (sizeC_primrec.comp hri) hs))
        (ruleSC_comp hs hR hsc hct hle hri)))

end Comp

end PR

/-! ### The decision -/

section Decide

variable (Lf sf : ℕ → ℕ)

/-- The rule check for input `m`. -/
def firesM (m : ℕ) (R : List ℕ) (c : ℕ) : Bool := firesLS (Lf m) (sf m) R c

/-- The universe of codes for input `m`. -/
def MbM (m : ℕ) : ℕ := MbLS (Lf m) (sf m)

/-- The derived codes for input `m`. -/
abbrev lfpM (m : ℕ) : List ℕ := lfpList (firesM Lf sf) (MbM Lf sf) m

variable {Lf sf}

theorem firesM_mono : FiresMono (firesM Lf sf) := fun _ _ _ _ h hf => firesLS_mono h hf

theorem firesM_primrec (hL : Primrec Lf) (hs : Primrec sf) :
    Primrec fun p : ℕ × List ℕ × ℕ => firesM Lf sf p.1 p.2.1 p.2.2 :=
  firesLS_comp (hL.comp Primrec.fst) (hs.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
    (Primrec.snd.comp Primrec.snd)

theorem MbM_primrec (hL : Primrec Lf) (hs : Primrec sf) : Primrec (MbM Lf sf) :=
  MbLS_primrec.comp hL hs

/-- What a derived code means: a judgment that holds, or a summary that pops one level. -/
def CodeSound (c : ℕ) : Prop :=
  (∀ j : Judgment, c = Nat.pair 0 j.code → j.Holds) ∧
  (∀ j : Judgment, c = Nat.pair 1 j.code →
    ∀ k W, Sub j.Γ j.U (Ty.dN k W) → Sub j.Γ j.S (Ty.dN (k + 1) W))

theorem sound_of_codeSound {s : ℕ} {R : List ℕ} (h : ∀ c ∈ R, CodeSound c) {n : ℕ} (Γ : Ctx n) :
    SoundB Γ (BofR s R Γ) ∧ SoundS Γ (SofR s R Γ) := by
  constructor
  · rintro ⟨A, B⟩ hp
    exact (h _ (mem_BofR.1 hp).2.2).1 ⟨Γ, A, B⟩ rfl
  · rintro ⟨A, B⟩ hp
    exact (h _ (mem_SofR.1 hp).2.2).2 ⟨Γ, A, B⟩ rfl

/-- Every derived code is sound. -/
theorem lfpM_sound (m : ℕ) : ∀ c ∈ lfpM Lf sf m, CodeSound c := by
  refine lfpList_induction _ fun R c hR _ hf => ?_
  obtain ⟨n, Γ, P, W, rfl | rfl⟩ := firesLS_cases hf
  · have h := ((firesLS_bcode Γ P W).1 hf).2.2.2.2
    have hs := sound_of_codeSound (s := sf m) hR Γ
    have hsub : Sub Γ P W := h.elim (RuleB.sound hs.1 hs.2)
      (AllRule.sound fun i => sound_of_codeSound hR _)
    refine ⟨fun j hj => ?_, fun j hj => absurd (Nat.pair_eq_pair.1 hj).1 (by decide)⟩
    have : (⟨Γ, P, W⟩ : Judgment) = j := Judgment.code_injective (Nat.pair_eq_pair.1 hj).2
    subst this; exact hsub
  · have h := ((firesLS_scode Γ P W).1 hf).2.2.2.2
    have hs := sound_of_codeSound (s := sf m) hR Γ
    refine ⟨fun j hj => absurd (Nat.pair_eq_pair.1 hj).1 (by decide), fun j hj => ?_⟩
    have : (⟨Γ, P, W⟩ : Judgment) = j := Judgment.code_injective (Nat.pair_eq_pair.1 hj).2
    subst this; exact RuleS.sound hs.1 hs.2 h

/-- The derived codes, read as facts, are saturated for the family `Φ (Lf m) (sf m)`. -/
theorem lfpM_saturated (m : ℕ) :
    (Φ (Lf m) (sf m)).Saturated (factsOf (Lf m) (sf m) (lfpM Lf sf m)) where
  S_sub i p hp := by
    obtain ⟨A, B⟩ := p
    have hp' := mem_SofR.1 hp
    exact ⟨Φ.mem_F.2 hp'.1, Φ.mem_F.2 hp'.2.1⟩
  closedB i P hP W hW hr := by
    obtain ⟨hdim, hbnd⟩ := Φ.member_bounds _ _ i
    have hP' := Φ.mem_F.1 hP
    show (P, W) ∈ BofR _ _ _
    rw [mem_BofR]
    refine ⟨hP', hW, ?_⟩
    refine mem_lfpList_of_fires firesM_mono ?_ (fun x hx => hx) ((firesLS_bcode _ P W).2
      ⟨hdim, hbnd, hP', hW, hr⟩)
    exact fact_lt_MbLS (by omega) hdim hbnd (by omega) (size_le_of_mem_ext hW)
  closedS i P hP T hT hr := by
    obtain ⟨hdim, hbnd⟩ := Φ.member_bounds _ _ i
    have hP' := Φ.mem_F.1 hP
    have hT' := Φ.mem_F.1 hT
    show (P, T) ∈ SofR _ _ _
    rw [mem_SofR]
    refine ⟨hP', hT', ?_⟩
    refine mem_lfpList_of_fires firesM_mono ?_ (fun x hx => hx) ((firesLS_scode _ P T).2
      ⟨hdim, hbnd, hP', hT', hr⟩)
    exact fact_lt_MbLS le_rfl hdim hbnd (by omega) (by omega)

/-- In a saturated state, every good judgment within the bounds is recorded. -/
theorem bcode_mem_of_saturated {L s : ℕ} {R : List ℕ}
    (hsat : (Φ L s).Saturated (factsOf L s R)) (hs : 1 ≤ s) {G : Judgment → Prop}
    (hN : (Φ L s).Norm ((Φ L s).goodOf G)) {n : ℕ} {Γ : Ctx n} {S U : Ty n} (hn : n ≤ L)
    (hΓ : Γ.Bounded s) (hS : S.size ≤ s) (hU : U.size ≤ s) (hG : G ⟨Γ, S, U⟩)
    (hh : Sub Γ S U) : bcodeC n Γ.code S.code U.code ∈ R := by
  obtain ⟨i, e⟩ := Φ.exists_member hn hΓ
  rw [Sigma.mk.inj_iff] at e
  obtain ⟨h1, h2⟩ := e
  subst h1
  have h2 := eq_of_heq h2
  subst h2
  obtain ⟨h, D⟩ := hh.subH
  obtain ⟨R', c, hR⟩ := hsat.complete hN (Φ.wf hs) h i S U D hG (Φ.mem_F.2 hS) 0 U
    (mem_ext_of_mem (Φ.mem_F.2 hU)) rfl
  cases c
  exact (mem_BofR.1 hR).2.2

variable (Lf sf)

/-- What the decision needs at a query `m` naming a judgment that holds: the judgment lies
within the bounds `Lf m`, `sf m`, and a `Norm` predicate holds at it. -/
def QueryOK (m : ℕ) : Prop :=
  ∀ j : Judgment, j.code = m → j.Holds →
    j.n ≤ Lf m ∧ j.Γ.Bounded (sf m) ∧ j.S.size ≤ sf m ∧ j.U.size ≤ sf m ∧ 1 ≤ sf m ∧
      ∃ G : Judgment → Prop, (Φ (Lf m) (sf m)).Norm ((Φ (Lf m) (sf m)).goodOf G) ∧ G j

variable {Lf sf}

theorem Subtyping_iff_lfpM {m : ℕ} (hq : QueryOK Lf sf m) :
    Subtyping m ↔ jValidC m = true ∧ Nat.pair 0 m ∈ lfpM Lf sf m := by
  constructor
  · rintro ⟨j, hj, hh⟩
    rw [Judgment.decode_eq_some_iff] at hj
    obtain ⟨hn, hΓ, hS, hU, hs, G, hN, hG⟩ := hq j hj hh
    have hmem := bcode_mem_of_saturated (lfpM_saturated m) hs hN hn hΓ hS hU hG hh
    have e : Nat.pair 0 m = bcodeC j.n j.Γ.code j.S.code j.U.code := by rw [← hj]; rfl
    refine ⟨?_, ?_⟩
    · rw [← hj]; exact jValidC_code j
    · rw [e]; exact hmem
  · rintro ⟨hv, hmem⟩
    obtain ⟨j, hj⟩ := jValidC_iff.1 hv
    exact ⟨j, Judgment.decode_eq_some_iff.2 hj, (lfpM_sound m _ hmem).1 j (by rw [hj])⟩

/-- Subtyping is decidable, given primitive recursive bounds within which every holding query
has a `Norm` predicate holding at it. -/
theorem Subtyping_computable_of_bounds (hL : Primrec Lf) (hs : Primrec sf)
    (hq : ∀ m, QueryOK Lf sf m) : ComputablePred Subtyping :=
  computablePred_of_primrec
    (Primrec.and.comp jValidC_primrec (lfpList_mem_primrec (firesM_primrec hL hs)
      (MbM_primrec hL hs) (Primrec₂.natPair.comp (Primrec.const 0) Primrec.id)))
    fun m => by rw [Subtyping_iff_lfpM (hq m), Bool.and_eq_true, decide_eq_true_iff]; rfl

end Decide

end Dsub
