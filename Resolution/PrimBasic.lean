import Mathlib.Computability.Primrec.List

/-!
Primitive recursion helpers: `all`, `any`, `filter` and membership on lists, and `getD` on
`List.range … |>.map`.
-/

namespace Dsub.PR

open Primrec

variable {α β σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]

theorem list_any {f : α → List β} {g : α → β → Bool} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec fun a => (f a).any (g a) := by
  have := list_foldr hf (const false)
    (Primrec.or.comp (hg.comp fst (fst.comp snd)) (snd.comp snd)).to₂
  refine this.of_eq fun a => ?_
  induction f a <;> simp_all

theorem list_all {f : α → List β} {g : α → β → Bool} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec fun a => (f a).all (g a) := by
  have := list_foldr hf (const true)
    (Primrec.and.comp (hg.comp fst (fst.comp snd)) (snd.comp snd)).to₂
  refine this.of_eq fun a => ?_
  induction f a <;> simp_all

theorem list_filter {f : α → List β} {g : α → β → Bool} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec fun a => (f a).filter (g a) := by
  have := list_foldr hf (const [])
    (cond (hg.comp fst (fst.comp snd)) (list_cons.comp (fst.comp snd) (snd.comp snd))
      (snd.comp snd)).to₂
  refine this.of_eq fun a => ?_
  induction f a with
  | nil => rfl
  | cons b l ih => simp only [List.foldr_cons, List.filter_cons, ih]; cases g a b <;> rfl

theorem list_mem [DecidableEq β] : Primrec₂ fun (l : List β) (b : β) => decide (b ∈ l) := by
  have := list_any (f := fun p : List β × β => p.1) (g := fun p c => decide (c = p.2)) fst
    (Primrec.eq.decide.comp snd (snd.comp fst))
  refine this.to₂.of_eq fun l b => ?_
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true, decide_eq_true_eq, exists_eq_right]

end Dsub.PR

namespace Dsub

theorem getD_map_range {β : Type*} {n a : ℕ} (f : ℕ → β) (d : β) (h : a < n) :
    ((List.range n).map f).getD a d = f a := by
  simp [List.getD_eq_getElem?_getD, h]

end Dsub
