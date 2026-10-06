import Resolution.Bound
import Resolution.Good

/-!
Lemma 4 in the form `Lemma4` that `Good` takes as a hypothesis, and the bound `Bnd` is
primitive recursive.
-/

namespace Dsub

open Primrec

private theorem sq_primrec {α : Type*} [Primcodable α] {f : α → ℕ} (hf : Primrec f) :
    Primrec fun a => f a ^ 2 :=
  (nat_mul.comp hf hf).of_eq fun a => (sq (f a)).symm

theorem codeBound_primrec : Primrec codeBound := by
  have hg : Primrec₂ fun (_ : ℕ) (p : ℕ × ℕ) => 3 * p.2 ^ 2 + 3 * p.1 + 6 :=
    (nat_add.comp (nat_add.comp (nat_mul.comp (const 3) (sq_primrec (snd.comp snd)))
      (nat_mul.comp (const 3) (fst.comp snd))) (const 6)).to₂
  refine ((nat_rec (const 1) hg).comp (const 0) .id).of_eq fun k => ?_
  induction k with
  | zero => rfl
  | succ k ih => simp only [codeBound, ← ih]; rfl

theorem two_pow_primrec : Primrec fun K : ℕ => 2 ^ K := by
  have hg : Primrec₂ fun (_ : ℕ) (p : ℕ × ℕ) => 2 * p.2 :=
    (nat_mul.comp (const 2) (snd.comp snd)).to₂
  refine ((nat_rec (const 1) hg).comp (const 0) .id).of_eq fun k => ?_
  induction k with
  | zero => rfl
  | succ k ih => simp only [pow_succ, ← ih]; exact Nat.mul_comm _ _

theorem clsStep_primrec : Primrec fun p : ℕ × ℕ × ℕ => clsStep p.1 p.2.1 p.2.2 :=
  sq_primrec (nat_add.comp (nat_add.comp fst (sq_primrec (nat_add.comp (fst.comp snd)
    (two_pow_primrec.comp (snd.comp snd))))) (const 1))

theorem clsBound_primrec : Primrec fun p : ℕ × ℕ × ℕ => clsBound p.1 p.2.1 p.2.2 := by
  have hf : Primrec fun q : ℕ × ℕ => clsStep q.1 q.2 0 :=
    clsStep_primrec.comp (fst.pair (snd.pair (const 0)))
  have hg : Primrec₂ fun (q : ℕ × ℕ) (p : ℕ × ℕ) => clsStep q.1 q.2 p.2 :=
    (clsStep_primrec.comp ((fst.comp fst).pair ((snd.comp fst).pair (snd.comp snd)))).to₂
  refine ((nat_rec hf hg).comp (fst.pair (fst.comp snd)) (snd.comp snd)).of_eq fun p => ?_
  obtain ⟨N, L, k⟩ := p
  induction k with
  | zero => rfl
  | succ k ih => simp only [clsBound, ← ih]

theorem treeBound_primrec : Primrec₂ treeBound := by
  have hg : Primrec₂ fun (b : ℕ) (p : ℕ × ℕ) => 1 + b * p.2 :=
    (nat_add.comp (const 1) (nat_mul.comp fst (snd.comp snd))).to₂
  refine (nat_rec (const 1) hg).of_eq fun b j => ?_
  induction j with
  | zero => rfl
  | succ j ih => simp only [treeBound, ← ih]

theorem Bnd_primrec : Primrec fun p : ℕ × ℕ × ℕ => Bnd p.1 p.2.1 p.2.2 := by
  have hb : Primrec fun p : ℕ × ℕ × ℕ =>
      clsBound p.1 (codeBound (p.2.2 + p.1 + 1 + p.2.1)) p.1 + 2 * p.2.1 :=
    nat_add.comp (clsBound_primrec.comp (fst.pair ((codeBound_primrec.comp
      (nat_add.comp (nat_add.comp (nat_add.comp (snd.comp snd) fst) (const 1))
        (fst.comp snd))).pair fst))) (nat_mul.comp (const 2) (fst.comp snd))
  exact (nat_mul.comp hb (treeBound_primrec.comp hb fst)).of_eq fun p => rfl

open Classical in
private theorem ncard_eq_card {n : ℕ} (p : BVar n → Prop) :
    {x | p x}.ncard = (Finset.univ.filter p).card := by
  rw [← Set.ncard_coe_finset]; congr 1; ext x; simp

/-- Lemma 4 at the bound `Bnd`. -/
theorem lemma4 (N s n₀ : ℕ) : Lemma4 N s n₀ (Bnd N s n₀) := by
  intro n Γ a S U hI hsz hS hU hb
  classical
  simp only [Ty.occCount, Ann.nBase, Ann.nCreated, ncard_eq_card] at hS hU hb ⊢
  have := bound_or_collapse (N := N) (s := s) (n₀ := n₀) hI (fun x _ => hsz x)
    (by convert hS) (by convert hU) (by convert hb)
  convert this

end Dsub
