import Resolution.Collapse
import Resolution.Sized
import Resolution.PrimCodes

/-!
A bound on codes by scope and size (`Ty.size` is in `FamilyEnum`), renamings injective on
the variables that occur, and the number of variables of a type.  Used to count the labels of
Lemma 4 (PROOF.md §4).
-/

namespace Dsub

/-! ### Codes are bounded by scope and size -/

/-- `codeBound k` bounds the codes of the types of scope `m` and size `s` with `m + s ≤ k`. -/
def codeBound : ℕ → ℕ
  | 0 => 1
  | k + 1 => 3 * codeBound k ^ 2 + 3 * k + 6

theorem codeBound_mono : Monotone codeBound := by
  apply monotone_nat_of_le_succ
  intro k
  show codeBound k ≤ 3 * codeBound k ^ 2 + 3 * k + 6
  have := Nat.le_self_pow (n := 2) (by omega) (codeBound k)
  omega

theorem Ty.code_lt {m : ℕ} (T : Ty m) : T.code < codeBound (m + T.size) := by
  induction T with
  | top => simp only [Ty.code, Ty.size, codeBound]; omega
  | bot => simp only [Ty.code, Ty.size, codeBound]; omega
  | sel x =>
    have := BVar.toNat_lt x
    simp only [Ty.code, Ty.size, codeBound]; omega
  | @bnd m S U ihS ihU =>
    have hS := S.size_pos
    have hU := U.size_pos
    obtain ⟨G, hG⟩ : ∃ G, codeBound (m + S.size + U.size) = G := ⟨_, rfl⟩
    have h1 : S.code < G := hG ▸ lt_of_lt_of_le ihS (codeBound_mono (by omega))
    have h2 : U.code < G := hG ▸ lt_of_lt_of_le ihU (codeBound_mono (by omega))
    have hp := Nat.pair_lt_max_add_one_sq S.code U.code
    have hq : (max S.code U.code + 1) ^ 2 ≤ G ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    show 3 * Nat.pair S.code U.code + 3 < codeBound (m + (S.size + U.size + 1))
    rw [show m + (S.size + U.size + 1) = (m + S.size + U.size) + 1 by omega, codeBound, hG]
    omega
  | @all m S T ihS ihT =>
    have hS := S.size_pos
    have hT := T.size_pos
    obtain ⟨G, hG⟩ : ∃ G, codeBound (m + S.size + T.size) = G := ⟨_, rfl⟩
    have h1 : S.code < G := hG ▸ lt_of_lt_of_le ihS (codeBound_mono (by omega))
    have h2 : T.code < G := hG ▸ lt_of_lt_of_le ihT (codeBound_mono (by omega))
    have hp := Nat.pair_lt_max_add_one_sq S.code T.code
    have hq : (max S.code T.code + 1) ^ 2 ≤ G ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    show 3 * Nat.pair S.code T.code + 4 < codeBound (m + (S.size + T.size + 1))
    rw [show m + (S.size + T.size + 1) = (m + S.size + T.size) + 1 by omega, codeBound, hG]
    omega

/-! ### Renamings injective on the occurring variables -/

theorem Ty.rename_injOn {n m : ℕ} {f : Rename n m} {S T : Ty n}
    (hf : ∀ x y, (S.Occ x ∨ T.Occ x) → (S.Occ y ∨ T.Occ y) → f.var x = f.var y → x = y)
    (h : S.rename f = T.rename f) : S = T := by
  induction S generalizing m with
  | top => cases T <;> simp_all
  | bot => cases T <;> simp_all
  | sel x =>
    cases T with
    | sel y =>
      simp only [Ty.rename_sel, Ty.sel.injEq] at h
      rw [hf x y (Or.inl rfl) (Or.inr rfl) h]
    | _ => simp at h
  | bnd S U ihS ihU =>
    cases T with
    | bnd S' U' =>
      simp only [Ty.rename_bnd, Ty.bnd.injEq] at h
      rw [ihS (fun x y hx hy e => hf x y (by simp only [Ty.occ_bnd]; tauto)
        (by simp only [Ty.occ_bnd]; tauto) e) h.1,
        ihU (fun x y hx hy e => hf x y (by simp only [Ty.occ_bnd]; tauto)
        (by simp only [Ty.occ_bnd]; tauto) e) h.2]
    | _ => simp at h
  | all S B ihS ihB =>
    cases T with
    | all S' B' =>
      simp only [Ty.rename_all, Ty.all.injEq] at h
      rw [ihS (fun x y hx hy e => hf x y (by simp only [Ty.occ_all]; tauto)
        (by simp only [Ty.occ_all]; tauto) e) h.1]
      rw [ihB (fun x y hx hy e => ?_) h.2]
      cases x with
      | here =>
        cases y with
        | here => rfl
        | there y => simp at e
      | there x =>
        cases y with
        | here => simp at e
        | there y =>
          simp only [Rename.lift_there, BVar.there.injEq] at e
          rw [hf x y (by simp only [Ty.occ_all]; tauto) (by simp only [Ty.occ_all]; tauto) e]
    | _ => simp at h

/-! ### Variables by index -/

theorem BVar.toNat_ofNat : ∀ {n k : ℕ} {x : BVar n}, BVar.ofNat n k = some x → x.toNat = k
  | 0, _, _, h => by simp [BVar.ofNat] at h
  | _ + 1, 0, _, h => by
    simp only [BVar.ofNat, Option.some.injEq] at h
    subst h; rfl
  | n + 1, k + 1, x, h => by
    simp only [BVar.ofNat, Option.map_eq_some_iff] at h
    obtain ⟨y, hy, rfl⟩ := h
    simp [BVar.toNat, BVar.toNat_ofNat hy]

theorem BVar.ofNat_exists : ∀ {n k : ℕ}, k < n → ∃ x, BVar.ofNat n k = some x
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _ => ⟨.here, rfl⟩
  | n + 1, k + 1, h => by
    obtain ⟨x, hx⟩ := BVar.ofNat_exists (n := n) (k := k) (by omega)
    exact ⟨.there x, by simp [BVar.ofNat, hx]⟩

/-- The variable of index `k` in scope `m + 1`, or `here` if there is none. -/
def BVar.ofNatD (m k : ℕ) : BVar (m + 1) := (BVar.ofNat (m + 1) k).getD .here

theorem BVar.ofNatD_inj {m k k' : ℕ} (hk : k ≤ m) (hk' : k' ≤ m)
    (h : BVar.ofNatD m k = BVar.ofNatD m k') : k = k' := by
  obtain ⟨x, hx⟩ := BVar.ofNat_exists (n := m + 1) (k := k) (by omega)
  obtain ⟨x', hx'⟩ := BVar.ofNat_exists (n := m + 1) (k := k') (by omega)
  simp only [BVar.ofNatD, hx, hx', Option.getD_some] at h
  rw [← BVar.toNat_ofNat hx, ← BVar.toNat_ofNat hx', h]

/-! ### The number of variables of a type -/

section

open Classical

theorem Ty.card_occ_mono {n : ℕ} {T T' : Ty n} (h : ∀ x, T.Occ x → T'.Occ x) :
    (Finset.univ.filter fun x => T.Occ x).card ≤ (Finset.univ.filter fun x => T'.Occ x).card :=
  Finset.card_le_card (fun x hx => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact h x hx)

/-- A type mentions at most as many variables as it has constructors. -/
theorem Ty.card_occ_le_size {n : ℕ} (T : Ty n) :
    (Finset.univ.filter fun x => T.Occ x).card ≤ T.size := by
  induction T with
  | top => simp [Ty.size]
  | bot => simp [Ty.size]
  | sel y =>
    have : (Finset.univ.filter fun x => (Ty.sel y).Occ x) ⊆ {y} := fun x hx => by simpa using hx
    exact le_trans (Finset.card_le_card this) (by simp [Ty.size])
  | bnd S U ihS ihU =>
    have : (Finset.univ.filter fun x => (Ty.bnd S U).Occ x) ⊆
        (Finset.univ.filter fun x => S.Occ x) ∪ (Finset.univ.filter fun x => U.Occ x) :=
      fun x hx => by simpa using hx
    have h1 := Finset.card_le_card this
    have h2 := Finset.card_union_le (Finset.univ.filter fun x => S.Occ x)
      (Finset.univ.filter fun x => U.Occ x)
    simp only [Ty.size]
    omega
  | @all n S T ihS ihT =>
    have hT : (Finset.univ.filter fun x : BVar n => T.Occ (.there x)).card ≤
        (Finset.univ.filter fun y => T.Occ y).card :=
      Finset.card_le_card_of_injOn BVar.there (fun x hx => by simpa using hx)
        (fun x _ y _ e => BVar.there.inj e)
    have : (Finset.univ.filter fun x => (Ty.all S T).Occ x) ⊆
        (Finset.univ.filter fun x => S.Occ x) ∪
          (Finset.univ.filter fun x : BVar n => T.Occ (.there x)) :=
      fun x hx => by simpa using hx
    have h1 := Finset.card_le_card this
    have h2 := Finset.card_union_le (Finset.univ.filter fun x => S.Occ x)
      (Finset.univ.filter fun x : BVar n => T.Occ (.there x))
    simp only [Ty.size]
    omega

/-- A right side sized by `s` mentions at most `s` variables. -/
theorem Ty.RSized.card_occ {n s : ℕ} {T : Ty n} (h : T.RSized s) :
    (Finset.univ.filter fun x => T.Occ x).card ≤ s := by
  induction T with
  | top => exact le_trans (Ty.card_occ_le_size _) h
  | bot => exact le_trans (Ty.card_occ_le_size _) h
  | sel y => exact le_trans (Ty.card_occ_le_size _) h
  | bnd L H _ ihH =>
    rcases h with h | ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact le_trans (Ty.card_occ_le_size _) h
    · exact le_trans (Ty.card_occ_mono (T' := H) (fun x hx => by simpa using hx)) (ihH h)
    · exact le_trans (Ty.card_occ_mono (T' := L) (fun x hx => by simpa using hx))
        (le_trans (Ty.card_occ_le_size _) h)
  | all S T => exact le_trans (Ty.card_occ_le_size _) h

end

end Dsub
