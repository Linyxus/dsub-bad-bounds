import Dsub

/-!
Renamings: identity, composition, lifting, and how weakening commutes with renaming.
Nested declarations `dN`.  Context morphisms.
-/

namespace Dsub

/-! ### Renamings -/

def Rename.id {n : ℕ} : Rename n n where var := fun x => x

def Rename.comp {n m k : ℕ} (f : Rename n m) (g : Rename m k) : Rename n k where
  var := fun x => g.var (f.var x)

theorem Rename.ext {n m : ℕ} {f g : Rename n m} (h : ∀ x, f.var x = g.var x) : f = g := by
  cases f; cases g; congr; exact funext h

@[simp] theorem Rename.lift_here {n m : ℕ} {f : Rename n m} : f.lift.var .here = .here := rfl
@[simp] theorem Rename.lift_there {n m : ℕ} {f : Rename n m} {x : BVar n} :
    f.lift.var (.there x) = .there (f.var x) := rfl
@[simp] theorem Rename.succ_var {n : ℕ} {x : BVar n} : (Rename.succ).var x = .there x := rfl
@[simp] theorem Rename.id_var {n : ℕ} {x : BVar n} : (Rename.id).var x = x := rfl
@[simp] theorem Rename.comp_var {n m k : ℕ} {f : Rename n m} {g : Rename m k} {x : BVar n} :
    (f.comp g).var x = g.var (f.var x) := rfl

theorem Rename.lift_id {n : ℕ} : (Rename.id (n := n)).lift = Rename.id := by
  apply Rename.ext; intro x; cases x <;> rfl

theorem Rename.lift_comp {n m k : ℕ} {f : Rename n m} {g : Rename m k} :
    (f.comp g).lift = f.lift.comp g.lift := by
  apply Rename.ext; intro x; cases x <;> rfl

theorem Rename.succ_lift_comm {n m : ℕ} {f : Rename n m} :
    (Rename.succ).comp f.lift = f.comp Rename.succ := by
  apply Rename.ext; intro x; rfl

@[simp] theorem Ty.rename_top {n m : ℕ} {f : Rename n m} : (Ty.top (n := n)).rename f = .top := rfl
@[simp] theorem Ty.rename_bot {n m : ℕ} {f : Rename n m} : (Ty.bot (n := n)).rename f = .bot := rfl
@[simp] theorem Ty.rename_bnd {n m : ℕ} {S U : Ty n} {f : Rename n m} :
    (Ty.bnd S U).rename f = .bnd (S.rename f) (U.rename f) := rfl
@[simp] theorem Ty.rename_sel {n m : ℕ} {x : BVar n} {f : Rename n m} :
    (Ty.sel x).rename f = .sel (f.var x) := rfl
@[simp] theorem Ty.rename_all {n m : ℕ} {S : Ty n} {T : Ty (n+1)} {f : Rename n m} :
    (Ty.all S T).rename f = .all (S.rename f) (T.rename f.lift) := rfl

theorem Ty.rename_id {n : ℕ} {T : Ty n} : T.rename Rename.id = T := by
  induction T with
  | top => rfl
  | bot => rfl
  | bnd S U ih1 ih2 => simp only [Ty.rename, ih1, ih2]
  | sel x => rfl
  | all S T ih1 ih2 => simp only [Ty.rename, Rename.lift_id, ih1, ih2]

theorem Ty.rename_comp {n m k : ℕ} {T : Ty n} {f : Rename n m} {g : Rename m k} :
    (T.rename f).rename g = T.rename (f.comp g) := by
  induction T generalizing m k with
  | top => rfl
  | bot => rfl
  | bnd S U ih1 ih2 => simp only [Ty.rename, ih1, ih2]
  | sel x => rfl
  | all S T ih1 ih2 => simp only [Ty.rename, ih1, ih2, Rename.lift_comp]

theorem Ty.weaken_rename_comm {n m : ℕ} {T : Ty n} {f : Rename n m} :
    T.weaken.rename f.lift = (T.rename f).weaken := by
  simp only [Ty.weaken, Ty.rename_comp, Rename.succ_lift_comm]

@[simp] theorem Ty.weaken_top {n : ℕ} : (Ty.top (n := n)).weaken = .top := rfl
@[simp] theorem Ty.weaken_bot {n : ℕ} : (Ty.bot (n := n)).weaken = .bot := rfl
@[simp] theorem Ty.weaken_bnd {n : ℕ} {S U : Ty n} :
    (Ty.bnd S U).weaken = .bnd S.weaken U.weaken := rfl
@[simp] theorem Ty.weaken_sel {n : ℕ} {x : BVar n} : (Ty.sel x).weaken = .sel (.there x) := rfl

@[simp] theorem Ctx.lookup_here {n : ℕ} {Γ : Ctx n} {T : Ty n} :
    (Γ.push T).lookup .here = T.weaken := rfl
@[simp] theorem Ctx.lookup_there {n : ℕ} {Γ : Ctx n} {T : Ty n} {x : BVar n} :
    (Γ.push T).lookup (.there x) = (Γ.lookup x).weaken := rfl

/-! ### Nested declarations -/

/-- `dN k V = {A:⊥..{A:⊥..…V}}` with `k` declarations. -/
def Ty.dN {n : ℕ} : ℕ → Ty n → Ty n
  | 0, V => V
  | k + 1, V => .bnd .bot (Ty.dN k V)

@[simp] theorem Ty.dN_zero {n : ℕ} {V : Ty n} : Ty.dN 0 V = V := rfl
@[simp] theorem Ty.dN_succ {n k : ℕ} {V : Ty n} : Ty.dN (k + 1) V = .bnd .bot (Ty.dN k V) := rfl

/-! ### Context morphisms -/

/-- `f` maps `Γ` into `Δ`: the type of each renamed variable is the renamed type.  `f` need not
be injective. -/
def Rename.IsCtxMorph {n m : ℕ} (f : Rename n m) (Γ : Ctx n) (Δ : Ctx m) : Prop :=
  ∀ x, Δ.lookup (f.var x) = (Γ.lookup x).rename f

theorem Rename.IsCtxMorph.lift {n m : ℕ} {f : Rename n m} {Γ : Ctx n} {Δ : Ctx m}
    (h : f.IsCtxMorph Γ Δ) (S : Ty n) : f.lift.IsCtxMorph (Γ.push S) (Δ.push (S.rename f)) := by
  intro x
  cases x with
  | here => simp only [Rename.lift_here, Ctx.lookup_here, Ty.weaken_rename_comm]
  | there x => simp only [Rename.lift_there, Ctx.lookup_there, h x, Ty.weaken_rename_comm]

theorem Rename.isCtxMorph_succ {n : ℕ} (Γ : Ctx n) (T : Ty n) :
    (Rename.succ).IsCtxMorph Γ (Γ.push T) :=
  fun _ => rfl

theorem Rename.isCtxMorph_id {n : ℕ} (Γ : Ctx n) : (Rename.id).IsCtxMorph Γ Γ :=
  fun _ => Ty.rename_id.symm

theorem Rename.IsCtxMorph.comp {n m k : ℕ} {f : Rename n m} {g : Rename m k} {Γ : Ctx n}
    {Δ : Ctx m} {Θ : Ctx k} (hf : f.IsCtxMorph Γ Δ) (hg : g.IsCtxMorph Δ Θ) :
    (f.comp g).IsCtxMorph Γ Θ := by
  intro x
  simp only [Rename.comp_var, hg (f.var x), hf x, Ty.rename_comp]

end Dsub
