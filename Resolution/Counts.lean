import Resolution.Annot
import Resolution.Thin
import Mathlib.Data.Set.Card

/-!
Counting variables: those occurring in a type, the created ones and the others.
-/

namespace Dsub

/-- The number of variables occurring in a type. -/
noncomputable def Ty.occCount {n : ℕ} (T : Ty n) : ℕ := {x | T.Occ x}.ncard

/-- The number of created variables. -/
noncomputable def Ann.nCreated {n : ℕ} (a : Ann n) : ℕ := {x | a.cr x}.ncard

/-- The number of non-created variables. -/
noncomputable def Ann.nBase {n : ℕ} (a : Ann n) : ℕ := {x | ¬ a.cr x}.ncard

end Dsub
