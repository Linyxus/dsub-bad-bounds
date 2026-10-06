import Resolution.Final
import Resolution.Trans

/-!
# Subtyping in kernel D<: with bad bounds is decidable

The main theorem. The definitions it is about are in `Dsub/Basic.lean`. The proof is in the
modules under `Resolution/` and ends in `Resolution/Final.lean`; `Resolution/Trans.lean`
proves, separately, that transitivity is admissible.
-/

namespace Dsub

/-- Subtyping in kernel D<: with bad bounds is decidable: some algorithm decides, for every
code, whether it names a judgment that holds. -/
theorem decidable : ComputablePred Subtyping :=
  subtyping_computable

end Dsub
