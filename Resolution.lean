import Dsub
import Resolution.Syntax
import Resolution.Lemmas
import Resolution.Trans
import Resolution.Decide
import Resolution.Height
import Resolution.Thin
import Resolution.Annot
import Resolution.Collapse
import Resolution.Family
import Resolution.FamilyEnum
import Resolution.Sized
import Resolution.Skeleton
import Resolution.Counts
import Resolution.Good
import Resolution.NormFam
import Resolution.PrimBasic
import Resolution.PrimFix
import Resolution.PrimCodes
import Resolution.PrimCtx
import Resolution.BoundCode
import Resolution.Bound
import Resolution.BoundPrim
import Resolution.Glue
import Resolution.PrimFires
import Resolution.PrimDecide
import Resolution.Final

/-!
The two alternatives. Exactly one of them is true; prove one of them. Put helper definitions
and lemmas in modules under `Resolution/` imported from here, or in this file.
-/

namespace Dsub

/-- Subtyping in kernel D<: with bad bounds is decidable: some algorithm decides, for every
code, whether it names a judgment that holds. -/
theorem decidable : ComputablePred Subtyping :=
  subtyping_computable

/-- Subtyping in kernel D<: with bad bounds is undecidable: no algorithm decides, for every
code, whether it names a judgment that holds. -/
theorem undecidable : ¬ ComputablePred Subtyping := by
  sorry

end Dsub
