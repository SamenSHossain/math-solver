import Mathlib
import Definitions.Def_SmaleDiffS4_Basic

open SmaleDiffS4
open scoped ContDiff

namespace SmaleDiffS4

/-- **`Diff(D¹ rel ∂)` is path-connected.** Every diffeomorphism of `ℝ` that is the identity
outside the open unit interval is joined to the identity by the straight-line isotopy
`(1 - t) x + t f(x)`, which is a path in the `C^∞` topology. -/
theorem diffDisk_one_pathConnected : PathConnectedSpace (DiffDisk 1) := by
  sorry

end SmaleDiffS4
