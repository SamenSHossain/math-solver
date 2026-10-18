import Mathlib
import Definitions.Def_NavierStokesAlternating

namespace OAI

open scoped BigOperators ENNReal Topology ContDiff

open MeasureTheory

namespace AlternatingNS

/-- **Computable force compiler.** For a positive computable viscosity `ν` there is a computable
map on field programs sending any program for a smooth, rapidly decaying, compactly supported
velocity `U` to a program for the force `f = ∂ₜU + (U·∇)U − νΔU`. -/
theorem force_compiler (ν : ℝ) (hν : 0 < ν) (hc : ComputableReal ν) :
    ∃ compileForce : FieldProgram → FieldProgram, Computable compileForce ∧
      ∀ (c : FieldProgram) (U : Velocity) (K : Set Space), IsCompact K →
        Smooth U → SupportedIn U K → Rapid U → ProgramFor c U →
        ProgramFor (compileForce c) (residual ν U) := by
  sorry

end AlternatingNS
end OAI
