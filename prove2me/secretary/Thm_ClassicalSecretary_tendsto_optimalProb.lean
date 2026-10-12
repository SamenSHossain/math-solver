import Mathlib
import Definitions.Def_ClassicalSecretary_Model

open Finset Filter Topology

namespace ClassicalSecretary

theorem tendsto_optimalProb :
    Tendsto optimalProb atTop (𝓝 (Real.exp (-1))) := by sorry

end ClassicalSecretary
