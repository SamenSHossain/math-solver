-- Smoke test: builds in seconds only if the toolchain, the pinned Mathlib
-- revision, and the unpacked cache are all correct.
--   lake build Solutions.SmokeTest
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

example (a b : ℝ) : a^2 + b^2 - 2*a*b ≥ 0 := by
  nlinarith [sq_nonneg (a - b)]
