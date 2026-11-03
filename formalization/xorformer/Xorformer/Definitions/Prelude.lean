import MechInterp.Definitions.Algebra.Spaces
import MechInterp.Theorems.Algebra.Spaces
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin

set_option linter.style.header false

/-!
# Shared imports for XORFormer

Every XORFormer module imports this prelude. It brings in the `MechInterp` vector spaces:
`Vec d = RVec (Fin d) = EuclideanSpace ℝ (Fin d)` and streams `Stream P V = P → V`. It also
brings in the Mathlib modules the head-complexity development relies on.

XORFormer imports only `Mathlib`, `MechInterp`, and `Xorformer` modules.
-/
