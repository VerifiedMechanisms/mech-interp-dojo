import Xorformer.Definitions.Prelude
import Xorformer.Definitions.BooleanCube.SymmetricSignChanges
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option linter.style.header false

/-!
# Sign polynomial for a weight profile (L12 upper bound).

This module holds the definitions of this part of the development. Their proofs are in
`Xorformer.Theorems.Atoms.SignPolynomial`.

For `F : ℕ → Bool` and `n`, we build `P : ℝ[X]` with `natDegree P ≤ signChanges n F`
and, for every `k ≤ n`, `0 < P.eval k ↔ F k = true`.  `P` places a root at each
half-integer `t + 1/2` where `F` changes between `t` and `t+1`, scaled by a global
sign chosen from `F n`.
-/

open Polynomial Finset

namespace Xorformer

open MechInterp
variable (F : ℕ → Bool) (n : ℕ)

/-- The set of sign-change positions of `F` below `n`. -/
def changeSet : Finset ℕ := (Finset.range n).filter (fun t => F t ≠ F (t + 1))

/-- Number of sign changes at position `≥ k`. -/
def negCount (k : ℕ) : ℕ := ((changeSet F n).filter (fun t => k ≤ t)).card

end Xorformer
