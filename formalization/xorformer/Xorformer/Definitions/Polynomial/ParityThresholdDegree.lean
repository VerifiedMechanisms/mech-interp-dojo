import Xorformer.Definitions.Prelude
import Xorformer.Definitions.Polynomial.UnivariateReduction

set_option linter.style.header false

/-!
# Theorem 7 — parity has threshold degree exactly `n`.

This module holds the definitions of this part of the development. Their proofs are in
`Xorformer.Theorems.Polynomial.ParityThresholdDegree`.

`deg±(PARITY_n) = n`, where `deg±` is the least total degree of a real polynomial
sign-representing the function on the Boolean cube (`thresholdDeg` below).

* **Upper bound** `deg± ≤ n`: the witness `P := -∏ i, (1 - 2 X_i)` evaluates on the
  cube to `-(-1)^{|x|}`, which is positive exactly when `|x|` is odd, i.e. when
  `PARITY_n x` is true; it has total degree `≤ n`.
* **Lower bound** `n ≤ deg±`: reuse the symmetric lower-bound machinery
  `signChanges_le_of_ThresholdDegLE` — any sign representation of total degree `H`
  forces `signChanges n (parity profile) = n ≤ H`.
-/

namespace Xorformer

open MechInterp
open MvPolynomial Finset

variable {n : ℕ}

/-- The (sign-representation) threshold degree `deg±(f)`: the least `d` for which a
real polynomial of total degree `≤ d` sign-represents `f` on the cube. -/
noncomputable def thresholdDeg (f : (Fin n → Bool) → Bool) : ℕ := by
  classical
  exact if h : ∃ d, ThresholdDegLE f d then Nat.find h else 0

/-! ## The parity sign polynomial `-∏ (1 - 2 X_i)` -/

/-! ## Theorem 7 -/

end Xorformer
