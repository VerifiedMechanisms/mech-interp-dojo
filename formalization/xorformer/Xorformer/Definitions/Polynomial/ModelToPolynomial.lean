import Xorformer.Definitions.Prelude
import Xorformer.Definitions.Polynomial.ThresholdDegree

set_option linter.style.header false

/-!
# Model → polynomial bridge (Theorem 6 / L12 lower bound, Phase 2).

This module holds the definitions of this part of the development. Their proofs are in
`Xorformer.Theorems.Polynomial.ModelToPolynomial`.

`reducedComputableWithHeads n H f → ThresholdDegLE f H`: any function computed by `H`
attention heads has a real polynomial of total degree `≤ H` whose sign matches
`f` on the cube.

The mechanism is purely Boolean-finite: each softmax weight `σ_p` and each value
readout depends, under a fixed head, on **one** input bit (or none, for the query
token), and any `{0,1} → ℝ` function is its own affine (degree ≤ 1) interpolant.
So each head's numerator readout and denominator are affine (degree ≤ 1) in the
bits, with denominator `> 0`. Clearing the positive product of denominators turns
the `H`-head thresholded score into a single polynomial of total degree `≤ H`.
-/

namespace Xorformer

open MechInterp
open MvPolynomial
open scoped InnerProductSpace BigOperators

variable {n d : ℕ}

/-! ## Affine (degree ≤ 1) gadget -/

/-- Affine polynomial matching a 2-valued function at position `p`. -/
noncomputable def affineAt (p : Fin n) (vf vt : ℝ) : MvPolynomial (Fin n) ℝ :=
  C vf + C (vt - vf) * X p

/-! ## Single-position dependence of one head -/

variable (H : Head n d)

/-! ## Per-head denominator and numerator-readout polynomials -/

/-! ## Degree helpers -/

/-! ## Main theorem (Theorem 6): `H` heads give a degree-≤H sign representation. -/

end Xorformer
