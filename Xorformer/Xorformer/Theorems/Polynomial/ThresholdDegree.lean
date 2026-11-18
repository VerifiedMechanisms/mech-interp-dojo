import Xorformer.Definitions.Polynomial.ThresholdDegree
import Xorformer.Theorems.BooleanCube.SymmetricSignChanges
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.CommRing

set_option linter.style.header false

/-!
# Threshold (sign-representation) degree on the Boolean cube.

The definitions used here are in `Xorformer.Definitions.Polynomial.ThresholdDegree`.

Foundation for the Theorem 12 lower bound `H^{*}(f) ≥ C(F)`. We encode a Boolean
function `f : (Fin n → Bool) → Bool` and ask for a real polynomial whose sign
matches `f` at every cube point; the least total degree of such a polynomial is
the threshold degree. The lower-bound chain is:

`reducedComputableWithHeads n H f  ⇒  ThresholdDegLE f H`  (each head clears to a
degree-≤1 affine ratio; `H` heads to a degree-≤H polynomial), and for symmetric
`f`, `ThresholdDegLE f H ⇒ signChanges ≤ H`.
-/

namespace Xorformer

open MechInterp
open MvPolynomial

variable {n : ℕ}

end Xorformer
