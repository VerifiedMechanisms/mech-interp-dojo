import Xorformer.Theorems.Polynomial.ModelToPolynomial
import Xorformer.Theorems.Polynomial.ParityThresholdDegree

set_option linter.style.header false

/-!
# Result-facing threshold-degree bounds.

The polynomial modules define threshold degree and prove polynomial facts. This
module exposes the parts of that machinery that are headline results for head
complexity: heads imply low threshold degree, and parity has threshold degree `n`.
-/

namespace Xorformer

open MechInterp
/-- **Theorem 6.** `H` heads give a degree-`≤ H` sign representation. -/
alias degree_le_of_reducedComputableWithHeads := signReprDegLe_of_reducedComputableWithHeads

/-- **Theorem 7.** Parity has threshold degree exactly `n`. -/
alias parity_thresholdDeg := thresholdDeg_parity

end Xorformer
