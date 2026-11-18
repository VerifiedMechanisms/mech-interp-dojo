import Xorformer.Definitions.Prelude
import Xorformer.Definitions.Model.Head
import Xorformer.Definitions.Examples.TwoBit

set_option linter.style.header false

/-!
# Theorem 1: one attention head cannot compute XOR.

This module holds the definitions of this part of the development. Their proofs are in
`Xorformer.Theorems.Examples.OneHead`.

A single `Head 2 d` would give a one-head realization of the two-bit XOR
function, but the model-level checkerboard lower bound rules that out.
-/

namespace Xorformer

open MechInterp
open scoped InnerProductSpace

variable {d : ℕ} (H : Head 2 d)

/-- The Bool-product view of a two-bit input. -/
def pairBits (ab : Bool × Bool) : Fin 2 → Bool :=
  bits2 ab.1 ab.2

/-- The attention numerator as a Bool-product map. -/
noncomputable def boolNumerator (H : Head 2 d) (ab : Bool × Bool) : Vec d :=
  H.numerator (pairBits ab)

/-- The attention denominator as a Bool-product map. -/
noncomputable def boolDenominator (H : Head 2 d) (ab : Bool × Bool) : ℝ :=
  H.denominator (pairBits ab)

/-- The attention update as a Bool-product map. -/
noncomputable def boolUpdate (H : Head 2 d) (ab : Bool × Bool) : Vec d :=
  H.attnUpdate (pairBits ab)

/-- The **midpoint** `P` of the four attention outputs: `𝒟⁻¹ • 𝒩`. -/
noncomputable def midpoint : Vec d :=
  (boolDenominator H (false, false) + boolDenominator H (true, true))⁻¹
  • (boolNumerator H (false, false) + boolNumerator H (true, true))

end Xorformer
