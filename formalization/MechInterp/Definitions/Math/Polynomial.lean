import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Real.Basic

set_option linter.style.header false

/-!
# Shifted-product polynomials

The polynomials `∏ h, (X + a_h)` and `∏_{j ≠ h} (X + a_j)` used by the real
partial-fraction identity.
-/

namespace MechInterp

open Polynomial

/-- The shifted product `∏ h, (X + a_h)`. -/
noncomputable def shiftProd {K : ℕ} (av : Fin K → ℝ) : ℝ[X] :=
  ∏ h : Fin K, (X + C (av h))

/-- The shifted product with the factor `h` removed: `∏_{j ≠ h} (X + a_j)`. -/
noncomputable def shiftProdErase {K : ℕ} (av : Fin K → ℝ) (h : Fin K) : ℝ[X] :=
  ∏ j ∈ Finset.univ.erase h, (X + C (av j))

end MechInterp
