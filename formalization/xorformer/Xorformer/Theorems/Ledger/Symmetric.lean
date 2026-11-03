import Xorformer.Theorems.Ledger.ThresholdDegree
import Xorformer.Theorems.Results.SymmetricComplexity
import Xorformer.Theorems.Polynomial.UnivariateReduction

set_option linter.style.header false

/-!
# Ledger 12: symmetric Boolean functions

For a symmetric function with weight profile `F`, head complexity, threshold degree, and the
number of sign changes `C(F)` of the profile along `0, …, n` coincide:

`H*(f) = deg±(f) = C(F)`.
-/

namespace Xorformer

variable {n : ℕ}

/-- **Theorem 12.** Head complexity of a symmetric function is its sign-change count. -/
theorem HStar_symmetricFn (F : ℕ → Bool) (n : ℕ) :
    HStar n (symmetricFn F) = signChanges n F := by
  rw [HStar_eq_ReducedHStar, ReducedHStar_symmetricFn]

/-- **Theorem 12 (threshold degree).** The threshold degree of a symmetric function is its
sign-change count. -/
theorem thresholdDeg_symmetricFn (F : ℕ → Bool) (n : ℕ) :
    thresholdDeg (n := n) (symmetricFn F) = signChanges n F := by
  apply le_antisymm
  · rw [← HStar_symmetricFn F n]; exact thresholdDeg_le_HStar _
  · exact signChanges_le_of_ThresholdDegLE (thresholdDegLE_thresholdDeg _)

/-- **Theorem 12 (equality with threshold degree).** -/
theorem HStar_symmetricFn_eq_thresholdDeg (F : ℕ → Bool) (n : ℕ) :
    HStar n (symmetricFn F) = thresholdDeg (n := n) (symmetricFn F) := by
  rw [HStar_symmetricFn, thresholdDeg_symmetricFn]

end Xorformer
