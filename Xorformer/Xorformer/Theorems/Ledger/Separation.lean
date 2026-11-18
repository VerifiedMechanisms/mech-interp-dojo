import Xorformer.Theorems.Model.Computability
import Xorformer.Theorems.Results.StrictSeparation

set_option linter.style.header false

/-!
# Ledger 13: threshold degree and head complexity separate

The explicit ten-bit function `f10` has threshold degree exactly two but needs at least three
literal heads.
-/

namespace Xorformer

/-- **Theorem 13 (degree).** -/
theorem thresholdDeg_f10_eq_two : thresholdDeg f10 = 2 := thresholdDeg_f10

/-- **Theorem 13 (two heads fail).** -/
theorem f10_not_computableWithHeads_two : ¬ ComputableWithHeads 10 2 f10 := by
  rw [computableWithHeads_iff_reduced]; exact f10_not_reducedComputableWithHeads_two

/-- **Theorem 13 (heads).** -/
theorem HStar_f10_ge_three : 3 ≤ HStar 10 f10 := by
  rw [HStar_eq_ReducedHStar]; exact ReducedHStar_f10_ge_three

/-- **Theorem 13.** Threshold degree is strictly smaller than head complexity. -/
theorem f10_strict_separation_literal : thresholdDeg f10 < HStar 10 f10 := by
  rw [HStar_eq_ReducedHStar]; exact f10_strict_separation

end Xorformer
