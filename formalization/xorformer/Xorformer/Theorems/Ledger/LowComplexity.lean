import Xorformer.Theorems.Model.Computability
import Xorformer.Theorems.Results.LowComplexity

set_option linter.style.header false

/-!
# Ledger 11: the zero- and one-head levels

`H*(f) = 0` exactly for constant functions, and `H*(f) = 1` exactly for nonconstant linear
threshold functions.
-/

namespace Xorformer

variable {n : ℕ}

/-- Zero literal heads compute exactly the constant functions. -/
theorem computableWithHeads_zero_iff (f : (Fin n → Bool) → Bool) :
    ComputableWithHeads n 0 f ↔ ∀ x y, f x = f y := by
  rw [computableWithHeads_iff_reduced]; exact reducedComputableWithHeads_zero_iff f

/-- One literal head computes exactly the linear threshold functions. -/
theorem computableWithHeads_one_iff_isLTF (f : (Fin n → Bool) → Bool) :
    ComputableWithHeads n 1 f ↔ isLTF f := by
  rw [computableWithHeads_iff_reduced]
  exact ⟨isLTF_of_computable_one f, computable_one_of_isLTF f⟩

/-- **Theorem 11 (level 0).** -/
theorem HStar_eq_zero_iff (f : (Fin n → Bool) → Bool) : HStar n f = 0 ↔ ∀ x y, f x = f y := by
  rw [HStar_eq_ReducedHStar]; exact ReducedHStar_eq_zero_iff f

/-- **Theorem 11 (level 1).** -/
theorem HStar_eq_one_iff (f : (Fin n → Bool) → Bool) :
    HStar n f = 1 ↔ (¬ (∀ x y, f x = f y) ∧ isLTF f) := by
  rw [HStar_eq_ReducedHStar]; exact ReducedHStar_eq_one_iff f

end Xorformer
