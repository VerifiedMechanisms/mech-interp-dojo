import Xorformer.Theorems.Model.Computability
import Xorformer.Theorems.Results.WeightedUpperBound

set_option linter.style.header false

/-!
# Ledger 9: weighted and universal upper bounds

If `f` factors through a positive weighted statistic `t(x) = ∑_{x_i} λ_i` with `M` distinct
values, then `H* ≤ M - 1`. In particular, `H* ≤ 2ⁿ - 1` for every `f`.
-/

namespace Xorformer

variable {n : ℕ}

/-- **Theorem 9 (weighted).** -/
theorem HStar_le_weighted_sum (lam : Fin n → ℝ) (hlam : ∀ i, 0 < lam i)
    (f : (Fin n → Bool) → Bool) (G : ℝ → Bool) (hf : ∀ bits, f bits = G (wT lam bits)) :
    HStar n f ≤ (Finset.univ.image (wT lam)).card - 1 := by
  rw [HStar_eq_ReducedHStar]; exact ReducedHStar_le_weighted_sum lam hlam f G hf

/-- **Theorem 9 (universal).** -/
theorem HStar_le_universal (f : (Fin n → Bool) → Bool) : HStar n f ≤ 2 ^ n - 1 := by
  rw [HStar_eq_ReducedHStar]; exact ReducedHStar_le_universal_boolean f

end Xorformer
