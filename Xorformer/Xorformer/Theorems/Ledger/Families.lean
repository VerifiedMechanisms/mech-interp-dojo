import Xorformer.Theorems.Model.Computability
import Xorformer.Theorems.Results.ExactFamilies
import Xorformer.Theorems.BooleanCube.Families

set_option linter.style.header false

/-!
# Ledger 4, 5, 8: standard symmetric families in the literal model

4. Monotone symmetric thresholds `[|x| ≥ t]` with `1 ≤ t ≤ n` have `H* = 1`.
5. Parity and internal exact-count predicates are not computable with fewer than two heads,
   and `H*(EXACT n k) = 2` for `1 ≤ k ≤ n - 1`.
8. Parity needs one head per bit: `H*(PARITY n) = n`.
-/

namespace Xorformer

variable {n : ℕ}

/-- **Theorem 4.** -/
theorem HStar_threshold (t : ℕ) (ht1 : 1 ≤ t) (htn : t ≤ n) : HStar n (THRESHOLD n t) = 1 := by
  rw [HStar_eq_ReducedHStar, ReducedHStar_threshold t ht1 htn]

/-- **Theorem 5 (parity, one head).** -/
theorem PARITY_not_computableWithHeads_one (hn : 2 ≤ n) :
    ¬ ComputableWithHeads n 1 (PARITY n) := by
  rw [computableWithHeads_iff_reduced]; exact PARITY_not_computable_with_one_head hn

/-- **Theorem 5 (parity, zero heads).** -/
theorem PARITY_not_computableWithHeads_zero (hn : 2 ≤ n) :
    ¬ ComputableWithHeads n 0 (PARITY n) := by
  rw [computableWithHeads_iff_reduced]; exact PARITY_not_computable_with_zero_heads hn

/-- **Theorem 5 (parity).** Parity needs at least two heads. -/
theorem PARITY_HStar_ge_two (hn : 2 ≤ n) : 2 ≤ HStar n (PARITY n) := by
  refine le_HStar_of_not_computable fun k hk => ?_
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · exact PARITY_not_computableWithHeads_zero hn
  · exact PARITY_not_computableWithHeads_one hn

/-- **Theorem 5 (exact count, one head).** -/
theorem EXACT_not_computableWithHeads_one (hn : 2 ≤ n) {k : ℕ} (hk1 : 1 ≤ k)
    (hk2 : k ≤ n - 1) : ¬ ComputableWithHeads n 1 (EXACT n k) := by
  rw [computableWithHeads_iff_reduced]; exact EXACT_not_computable_with_one_head hn hk1 hk2

/-- **Theorem 5 (exact count, zero heads).** -/
theorem EXACT_not_computableWithHeads_zero {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ n) :
    ¬ ComputableWithHeads n 0 (EXACT n k) := by
  rw [computableWithHeads_iff_reduced]; exact EXACT_not_computable_with_zero_heads hk1 hk2

/-- **Theorem 5 (exact count).** Internal exact-count predicates need exactly two heads. -/
theorem HStar_exact (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n - 1) : HStar n (EXACT n k) = 2 := by
  rw [HStar_eq_ReducedHStar, ReducedHStar_exact k hk1 hkn]

/-- **Theorem 8.** Parity needs exactly one head per bit. -/
theorem HStar_parity (n : ℕ) : HStar n (PARITY n) = n := by
  rw [HStar_eq_ReducedHStar, ReducedHStar_parity]

end Xorformer
