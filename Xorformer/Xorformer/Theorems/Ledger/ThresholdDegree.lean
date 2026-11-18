import Xorformer.Theorems.Model.Computability
import Xorformer.Theorems.Results.ThresholdDegree

set_option linter.style.header false

/-!
# Ledger 6–7: threshold degree

6. `H` literal heads give a sign representation of degree at most `H`, so
   `thresholdDeg f ≤ HStar n f`.
7. Parity has threshold degree exactly `n`.
-/

namespace Xorformer

variable {n : ℕ}

/-- **Theorem 6.** `H` literal heads give a degree-`≤ H` sign representation. -/
theorem thresholdDegLE_of_computableWithHeads {H : ℕ} {f : (Fin n → Bool) → Bool}
    (h : ComputableWithHeads n H f) : ThresholdDegLE f H :=
  degree_le_of_reducedComputableWithHeads ((computableWithHeads_iff_reduced H f).mp h)

/-- Every Boolean function has a sign representation of some degree. -/
theorem exists_thresholdDegLE (f : (Fin n → Bool) → Bool) : ∃ d, ThresholdDegLE f d :=
  ⟨_, thresholdDegLE_of_computableWithHeads (HStar_computable f)⟩

/-- The threshold degree is attained. -/
theorem thresholdDegLE_thresholdDeg (f : (Fin n → Bool) → Bool) :
    ThresholdDegLE f (thresholdDeg f) := by
  classical
  have hex := exists_thresholdDegLE f
  unfold thresholdDeg
  rw [dif_pos hex]
  exact Nat.find_spec hex

/-- A sign representation of degree `d` bounds the threshold degree above. -/
theorem thresholdDeg_le_of_thresholdDegLE {f : (Fin n → Bool) → Bool} {d : ℕ}
    (h : ThresholdDegLE f d) : thresholdDeg f ≤ d := by
  classical
  have hex : ∃ d, ThresholdDegLE f d := ⟨d, h⟩
  unfold thresholdDeg
  rw [dif_pos hex]
  exact Nat.find_min' hex h

/-- **Theorem 6 (numeric form).** Threshold degree is at most head complexity. -/
theorem thresholdDeg_le_HStar (f : (Fin n → Bool) → Bool) : thresholdDeg f ≤ HStar n f :=
  thresholdDeg_le_of_thresholdDegLE (thresholdDegLE_of_computableWithHeads (HStar_computable f))

/-- **Theorem 7.** Parity has threshold degree exactly `n`. -/
theorem thresholdDeg_PARITY (n : ℕ) : thresholdDeg (PARITY n) = n := parity_thresholdDeg n

end Xorformer
