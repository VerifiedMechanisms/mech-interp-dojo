import Xorformer.Theorems.Model.Computability
import Xorformer.Theorems.Results.FractionalNormalForm

set_option linter.style.header false

/-!
# Ledger 10: the linear-fractional normal form

For every head count `H`, a literal XORFormer with `H` heads computes `f` exactly when `f`
is the sign of a constant plus `H` constrained linear-fractional atoms. Hence
`H*(f) = L_frac(f)`.
-/

namespace Xorformer

variable {n : ℕ}

/-- **Theorem 10 (per head count).** -/
theorem computableWithHeads_iff_fracComputable (H : ℕ) (f : (Fin n → Bool) → Bool) :
    ComputableWithHeads n H f ↔ fracComputable n H f :=
  (computableWithHeads_iff_reduced H f).trans (reducedComputableWithHeads_iff_fracComputable H f)

/-- **Theorem 10 (minima).** -/
theorem HStar_eq_Lfrac (f : (Fin n → Bool) → Bool) : HStar n f = Lfrac n f := by
  rw [HStar_eq_ReducedHStar, ReducedHStar_eq_Lfrac]

/-- The literal model and the reduced shared-embedding family have the same complexity. -/
theorem HStar_eq_SharedHStar (f : (Fin n → Bool) → Bool) : HStar n f = SharedHStar n f := by
  rw [HStar_eq_ReducedHStar, SharedHStar_eq_ReducedHStar]

end Xorformer
