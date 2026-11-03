import Xorformer.Theorems.Results.RestrictionLowerBounds
import Xorformer.Theorems.Results.ExactFamilies
import Xorformer.Theorems.Results.ThresholdDegree
import Xorformer.Theorems.Results.WeightedUpperBound
import Xorformer.Theorems.Results.FractionalNormalForm
import Xorformer.Theorems.Results.LowComplexity
import Xorformer.Theorems.Results.SymmetricComplexity
import Xorformer.Theorems.Results.StrictSeparation

set_option linter.style.header false

/-!
# Main results: the stack of entry points to the theory developed so far

A machine-checked table of contents. Each foundational `alias` below names the
headline Lean statement for one theorem writeup in `theorems/`. Because the build
elaborates these aliases, this file *verifies* every result. These results must be
axiom-clean (`[propext, Classical.choice, Quot.sound]`).

See `README.md` for the theorem↔file map and `PROOF_OVERVIEW.md` for the proof
architecture.
-/

namespace Xorformer

open MechInterp
/-! ## Results regarding softmax beyond the H* -/

/-- **Theorem 1.** The numerator, restricted to two coordinates, splits additively. -/
alias reduced_theorem1_additive_split := restricted_numerator_additive_split

/-- **Theorem 2.** Antipode identity for the restricted numerator. -/
alias reduced_theorem2_antipode := restricted_numerator_antipode

/-! ## Lower bound results for H* -/

/-- **Theorem 3.** A checkerboard restriction forces `H* ≥ 2`. -/
alias reduced_theorem3_checkerboard := checkerboard_restriction_ReducedHStar_ge_two

/-! ## Results for H* for specific boolean functions -/

/-- **Theorem 4.** Every monotone symmetric threshold has `H* = 1`. -/
alias reduced_theorem4_threshold := ReducedHStar_threshold

/-- **Theorem 5.** Internal exact-count predicates have `H* = 2`. -/
alias reduced_theorem5_exact := ReducedHStar_exact

/-- **Theorem 8.** Parity needs one head per bit: `H*(XOR_n) = n`. -/
alias reduced_theorem8_parity := ReducedHStar_parity

/-! ## Results regarding threshold degree beyond the H* -/

/-- **Theorem 6.** Threshold degree is bounded by head complexity:
`reducedComputableWithHeads n H f → ThresholdDegLE f H`. -/
alias reduced_theorem6_degree_le := degree_le_of_reducedComputableWithHeads

/-- **Theorem 7.** Parity has threshold degree exactly `n`. -/
alias reduced_theorem7_parity_degree := parity_thresholdDeg

/-! ## Upper bound results for H* -/

/-- **Theorem 9.** Weighted-sum upper bound `H* ≤ M − 1` … -/
alias reduced_theorem9_weighted := ReducedHStar_le_weighted_sum

/-- … and the universal bound `H* ≤ 2ⁿ − 1`. -/
alias reduced_theorem9_universal := ReducedHStar_le_universal_boolean

/-! ## Exact results for H* -/

/-- **Theorem 10.** Exact linear-fractional normal form: `H*(f) = L_frac(f)`. -/
alias reduced_theorem10_normal_form := ReducedHStar_eq_Lfrac

/-- **Theorem 10.** The same normal form for the literal shared-embedding model. -/
alias reduced_theorem10_shared_embedding_per_head_count :=
  computableWithSharedHeadsN_iff_fracComputable

/-- **Theorem 10.** Exact shared-embedding head complexity equals `L_frac`. -/
alias reduced_theorem10_shared_embedding_normal_form := SharedHStar_eq_Lfrac

/-- **Theorem 11.** `H* = 0` iff `f` is constant … -/
alias reduced_theorem11_level0 := ReducedHStar_eq_zero_iff

/-- … and `H* = 1` iff `f` is a nonconstant linear threshold function. -/
alias reduced_theorem11_level1 := ReducedHStar_eq_one_iff

/-- **Theorem 12.** Symmetric sign-change characterization:
`H*(symmetricFn F) = signChanges n F`. -/
alias reduced_theorem12_symmetric := ReducedHStar_symmetricFn

/-! ## Separation results for H* -/

/-- **Theorem 13.** Threshold degree can be strictly smaller than head
complexity. -/
alias reduced_theorem13_strict_separation := f10_strict_separation

end Xorformer
