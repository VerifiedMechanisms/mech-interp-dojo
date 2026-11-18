import Xorformer.Theorems.Ledger.Restrictions
import Xorformer.Theorems.Ledger.Families
import Xorformer.Theorems.Ledger.ThresholdDegree
import Xorformer.Theorems.Ledger.UpperBounds
import Xorformer.Theorems.Ledger.NormalForm
import Xorformer.Theorems.Ledger.LowComplexity
import Xorformer.Theorems.Ledger.Symmetric
import Xorformer.Theorems.Ledger.Separation

set_option linter.style.header false

/-!
# The theorem ledger for the literal XORFormer

A machine-checked table of contents for `theorems.md`. Every statement is about the literal
model of `model.md`: a shared additive embedding, rectangular projections with an explicit
`W_O`, full softmax attention, the constant query residual, and an affine probe at the query.
`HStar` is its head complexity. The reduced head-local model appears only through the
certified bridges at the end.
-/

namespace Xorformer

/-! ## Results on single heads -/

/-- **Theorem 1 (numerator).** Restricted literal-head numerators split additively. -/
alias theorem1_numerator_additive_split := literal_numerator_additive_split

/-- **Theorem 1 (denominator).** Restricted literal-head denominators split additively. -/
alias theorem1_denominator_additive_split := literal_denominator_additive_split

/-- **Theorem 2 (numerator).** Antipode identity for restricted literal-head numerators. -/
alias theorem2_numerator_antipode := literal_numerator_antipode

/-- **Theorem 2 (denominator).** Antipode identity for restricted literal-head
denominators. -/
alias theorem2_denominator_antipode := literal_denominator_antipode

/-! ## Lower bounds -/

/-- **Theorem 3.** A checkerboard restriction forces `H* ≥ 2`. -/
alias theorem3_checkerboard := checkerboard_HStar_ge_two

/-- **Theorem 3 (one head).** A checkerboard restriction is not one-head computable. -/
alias theorem3_checkerboard_one_head := checkerboard_not_computableWithHeads_one

/-- **Theorem 5 (parity).** Parity needs at least two heads. -/
alias theorem5_parity_ge_two := PARITY_HStar_ge_two

/-- **Theorem 5 (exact count).** Internal exact-count predicates are not one-head
computable. -/
alias theorem5_exact_not_one_head := EXACT_not_computableWithHeads_one

/-! ## Exact complexities of standard families -/

/-- **Theorem 4.** Monotone symmetric thresholds have `H* = 1`. -/
alias theorem4_threshold := HStar_threshold

/-- **Theorem 5.** Internal exact-count predicates have `H* = 2`. -/
alias theorem5_exact := HStar_exact

/-- **Theorem 8.** Parity has `H* = n`. -/
alias theorem8_parity := HStar_parity

/-! ## Threshold degree -/

/-- **Theorem 6.** `H` heads give a degree-`≤ H` sign representation. -/
alias theorem6_degree_le := thresholdDegLE_of_computableWithHeads

/-- **Theorem 6 (numeric).** `deg±(f) ≤ H*(f)`. -/
alias theorem6_thresholdDeg_le_HStar := thresholdDeg_le_HStar

/-- **Theorem 7.** Parity has threshold degree `n`. -/
alias theorem7_parity_degree := thresholdDeg_PARITY

/-! ## Upper bounds -/

/-- **Theorem 9 (weighted).** `H* ≤ M - 1` for weighted-statistic functions. -/
alias theorem9_weighted := HStar_le_weighted_sum

/-- **Theorem 9 (universal).** `H* ≤ 2ⁿ - 1`. -/
alias theorem9_universal := HStar_le_universal

/-! ## Exact characterizations -/

/-- **Theorem 10 (per head count).** `H` heads ⟺ `H` linear-fractional atoms. -/
alias theorem10_normal_form_per_head_count := computableWithHeads_iff_fracComputable

/-- **Theorem 10.** `H*(f) = L_frac(f)`. -/
alias theorem10_normal_form := HStar_eq_Lfrac

/-- **Theorem 11 (level 0).** `H* = 0` iff `f` is constant. -/
alias theorem11_level0 := HStar_eq_zero_iff

/-- **Theorem 11 (level 1).** `H* = 1` iff `f` is a nonconstant linear threshold function. -/
alias theorem11_level1 := HStar_eq_one_iff

/-- **Theorem 12.** `H*(symmetricFn F) = signChanges n F`. -/
alias theorem12_symmetric := HStar_symmetricFn

/-- **Theorem 12 (threshold degree).** `deg±(symmetricFn F) = signChanges n F`. -/
alias theorem12_symmetric_thresholdDeg := thresholdDeg_symmetricFn

/-- **Theorem 12 (equality).** `H* = deg±` for symmetric functions. -/
alias theorem12_HStar_eq_thresholdDeg := HStar_symmetricFn_eq_thresholdDeg

/-! ## Separation -/

/-- **Theorem 13 (degree).** `deg±(f10) = 2`. -/
alias theorem13_degree_two := thresholdDeg_f10_eq_two

/-- **Theorem 13 (heads).** `H*(f10) ≥ 3`. -/
alias theorem13_heads_ge_three := HStar_f10_ge_three

/-- **Theorem 13.** `deg±(f10) < H*(f10)`. -/
alias theorem13_strict_separation := f10_strict_separation_literal

/-! ## The model and its certified reductions -/

/-- The literal score is `⟪w, u_q + ∑ h, W_O^{(h)} ∑ j, A_qj W_V^{(h)} u_j⟫ - τ`. -/
alias model_score_eq := LiteralParams.score_eq

/-- Causal and full masks give the same query readout. -/
alias model_causal_eq_full := LiteralParams.causalScore_eq_score

/-- Literal and reduced models are equivalent at every head count (width may change). -/
alias model_equivalence := computableWithHeads_iff_reduced

/-- Literal and reduced head complexities are equal. -/
alias model_HStar_eq_reduced := HStar_eq_ReducedHStar

/-- Every function is computable, and the minimum `HStar` is attained. -/
alias model_HStar_attained := HStar_computable

end Xorformer
