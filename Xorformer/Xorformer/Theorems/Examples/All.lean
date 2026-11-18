import Xorformer.Theorems.Examples.OneHead
import Xorformer.Theorems.Examples.TwoHeads
import Xorformer.Theorems.Examples.BooleanFunctions
import Xorformer.Theorems.Examples.Literal

set_option linter.style.header false

/-!
# Examples umbrella.

This module collects the endpoint examples. The `example*` aliases are stated for the literal
XORFormer. The `reduced_example*` aliases are the original statements about the reduced
head-local model.
-/

namespace Xorformer

open MechInterp
/-- **Example 1.** No single head computes XOR from the residual stream. -/
alias reduced_example1_one_head_cannot_xor := one_head_cannot_xor_residual

/-- **Example 2.** The explicit two-head construction computes XOR. -/
alias reduced_example2_two_heads_compute_xor := two_heads_suffice

/-- **Example 3.** The constantly-false function has head complexity `0`. -/
alias reduced_example3_ReducedHStar_false := ReducedHStar_false

/-- **Example 4.** The constantly-true function has head complexity `0`. -/
alias reduced_example4_ReducedHStar_true := ReducedHStar_true

/-- **Example 5.** `OR` has head complexity `1`. -/
alias reduced_example5_ReducedHStar_or := ReducedHStar_or

/-- **Example 6.** `AND` has head complexity `1`. -/
alias reduced_example6_ReducedHStar_and := ReducedHStar_and

/-- **Example 7.** `NOR` has head complexity `1`. -/
alias reduced_example7_ReducedHStar_nor := ReducedHStar_nor

/-- **Example 8.** `NAND` has head complexity `1`. -/
alias reduced_example8_ReducedHStar_nand := ReducedHStar_nand

/-- **Example 9.** `XOR` has head complexity `2`. -/
alias reduced_example9_ReducedHStar_xor := ReducedHStar_xor

/-- **Example 10.** `XNOR` has head complexity `2`. -/
alias reduced_example10_ReducedHStar_xnor := ReducedHStar_xnor

/-- **Example 11.** Every symmetric two-bit Boolean function has the listed exact
head complexity. -/
alias reduced_example11_ReducedHStar_symmFn := ReducedHStar_symmFn

/-! ## Literal-model examples -/

/-- **Example 1.** No single literal head computes XOR. -/
alias example1_one_head_cannot_xor := xor_not_computableWithHeads_one

/-- **Example 2.** An explicit two-head literal model computes XOR. -/
alias example2_two_heads_compute_xor := exists_literal_xor_model

/-- **Example 3.** The constantly-false function has head complexity `0`. -/
alias example3_HStar_false := HStar_falseFn

/-- **Example 4.** The constantly-true function has head complexity `0`. -/
alias example4_HStar_true := HStar_trueFn

/-- **Example 5.** `OR` has head complexity `1`. -/
alias example5_HStar_or := HStar_orFn

/-- **Example 6.** `AND` has head complexity `1`. -/
alias example6_HStar_and := HStar_andFn

/-- **Example 7.** `NOR` has head complexity `1`. -/
alias example7_HStar_nor := HStar_norFn

/-- **Example 8.** `NAND` has head complexity `1`. -/
alias example8_HStar_nand := HStar_nandFn

/-- **Example 9.** `XOR` has head complexity `2`. -/
alias example9_HStar_xor := HStar_xorFn

/-- **Example 10.** `XNOR` has head complexity `2`. -/
alias example10_HStar_xnor := HStar_xnorFn

/-- **Example 11.** Every symmetric two-bit function has the listed head complexity. -/
alias example11_HStar_symmFn := HStar_symmFn

end Xorformer
