import Xorformer.Theorems.Examples.BooleanFunctions
import Xorformer.Theorems.Model.Computability

set_option linter.style.header false

/-!
# Two-bit examples in the literal model

The exact head complexity of every two-bit example, stated for the literal XORFormer:

* zero heads for the constant functions;
* one head for OR, AND, NOR, and NAND;
* two heads for XOR and XNOR;
* the full table for symmetric two-bit functions.

The XOR example is spelled out: no single literal head computes XOR, and an explicit pair of
heads, widened from `xorTwoHeadFamily`, does.
-/

namespace Xorformer

open MechInterp

/-- On two bits, the literal and reduced complexities agree. -/
theorem HStar_two_eq_ReducedHStar2 (f : (Fin 2 → Bool) → Bool) :
    HStar 2 f = ReducedHStar2 f :=
  HStar_eq_ReducedHStar f

theorem HStar_falseFn : HStar 2 falseFn = 0 := by
  rw [HStar_two_eq_ReducedHStar2]; exact ReducedHStar_false

theorem HStar_trueFn : HStar 2 trueFn = 0 := by
  rw [HStar_two_eq_ReducedHStar2]; exact ReducedHStar_true

theorem HStar_orFn : HStar 2 orFn = 1 := by
  rw [HStar_two_eq_ReducedHStar2]; exact ReducedHStar_or

theorem HStar_andFn : HStar 2 andFn = 1 := by
  rw [HStar_two_eq_ReducedHStar2]; exact ReducedHStar_and

theorem HStar_norFn : HStar 2 norFn = 1 := by
  rw [HStar_two_eq_ReducedHStar2]; exact ReducedHStar_nor

theorem HStar_nandFn : HStar 2 nandFn = 1 := by
  rw [HStar_two_eq_ReducedHStar2]; exact ReducedHStar_nand

theorem HStar_xorFn : HStar 2 xorFn = 2 := by
  rw [HStar_two_eq_ReducedHStar2]; exact ReducedHStar_xor

theorem HStar_xnorFn : HStar 2 xnorFn = 2 := by
  rw [HStar_two_eq_ReducedHStar2]; exact ReducedHStar_xnor

/-- Every symmetric two-bit function has the listed literal head complexity. -/
theorem HStar_symmFn (c0 c1 c2 : Bool) :
    HStar 2 (symmFn c0 c1 c2) =
      (if c0 = c1 then if c1 = c2 then 0 else 1 else if c0 = c2 then 2 else 1) := by
  rw [HStar_two_eq_ReducedHStar2]; exact ReducedHStar_symmFn c0 c1 c2

/-- No single literal head computes XOR. -/
theorem xor_not_computableWithHeads_one : ¬ ComputableWithHeads 2 1 xorFn := by
  rw [computableWithHeads_iff_reduced]; exact xor_not_computable_with_one_head_count

/-- Two literal heads compute XOR. -/
theorem xor_computableWithHeads_two : ComputableWithHeads 2 2 xorFn :=
  (computableWithHeads_iff_reduced 2 xorFn).mpr xor_computable_with_two_heads_count

/-- An explicit literal two-head XOR model: the widening of `xorTwoHeadFamily`. -/
theorem exists_literal_xor_model :
    ∃ (w : Vec 3) (τ : ℝ), (toLiteral xorTwoHeadFamily w τ).Computes xorFn := by
  obtain ⟨w, τ, hw⟩ := xor_computable_with_two_heads
  refine ⟨w, τ, toLiteral_computes xorTwoHeadFamily w τ fun bits => ?_⟩
  have h := xorTwoHeadFamily_attnUpdate bits
  rw [twoBitHeadFamilyAttnUpdate] at h
  rw [h]
  exact hw bits

end Xorformer
