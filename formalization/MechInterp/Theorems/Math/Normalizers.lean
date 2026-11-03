import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

set_option linter.style.header false

/-!
# Positive finite normalizers

Model-independent facts about finite sums of positive weights and two-term weighted
averages. Attention normalizers specialize these facts.
-/

namespace MechInterp

open Finset

/-- A finite sum of strictly positive terms over a nonempty type is strictly positive. -/
theorem positiveNormalizer_pos {ι : Type*} [Fintype ι] [Nonempty ι]
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) : 0 < ∑ i, w i :=
  Finset.sum_pos (fun i _ => hw i) Finset.univ_nonempty

/-- A finite sum of strictly positive terms over a nonempty finset is strictly positive. -/
theorem positiveNormalizer_pos_of_nonempty {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    (w : ι → ℝ) (hw : ∀ i ∈ s, 0 < w i) : 0 < ∑ i ∈ s, w i :=
  Finset.sum_pos hw hs

/-- A two-term normalized weighted sum written with divisions is the inverse-scaled sum of
its weighted summands. -/
theorem twoTermWeightedAverage_eq_inv_smul_sum
    {V : Type*} [AddCommGroup V] [Module ℝ V] (a b : ℝ) (u v : V) :
    (a / (a + b)) • u + (b / (a + b)) • v = (a + b)⁻¹ • (a • u + b • v) := by
  rw [smul_add, smul_smul, smul_smul]
  congr 1
  · rw [div_eq_mul_inv, mul_comm]
  · rw [div_eq_mul_inv, mul_comm]

end MechInterp
