/-
Copyright (c) 2026 Malhar A. Patel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Malhar A. Patel
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

/-!
# Positive normalizers

Softmax and other attention rules divide by a *normalizer*: a finite sum of positive weights.
This file collects the model-independent facts about such sums.

## Main results

* `positiveNormalizer_pos`, `positiveNormalizer_pos_of_nonempty`: a finite sum of strictly
  positive reals over a nonempty index set is strictly positive, so dividing by it is safe.
* `twoTermWeightedAverage_eq_inv_smul_sum`: the normalized two-term average
  `a/(a+b) • u + b/(a+b) • v` equals `(a+b)⁻¹ • (a • u + b • v)`.
-/

namespace MechInterp

open Finset

/-- A sum of strictly positive reals over a nonempty finite type is strictly positive. -/
theorem positiveNormalizer_pos {ι : Type*} [Fintype ι] [Nonempty ι]
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) : 0 < ∑ i, w i :=
  Finset.sum_pos (fun i _ => hw i) Finset.univ_nonempty

/-- A sum of strictly positive reals over a nonempty finset is strictly positive. -/
theorem positiveNormalizer_pos_of_nonempty {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    (w : ι → ℝ) (hw : ∀ i ∈ s, 0 < w i) : 0 < ∑ i ∈ s, w i :=
  Finset.sum_pos hw hs

/-- A two-term weighted average written with divisions equals the weighted sum scaled by the
inverse normalizer: `a/(a+b) • u + b/(a+b) • v = (a+b)⁻¹ • (a • u + b • v)`.
No positivity hypothesis is needed, since both sides use the same (possibly zero) inverse. -/
theorem twoTermWeightedAverage_eq_inv_smul_sum
    {V : Type*} [AddCommGroup V] [Module ℝ V] (a b : ℝ) (u v : V) :
    (a / (a + b)) • u + (b / (a + b)) • v = (a + b)⁻¹ • (a • u + b • v) := by
  rw [smul_add, smul_smul, smul_smul]
  congr 1
  · rw [div_eq_mul_inv, mul_comm]
  · rw [div_eq_mul_inv, mul_comm]

end MechInterp
