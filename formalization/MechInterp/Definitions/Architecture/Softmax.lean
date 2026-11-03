import MechInterp.Definitions.Architecture.Pattern
import MechInterp.Theorems.Math.Normalizers
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Sigmoid

set_option linter.style.header false

/-!
# Softmax, hardmax, and raw weight rules

* Legacy full-type softmax `softmax s i = exp (s i) / ∑ j, exp (s j)`.
* Masked softmax at inverse temperature `β`:
  `A_ij = 1[M i j] exp (β s_ij) / ∑_{j' allowed} exp (β s_ij')`.
  `softmaxRule β hM` packages it as a certified pattern rule; `hM` certifies that every row
  has a positive normalizer.
* Hardmax (averaging hard attention): uniform over the allowed maximizers of each row.
* Raw weight rules for linear and sigmoid attention.
-/

namespace MechInterp

open Finset

/-- The finite softmax denominator `∑ i, exp (s i)`. -/
noncomputable def softmaxDenom {ι : Type*} [Fintype ι] (s : ι → ℝ) : ℝ := ∑ i, Real.exp (s i)

/-- Finite softmax weights over a whole type. -/
noncomputable def softmax {ι : Type*} [Fintype ι] (s : ι → ℝ) : ι → ℝ :=
  fun i => Real.exp (s i) / softmaxDenom s

section Masked

variable {Pdst Psrc : Type*} [Fintype Psrc] (M : Mask Pdst Psrc)

/-- The masked softmax normalizer of row `i` at inverse temperature `β`. -/
noncomputable def maskedDenom (β : ℝ) (s : Pdst → Psrc → ℝ) (i : Pdst) : ℝ :=
  ∑ j ∈ M.allowedSet i, Real.exp (β * s i j)

/-- Masked softmax weights at inverse temperature `β`. -/
noncomputable def maskedSoftmax (β : ℝ) (s : Pdst → Psrc → ℝ) (i : Pdst) (j : Psrc) : ℝ :=
  if M.allowed i j then Real.exp (β * s i j) / maskedDenom M β s i else 0

/-- The allowed maximizers of row `i`. -/
noncomputable def argSet (s : Pdst → Psrc → ℝ) (i : Pdst) : Finset Psrc :=
  univ.filter fun j => M.allowed i j ∧ ∀ j', M.allowed i j' → s i j' ≤ s i j

/-- Hardmax weights: uniform over the allowed maximizers of each row. -/
noncomputable def hardmax [DecidableEq Psrc] (s : Pdst → Psrc → ℝ) (i : Pdst) (j : Psrc) : ℝ :=
  if j ∈ argSet M s i then 1 / ((argSet M s i).card : ℝ) else 0

variable {M}

/-- The masked softmax pattern rule at inverse temperature `β`. -/
noncomputable def softmaxRule (β : ℝ) (hM : M.WellFormed) : PatternRule Pdst Psrc M where
  toPattern s :=
    { A := maskedSoftmax M β s
      nonneg := fun i j => by
        unfold maskedSoftmax
        split_ifs
        · exact div_nonneg (Real.exp_pos _).le
            (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)
        · exact le_refl 0
      row_sum := fun i => by
        have hne : (M.allowedSet i).Nonempty := by
          obtain ⟨j, hj⟩ := hM i
          exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
        have hpos : 0 < maskedDenom M β s i :=
          positiveNormalizer_pos_of_nonempty hne _ fun _ _ => Real.exp_pos _
        unfold maskedSoftmax
        rw [← Finset.sum_filter, ← Finset.sum_div]
        exact div_self hpos.ne' }
  supported s i j h := by
    change maskedSoftmax M β s i j = 0
    simp [maskedSoftmax, h]

/-- The hardmax pattern rule. -/
noncomputable def hardmaxRule [DecidableEq Psrc] (hM : M.WellFormed) : PatternRule Pdst Psrc M where
  toPattern s :=
    { A := hardmax M s
      nonneg := fun i j => by
        unfold hardmax
        split_ifs
        · exact div_nonneg zero_le_one (Nat.cast_nonneg _)
        · exact le_refl 0
      row_sum := fun i => by
        have hne : (argSet M s i).Nonempty := by
          obtain ⟨j₀, hj₀⟩ := hM i
          have hrow : (M.allowedSet i).Nonempty :=
            ⟨j₀, Finset.mem_filter.mpr ⟨Finset.mem_univ j₀, hj₀⟩⟩
          obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (M.allowedSet i) (s i) hrow
          refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j,
            (Finset.mem_filter.mp hj).2, fun j' hj' => hmax j' ?_⟩⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ j', hj'⟩
        unfold hardmax
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
          Finset.sum_const, nsmul_eq_mul]
        have : ((argSet M s i).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hne.card_pos.ne'
        field_simp }
  supported s i j h := by
    change hardmax M s i j = 0
    have : j ∉ argSet M s i := fun hj => h (Finset.mem_filter.mp hj).2.1
    simp [hardmax, this]

variable (M)

/-- Linear attention: the masked raw scores are the weights. -/
def linearWeights : WeightRule Pdst Psrc where
  toWeights s i j := if M.allowed i j then s i j else 0

/-- Sigmoid attention at inverse temperature `β`. -/
noncomputable def sigmoidWeights (β : ℝ) : WeightRule Pdst Psrc where
  toWeights s i j := if M.allowed i j then Real.sigmoid (β * s i j) else 0

end Masked

end MechInterp
