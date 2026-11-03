import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

set_option linter.style.header false

/-!
# Finite distributions and datasets

`FinDist α` is a finitely supported probability distribution with real weights. Real
weights keep expectations of real- and vector-valued functions free of `ℝ≥0∞`
conversions. `FinDist.toPMF` connects to Mathlib's `PMF`.

Datasets are uniform distributions on finite sets. Clean/corrupt pairs are distributions on
`α × α`.
-/

namespace MechInterp

/-- A finitely supported probability distribution with real weights. -/
structure FinDist (α : Type*) where
  /-- The weights. -/
  w : α →₀ ℝ
  nonneg : ∀ a, 0 ≤ w a
  sum_one : w.sum (fun _ r => r) = 1

namespace FinDist

variable {α β : Type*}

/-- Expectation of a vector-valued function. -/
noncomputable def expect {M : Type*} [AddCommGroup M] [Module ℝ M] (μ : FinDist α)
    (g : α → M) : M :=
  μ.w.sum fun a r => r • g a

/-- Probability of a predicate. -/
noncomputable def prob (μ : FinDist α) (p : α → Prop) : ℝ := by
  classical exact μ.expect fun a => if p a then (1 : ℝ) else 0

/-- The point mass at `a`. -/
noncomputable def pure (a : α) : FinDist α where
  w := Finsupp.single a 1
  nonneg b := by
    classical
    rw [Finsupp.single_apply]; split_ifs <;> norm_num
  sum_one := by simp

/-- Pushforward along `f`. -/
noncomputable def map (f : α → β) (μ : FinDist α) : FinDist β where
  w := μ.w.mapDomain f
  nonneg b := by
    classical
    rw [Finsupp.mapDomain, Finsupp.sum_apply]
    refine Finset.sum_nonneg fun a _ => ?_
    simp only [Finsupp.single_apply]
    split_ifs
    · exact μ.nonneg a
    · exact le_refl 0
  sum_one := by
    rw [Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]
    exact μ.sum_one

/-- The uniform distribution on a nonempty finite set. -/
noncomputable def uniform [DecidableEq α] (s : Finset α) (hs : s.Nonempty) : FinDist α where
  w := Finsupp.onFinset s (fun a => if a ∈ s then 1 / (s.card : ℝ) else 0)
    (fun a ha => by by_contra h; exact ha (if_neg h))
  nonneg a := by
    rw [Finsupp.onFinset_apply]
    split_ifs
    · positivity
    · exact le_refl 0
  sum_one := by
    rw [Finsupp.onFinset_sum _ (fun _ => rfl)]
    rw [Finset.sum_congr rfl fun a ha => if_pos ha, Finset.sum_const, nsmul_eq_mul]
    have : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hs.card_pos.ne'
    field_simp

/-- The underlying Mathlib probability mass function. -/
noncomputable def toPMF (μ : FinDist α) : PMF α :=
  PMF.ofFinset (fun a => ENNReal.ofReal (μ.w a)) μ.w.support
    (by
      rw [← ENNReal.ofReal_sum_of_nonneg fun a _ => μ.nonneg a]
      have h : ∑ a ∈ μ.w.support, μ.w a = 1 := μ.sum_one
      rw [h, ENNReal.ofReal_one])
    (fun a ha => by rw [Finsupp.notMem_support_iff.mp ha, ENNReal.ofReal_zero])

end FinDist

end MechInterp
