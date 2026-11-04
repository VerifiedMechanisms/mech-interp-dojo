/-
Copyright (c) 2026 Malhar A. Patel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Malhar A. Patel
-/
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Finite probability distributions

Interpretability measurements are averages over a dataset of prompts: the mean activation used
in mean ablation, the average effect of a patch, the accuracy of a probe. This file models such
datasets as finitely supported probability distributions with *real* weights.

Mathlib's `PMF` uses weights in `ℝ≥0∞`, which makes expectations of real- or vector-valued
functions awkward. `FinDist` uses weights in `ℝ` instead, and `FinDist.toPMF` converts back.

## Main definitions

* `FinDist α`: a finitely supported weight function `w : α →₀ ℝ` with nonnegative weights that
  sum to one.
* `FinDist.expect μ g`: the expectation `∑ a, μ a • g a` of a function valued in any real vector
  space.
* `FinDist.prob μ p`: the probability of a predicate.
* Constructors: `FinDist.pure a` (point mass), `FinDist.map f μ` (pushforward), and
  `FinDist.uniform s hs` (uniform on a nonempty finite set, the usual model of a dataset).

A dataset of clean/corrupted prompt pairs is a distribution on `α × α`.

## Main results

* Expectation is linear (`expect_add`, `expect_smul`, `expect_sub`, `expect_finsetSum`),
  normalized (`expect_const`), and monotone for real-valued functions (`expect_mono`).
* `expect_map`, `expect_pure`, `expect_uniform`: expectations under the constructors.
* `prob_nonneg`, `prob_le_one`, `prob_mono`: probabilities lie in `[0, 1]` and are monotone.
-/

namespace MechInterp

/-- A finitely supported probability distribution on `α` with real weights. -/
structure FinDist (α : Type*) where
  /-- The weight of each point; only finitely many are nonzero. -/
  w : α →₀ ℝ
  /-- Every weight is nonnegative. -/
  nonneg : ∀ a, 0 ≤ w a
  /-- The weights sum to one. -/
  sum_one : w.sum (fun _ r => r) = 1

namespace FinDist

variable {α β : Type*}

/-! ### Expectations and probabilities -/

/-- The expectation `𝔼_{a ∼ μ}[g a] = ∑ a, μ.w a • g a` of a function valued in any real vector
space `M`. -/
noncomputable def expect {M : Type*} [AddCommGroup M] [Module ℝ M] (μ : FinDist α)
    (g : α → M) : M :=
  μ.w.sum fun a r => r • g a

/-- The probability `Pr_{a ∼ μ}[p a]`, the expectation of the indicator of `p`. -/
noncomputable def prob (μ : FinDist α) (p : α → Prop) : ℝ := by
  classical exact μ.expect fun a => if p a then (1 : ℝ) else 0

/-! ### Constructors -/

/-- The point mass at `a`. -/
noncomputable def pure (a : α) : FinDist α where
  w := Finsupp.single a 1
  nonneg b := by
    classical
    rw [Finsupp.single_apply]; split_ifs <;> norm_num
  sum_one := by simp

/-- The pushforward `f_* μ`, which gives `b` the total weight of the points `a` with `f a = b`. -/
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

/-- The uniform distribution on a nonempty finite set `s`: each point of `s` has weight
`1 / |s|`. -/
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

/-- The same distribution as a Mathlib probability mass function, with weights in `ℝ≥0∞`. -/
noncomputable def toPMF (μ : FinDist α) : PMF α :=
  PMF.ofFinset (fun a => ENNReal.ofReal (μ.w a)) μ.w.support
    (by
      rw [← ENNReal.ofReal_sum_of_nonneg fun a _ => μ.nonneg a]
      have h : ∑ a ∈ μ.w.support, μ.w a = 1 := μ.sum_one
      rw [h, ENNReal.ofReal_one])
    (fun a ha => by rw [Finsupp.notMem_support_iff.mp ha, ENNReal.ofReal_zero])

/-! ### Properties of expectation -/

variable {M : Type*} [AddCommGroup M] [Module ℝ M]

/-- The expectation as a sum over the support of `μ`. -/
theorem expect_def (μ : FinDist α) (g : α → M) :
    μ.expect g = ∑ a ∈ μ.w.support, μ.w a • g a := rfl

/-- The weights sum to one over the support. -/
theorem sum_weights (μ : FinDist α) : ∑ a ∈ μ.w.support, μ.w a = 1 := μ.sum_one

/-- Expectation is additive: `𝔼[g + g'] = 𝔼[g] + 𝔼[g']`. -/
theorem expect_add (μ : FinDist α) (g g' : α → M) :
    μ.expect (fun a => g a + g' a) = μ.expect g + μ.expect g' := by
  simp only [expect_def, smul_add, Finset.sum_add_distrib]

/-- Expectation is homogeneous: `𝔼[c • g] = c • 𝔼[g]`. -/
theorem expect_smul (μ : FinDist α) (c : ℝ) (g : α → M) :
    μ.expect (fun a => c • g a) = c • μ.expect g := by
  simp only [expect_def, Finset.smul_sum, smul_comm c]

/-- `𝔼[-g] = -𝔼[g]`. -/
theorem expect_neg (μ : FinDist α) (g : α → M) :
    μ.expect (fun a => -g a) = -μ.expect g := by
  simp only [expect_def, smul_neg, Finset.sum_neg_distrib]

/-- `𝔼[g - g'] = 𝔼[g] - 𝔼[g']`. -/
theorem expect_sub (μ : FinDist α) (g g' : α → M) :
    μ.expect (fun a => g a - g' a) = μ.expect g - μ.expect g' := by
  simp only [sub_eq_add_neg, expect_add, expect_neg]

/-- The expectation of a constant is that constant, because the weights sum to one. -/
@[simp] theorem expect_const (μ : FinDist α) (c : M) : μ.expect (fun _ => c) = c := by
  rw [expect_def, ← Finset.sum_smul, sum_weights, one_smul]

/-- Expectation commutes with finite sums. -/
theorem expect_finsetSum {ι : Type*} (s : Finset ι) (μ : FinDist α) (g : ι → α → M) :
    μ.expect (fun a => ∑ i ∈ s, g i a) = ∑ i ∈ s, μ.expect (g i) := by
  simp only [expect_def, Finset.smul_sum]
  exact Finset.sum_comm

/-- Expectation under a pushforward: `𝔼_{f_* μ}[g] = 𝔼_μ[g ∘ f]`. -/
theorem expect_map (f : α → β) (μ : FinDist α) (g : β → M) :
    (μ.map f).expect g = μ.expect (g ∘ f) := by
  change (μ.w.mapDomain f).sum (fun b r => r • g b) = μ.w.sum fun a r => r • g (f a)
  exact Finsupp.sum_mapDomain_index (h := fun b r => r • g b) (fun b => zero_smul ℝ (g b))
    (fun b r t => add_smul r t (g b))

/-- The expectation under a point mass is evaluation at the point. -/
@[simp] theorem expect_pure (a : α) (g : α → M) : (pure a).expect g = g a := by
  change (Finsupp.single a (1 : ℝ)).sum (fun b r => r • g b) = g a
  simp

/-- The expectation under the uniform distribution is the average `(1 / |s|) • ∑ a ∈ s, g a`. -/
theorem expect_uniform [DecidableEq α] (s : Finset α) (hs : s.Nonempty) (g : α → M) :
    (uniform s hs).expect g = (1 / (s.card : ℝ)) • ∑ a ∈ s, g a := by
  simp only [expect, uniform]
  rw [Finsupp.onFinset_sum _ (fun a => zero_smul ℝ (g a)), Finset.smul_sum]
  exact Finset.sum_congr rfl fun a ha => by rw [if_pos ha]

/-- Expectation is monotone for real-valued functions. -/
theorem expect_mono (μ : FinDist α) {g g' : α → ℝ} (h : ∀ a, g a ≤ g' a) :
    μ.expect g ≤ μ.expect g' := by
  simp only [expect_def, smul_eq_mul]
  exact Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (μ.nonneg a)

/-- The expectation of a nonnegative function is nonnegative. -/
theorem expect_nonneg (μ : FinDist α) {g : α → ℝ} (h : ∀ a, 0 ≤ g a) : 0 ≤ μ.expect g := by
  simpa using μ.expect_mono (g := fun _ => (0 : ℝ)) h

/-- A function bounded above by `c` has expectation at most `c`. -/
theorem expect_le_of_le (μ : FinDist α) {g : α → ℝ} {c : ℝ} (h : ∀ a, g a ≤ c) :
    μ.expect g ≤ c := by
  simpa using μ.expect_mono (g' := fun _ => c) h

/-! ### Properties of probability -/

/-- Probabilities are nonnegative. -/
theorem prob_nonneg (μ : FinDist α) (p : α → Prop) : 0 ≤ μ.prob p := by
  classical
  unfold prob
  exact μ.expect_nonneg fun a => by split_ifs <;> norm_num

/-- Probabilities are at most one. -/
theorem prob_le_one (μ : FinDist α) (p : α → Prop) : μ.prob p ≤ 1 := by
  classical
  unfold prob
  exact μ.expect_le_of_le fun a => by split_ifs <;> norm_num

/-- An event that always holds has probability one. -/
theorem prob_of_forall (μ : FinDist α) {p : α → Prop} (h : ∀ a, p a) : μ.prob p = 1 := by
  classical
  unfold prob
  simp [h]

/-- Probability is monotone: if `p` implies `q` then `Pr[p] ≤ Pr[q]`. -/
theorem prob_mono (μ : FinDist α) {p q : α → Prop} (h : ∀ a, p a → q a) :
    μ.prob p ≤ μ.prob q := by
  classical
  unfold prob
  refine μ.expect_mono fun a => ?_
  by_cases hp : p a
  · simp [hp, h a hp]
  · simp only [hp, if_false]; split_ifs <;> norm_num

/-- The `PMF` weight of a point is the (nonnegative) real weight, cast to `ℝ≥0∞`. -/
theorem toPMF_apply (μ : FinDist α) (a : α) : μ.toPMF a = ENNReal.ofReal (μ.w a) := by
  simp [toPMF]

end FinDist

end MechInterp
