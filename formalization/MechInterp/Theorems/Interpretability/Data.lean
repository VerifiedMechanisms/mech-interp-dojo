import MechInterp.Definitions.Interpretability.Data

set_option linter.style.header false

/-!
# Expectations under finite distributions

Linearity, constants, monotonicity, point masses, pushforwards, uniform distributions, and
probability bounds.
-/

namespace MechInterp

namespace FinDist

variable {α β : Type*} {M : Type*} [AddCommGroup M] [Module ℝ M]

theorem expect_def (μ : FinDist α) (g : α → M) :
    μ.expect g = ∑ a ∈ μ.w.support, μ.w a • g a := rfl

theorem sum_weights (μ : FinDist α) : ∑ a ∈ μ.w.support, μ.w a = 1 := μ.sum_one

theorem expect_add (μ : FinDist α) (g g' : α → M) :
    μ.expect (fun a => g a + g' a) = μ.expect g + μ.expect g' := by
  simp only [expect_def, smul_add, Finset.sum_add_distrib]

theorem expect_smul (μ : FinDist α) (c : ℝ) (g : α → M) :
    μ.expect (fun a => c • g a) = c • μ.expect g := by
  simp only [expect_def, Finset.smul_sum, smul_comm c]

theorem expect_neg (μ : FinDist α) (g : α → M) :
    μ.expect (fun a => -g a) = -μ.expect g := by
  simp only [expect_def, smul_neg, Finset.sum_neg_distrib]

theorem expect_sub (μ : FinDist α) (g g' : α → M) :
    μ.expect (fun a => g a - g' a) = μ.expect g - μ.expect g' := by
  simp only [sub_eq_add_neg, expect_add, expect_neg]

@[simp] theorem expect_const (μ : FinDist α) (c : M) : μ.expect (fun _ => c) = c := by
  rw [expect_def, ← Finset.sum_smul, sum_weights, one_smul]

theorem expect_finsetSum {ι : Type*} (s : Finset ι) (μ : FinDist α) (g : ι → α → M) :
    μ.expect (fun a => ∑ i ∈ s, g i a) = ∑ i ∈ s, μ.expect (g i) := by
  simp only [expect_def, Finset.smul_sum]
  exact Finset.sum_comm

theorem expect_map (f : α → β) (μ : FinDist α) (g : β → M) :
    (μ.map f).expect g = μ.expect (g ∘ f) := by
  change (μ.w.mapDomain f).sum (fun b r => r • g b) = μ.w.sum fun a r => r • g (f a)
  exact Finsupp.sum_mapDomain_index (h := fun b r => r • g b) (fun b => zero_smul ℝ (g b))
    (fun b r t => add_smul r t (g b))

@[simp] theorem expect_pure (a : α) (g : α → M) : (pure a).expect g = g a := by
  change (Finsupp.single a (1 : ℝ)).sum (fun b r => r • g b) = g a
  simp

theorem expect_uniform [DecidableEq α] (s : Finset α) (hs : s.Nonempty) (g : α → M) :
    (uniform s hs).expect g = (1 / (s.card : ℝ)) • ∑ a ∈ s, g a := by
  simp only [expect, uniform]
  rw [Finsupp.onFinset_sum _ (fun a => zero_smul ℝ (g a)), Finset.smul_sum]
  exact Finset.sum_congr rfl fun a ha => by rw [if_pos ha]

theorem expect_mono (μ : FinDist α) {g g' : α → ℝ} (h : ∀ a, g a ≤ g' a) :
    μ.expect g ≤ μ.expect g' := by
  simp only [expect_def, smul_eq_mul]
  exact Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (μ.nonneg a)

theorem expect_nonneg (μ : FinDist α) {g : α → ℝ} (h : ∀ a, 0 ≤ g a) : 0 ≤ μ.expect g := by
  simpa using μ.expect_mono (g := fun _ => (0 : ℝ)) h

theorem expect_le_of_le (μ : FinDist α) {g : α → ℝ} {c : ℝ} (h : ∀ a, g a ≤ c) :
    μ.expect g ≤ c := by
  simpa using μ.expect_mono (g' := fun _ => c) h

theorem prob_nonneg (μ : FinDist α) (p : α → Prop) : 0 ≤ μ.prob p := by
  classical
  unfold prob
  exact μ.expect_nonneg fun a => by split_ifs <;> norm_num

theorem prob_le_one (μ : FinDist α) (p : α → Prop) : μ.prob p ≤ 1 := by
  classical
  unfold prob
  exact μ.expect_le_of_le fun a => by split_ifs <;> norm_num

theorem prob_of_forall (μ : FinDist α) {p : α → Prop} (h : ∀ a, p a) : μ.prob p = 1 := by
  classical
  unfold prob
  simp [h]

theorem prob_mono (μ : FinDist α) {p q : α → Prop} (h : ∀ a, p a → q a) :
    μ.prob p ≤ μ.prob q := by
  classical
  unfold prob
  refine μ.expect_mono fun a => ?_
  by_cases hp : p a
  · simp [hp, h a hp]
  · simp only [hp, if_false]; split_ifs <;> norm_num

theorem toPMF_apply (μ : FinDist α) (a : α) : μ.toPMF a = ENNReal.ofReal (μ.w a) := by
  simp [toPMF]

end FinDist

end MechInterp
