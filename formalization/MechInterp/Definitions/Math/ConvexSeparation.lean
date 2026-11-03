import Mathlib.Analysis.InnerProductSpace.Basic

set_option linter.style.header false

/-!
# Linear-threshold separability

A pair of sets is linear-threshold separable when some affine functional `⟪w, ·⟫ - τ` is
strictly positive on the first set and nonpositive on the second. Zero scores are therefore
classified as negative, matching the classifier convention `f x = true ↔ S x > 0`.
-/

namespace MechInterp

open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `Spos` and `Sneg` are separated by a linear threshold: positive points score strictly
above `τ` and negative points score at most `τ`. -/
def LinThresholdSeparable (Spos Sneg : Set V) : Prop :=
  ∃ (w : V) (τ : ℝ), (∀ s ∈ Spos, τ < ⟪w, s⟫_ℝ) ∧ (∀ s ∈ Sneg, ⟪w, s⟫_ℝ ≤ τ)

end MechInterp
